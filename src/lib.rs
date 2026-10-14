//! Cobblestone-128, the chunked (or streaming) encryption scheme specified at
//! [c2sp.org/chunked-encryption](https://c2sp.org/chunked-encryption).
//!
//! Cobblestone-128 is based on AES-128-GCM and HKDF-SHA-512, and is designed to
//! encrypt large messages of up to 4 PiB, allowing authenticated streaming
//! encryption and decryption, and authenticated random access. The message is
//! broken up into 16 KiB chunks, each of which is encrypted and authenticated
//! separately, with protections against reordering and truncation attacks.
//!
//! It is interoperable with [filippo.io/cobblestone] (Go),
//! [pyca/cryptography] (Python) and [cobblestone.ts] (TypeScript).
//!
//! The scheme has a fixed overhead of 56 bytes and a marginal overhead of
//! approximately 0.1%.
//!
//! # APIs
//!
//! - [`Key`] is a Cobblestone-128 key.
//! - [`encrypt`] and [`decrypt`] work on in-memory messages.
//! - [`EncryptWriter`] and [`EncryptReader`] encrypt a stream, and
//!   [`DecryptReader`] decrypts one, never releasing unauthenticated
//!   plaintext.
//! - [`RandomAccessDecryptor`] decrypts any range of a seekable ciphertext.
//! - With the `tokio` feature, the `cobblestone::tokio` module provides
//!   async versions of the streaming APIs.
//!
//! ```
//! let key = cobblestone::Key::generate();
//! let ciphertext = cobblestone::encrypt(&key, b"file.txt", b"hello world")?;
//! let plaintext = cobblestone::decrypt(&key, b"file.txt", &ciphertext)?;
//! assert_eq!(plaintext, b"hello world");
//! # Ok::<(), cobblestone::Error>(())
//! ```
//!
//! [filippo.io/cobblestone]: https://github.com/FiloSottile/cobblestone
//! [pyca/cryptography]: https://cryptography.io/en/latest/cobblestone/
//! [cobblestone.ts]: https://github.com/FiloSottile/cobblestone.ts

#![forbid(unsafe_code)]
#![cfg_attr(docsrs, feature(doc_cfg))]

use std::fmt;
use std::io;

use aes_gcm::{Aes128Gcm, KeyInit};
use hmac::{Hmac, Mac};
use sha2::Sha512;
use subtle::ConstantTimeEq;
use zeroize::Zeroizing;

mod io_impl;
mod key;
mod raw;
mod stream;
#[cfg(test)]
mod test_vectors;

// Runs the examples in the README as doctests. One of them uses tokio.
#[cfg(all(doctest, feature = "tokio"))]
#[doc = include_str!("../README.md")]
struct ReadmeDoctests;
#[cfg(feature = "tokio")]
#[cfg_attr(docsrs, doc(cfg(feature = "tokio")))]
pub mod tokio;

pub use io_impl::{DecryptReader, EncryptReader, EncryptWriter, RandomAccessDecryptor};
pub use key::{KEY_SIZE, Key};

use raw::{CHUNK_SIZE, ChunkCipher, Decryptor, ENC_CHUNK_SIZE, Encryptor};

const SALT_SIZE: usize = 24;
const COMMITMENT_SIZE: usize = 32;
const NONCE_SIZE: usize = 12;
const HEADER_SIZE: usize = SALT_SIZE + COMMITMENT_SIZE;

/// An error encountered while encrypting or decrypting.
///
/// When returned through an [`io::Error`] by the streaming APIs, it can be
/// recovered with [`io::Error::downcast`](https://doc.rust-lang.org/std/io/struct.Error.html#method.downcast).
#[derive(Debug, Clone, PartialEq, Eq)]
#[non_exhaustive]
pub enum Error {
    /// A key was created from a slice that is not [`KEY_SIZE`] bytes long.
    InvalidKeySize(usize),
    /// The ciphertext was not produced with this key and context, or its
    /// header was modified.
    InvalidCommitment,
    /// The ciphertext ended early, for example in the middle of the header or
    /// of a chunk, or without a final short chunk.
    Truncated,
    /// The ciphertext size is not valid for any message.
    InvalidSize,
    /// A chunk failed to authenticate. The ciphertext was modified, truncated,
    /// reordered, or has trailing data.
    DecryptionFailed {
        /// The index of the chunk that failed to authenticate.
        chunk: u64,
    },
    /// The message exceeds the maximum size of 4 PiB - 1 byte.
    MessageTooLarge,
}

impl fmt::Display for Error {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Error::InvalidKeySize(n) => {
                write!(f, "invalid key size: {n} bytes, expected {KEY_SIZE}")
            }
            Error::InvalidCommitment => f.write_str("invalid commitment"),
            Error::Truncated => f.write_str("ciphertext is truncated"),
            Error::InvalidSize => f.write_str("invalid ciphertext size"),
            Error::DecryptionFailed { chunk } => {
                write!(f, "failed to decrypt and authenticate chunk {chunk}")
            }
            Error::MessageTooLarge => f.write_str("message exceeds the maximum size"),
        }
    }
}

impl std::error::Error for Error {}

impl From<Error> for io::Error {
    fn from(err: Error) -> io::Error {
        let kind = match err {
            Error::Truncated => io::ErrorKind::UnexpectedEof,
            Error::InvalidKeySize(_) => io::ErrorKind::InvalidInput,
            Error::MessageTooLarge => io::ErrorKind::Other,
            _ => io::ErrorKind::InvalidData,
        };
        io::Error::new(kind, err)
    }
}

/// Returns the size of the ciphertext of a plaintext of the given size, or
/// `None` if it exceeds the maximum message size (4 PiB - 1 byte).
///
/// # Examples
///
/// ```
/// // 56 bytes of header, plus a 16-byte tag for each chunk.
/// assert_eq!(cobblestone::ciphertext_size(0), Some(56 + 16));
/// assert_eq!(cobblestone::ciphertext_size(16 * 1024), Some(56 + 16 * 1024 + 2 * 16));
/// assert_eq!(cobblestone::ciphertext_size(1 << 52), None);
/// ```
pub fn ciphertext_size(plaintext_size: u64) -> Option<u64> {
    raw::ciphertext_size(plaintext_size).map(|n| n + HEADER_SIZE as u64)
}

/// Returns the size of the plaintext of a ciphertext of the given size.
///
/// Only one ciphertext size is valid for each plaintext size, so this returns
/// an error for sizes no message encrypts to.
///
/// # Errors
///
/// - [`Error::Truncated`] if the size is shorter than the 56-byte header.
/// - [`Error::InvalidSize`] if no message encrypts to this size, for example
///   because the final chunk is missing or shorter than its tag.
/// - [`Error::MessageTooLarge`] if the size exceeds that of the largest
///   message.
///
/// # Examples
///
/// ```
/// use cobblestone::{Error, plaintext_size};
///
/// assert_eq!(plaintext_size(56 + 16 + 100), Ok(100));
/// // A full chunk must be followed by a final short chunk.
/// assert_eq!(plaintext_size(56 + 16 * 1024 + 16), Err(Error::InvalidSize));
/// assert_eq!(plaintext_size(10), Err(Error::Truncated));
/// ```
pub fn plaintext_size(ciphertext_size: u64) -> Result<u64, Error> {
    let body = ciphertext_size
        .checked_sub(HEADER_SIZE as u64)
        .ok_or(Error::Truncated)?;
    raw::plaintext_size(body)
}

/// Encrypts a message.
///
/// The context is non-secret data bound to the ciphertext: decryption only
/// succeeds with the same context. Use it to tie a ciphertext to where it
/// belongs, for example a filename or a user ID. It is not encrypted and not
/// stored in the ciphertext. It may be empty (`b""`) when there is nothing to
/// bind.
///
/// A random salt is generated for each message, so encrypting the same message
/// twice produces different ciphertexts.
///
/// # Errors
///
/// Returns [`Error::MessageTooLarge`] if the plaintext exceeds 4 PiB - 1
/// byte, or the ciphertext doesn't fit in memory.
///
/// # Panics
///
/// Panics if the operating system's random number generator fails, which
/// doesn't happen on supported platforms.
///
/// # Examples
///
/// ```
/// let key = cobblestone::Key::generate();
/// let ciphertext = cobblestone::encrypt(&key, b"user 42", b"hello world")?;
/// assert_eq!(ciphertext.len() as u64, cobblestone::ciphertext_size(11).unwrap());
/// # Ok::<(), cobblestone::Error>(())
/// ```
pub fn encrypt(key: &Key, context: &[u8], plaintext: &[u8]) -> Result<Vec<u8>, Error> {
    let (header, mut enc) = new_header(key, context);
    let size = ciphertext_size(plaintext.len() as u64).ok_or(Error::MessageTooLarge)?;
    let mut out = Vec::with_capacity(size.try_into().map_err(|_| Error::MessageTooLarge)?);
    out.extend_from_slice(&header);
    let (chunks, rest) = plaintext.as_chunks::<CHUNK_SIZE>();
    for chunk in chunks {
        seal_into(&mut enc, &mut out, chunk, false)?;
    }
    seal_into(&mut enc, &mut out, rest, true)?;
    debug_assert_eq!(out.len() as u64, size);
    Ok(out)
}

fn seal_into(
    enc: &mut Encryptor<Aes128Gcm>,
    out: &mut Vec<u8>,
    chunk: &[u8],
    last: bool,
) -> Result<(), Error> {
    let start = out.len();
    out.extend_from_slice(chunk);
    let tag = enc.seal(&mut out[start..], last)?;
    out.extend_from_slice(&tag);
    Ok(())
}

/// Decrypts a message encrypted with the same key and context.
///
/// The whole ciphertext is authenticated before the plaintext is returned.
///
/// # Errors
///
/// - [`Error::InvalidCommitment`] if the ciphertext was not encrypted with
///   this key and context, or its header was modified.
/// - [`Error::Truncated`] if the ciphertext is shorter than the header, or
///   ends at a chunk boundary without a final short chunk.
/// - [`Error::DecryptionFailed`] if a chunk fails to authenticate, because
///   the ciphertext was modified, truncated, reordered, or has trailing data.
///
/// # Examples
///
/// ```
/// use cobblestone::{Error, Key, decrypt, encrypt};
///
/// let key = Key::generate();
/// let ciphertext = encrypt(&key, b"user 42", b"hello world")?;
/// assert_eq!(decrypt(&key, b"user 42", &ciphertext)?, b"hello world");
/// assert_eq!(decrypt(&key, b"user 43", &ciphertext), Err(Error::InvalidCommitment));
/// # Ok::<(), Error>(())
/// ```
pub fn decrypt(key: &Key, context: &[u8], ciphertext: &[u8]) -> Result<Vec<u8>, Error> {
    let header = ciphertext
        .get(..HEADER_SIZE)
        .ok_or(Error::Truncated)?
        .try_into()
        .unwrap();
    let mut dec = Decryptor::new(open_header(key, context, header)?);
    let mut body = &ciphertext[HEADER_SIZE..];
    let size = raw::plaintext_size(body.len() as u64).unwrap_or(0);
    let mut out = Vec::with_capacity(size as usize);
    let mut chunk = vec![0; ENC_CHUNK_SIZE];
    while !dec.is_done() {
        let n = body.len().min(ENC_CHUNK_SIZE);
        chunk[..n].copy_from_slice(&body[..n]);
        body = &body[n..];
        let len = dec.open(&mut chunk[..n])?;
        out.extend_from_slice(&chunk[..len]);
    }
    Ok(out)
}

const INFO_PREFIX: &[u8] = b"c2sp.org/chunked-encryption@v1+AEAD_AES_128_GCM\x00";

/// Derives the AEAD key, base nonce, and commitment for a message.
fn derive(
    key: &Key,
    salt: &[u8; SALT_SIZE],
    context: &[u8],
) -> (ChunkCipher<Aes128Gcm>, [u8; COMMITMENT_SIZE]) {
    // key || base nonce || commitment = HKDF-Expand(prk = input key,
    //     info = "c2sp.org/chunked-encryption@v1+" || aead || 0x00 || salt || context)
    //
    // The output fits in a single SHA-512 block, so HKDF-Expand is just
    // T(1) = HMAC(prk, info || 0x01). (The hkdf crate is not used because it
    // rejects PRKs shorter than the hash output.)
    const _: () = assert!(KEY_SIZE + NONCE_SIZE + COMMITMENT_SIZE <= 64);
    let mut mac =
        Hmac::<Sha512>::new_from_slice(key.as_bytes()).expect("HMAC accepts any key size");
    mac.update(INFO_PREFIX);
    mac.update(salt);
    mac.update(context);
    mac.update(&[1]);
    let out = Zeroizing::new(<[u8; 64]>::from(mac.finalize().into_bytes()));

    let (aead_key, rest) = out.split_at(KEY_SIZE);
    let (nonce, rest) = rest.split_at(NONCE_SIZE);
    let commitment = rest[..COMMITMENT_SIZE].try_into().unwrap();
    let aead = Aes128Gcm::new_from_slice(aead_key).expect("key size is correct");
    let cipher = ChunkCipher::new(aead, nonce.try_into().unwrap());
    (cipher, commitment)
}

/// Generates a salt and returns the header and the encryptor for a new message.
fn new_header(key: &Key, context: &[u8]) -> ([u8; HEADER_SIZE], Encryptor<Aes128Gcm>) {
    let mut salt = [0; SALT_SIZE];
    fill_random(&mut salt);
    let (cipher, commitment) = derive(key, &salt, context);
    let mut header = [0; HEADER_SIZE];
    header[..SALT_SIZE].copy_from_slice(&salt);
    header[SALT_SIZE..].copy_from_slice(&commitment);
    (header, Encryptor::new(cipher))
}

/// Fills `buf` with random bytes from the operating system.
///
/// A failing system random number generator is treated as fatal, like the Go
/// and TypeScript implementations do: there is no safe way to continue, and
/// it doesn't happen on supported platforms.
fn fill_random(buf: &mut [u8]) {
    getrandom::fill(buf).expect("the operating system's random number generator failed");
}

/// Checks the commitment in a header and returns the cipher for the message.
fn open_header(
    key: &Key,
    context: &[u8],
    header: &[u8; HEADER_SIZE],
) -> Result<ChunkCipher<Aes128Gcm>, Error> {
    let (salt, commitment) = header.split_at(SALT_SIZE);
    let (cipher, expected) = derive(key, salt.try_into().unwrap(), context);
    if !bool::from(commitment.ct_eq(&expected)) {
        return Err(Error::InvalidCommitment);
    }
    Ok(cipher)
}

#[cfg(test)]
mod tests {
    use super::*;
    use raw::TAG_SIZE;

    #[test]
    fn round_trip_sizes() {
        let key = Key::generate();
        for len in [
            0,
            1,
            CHUNK_SIZE - 1,
            CHUNK_SIZE,
            CHUNK_SIZE + 1,
            3 * CHUNK_SIZE,
        ] {
            let msg: Vec<u8> = (0..len).map(|i| i as u8).collect();
            let ct = encrypt(&key, b"ctx", &msg).unwrap();
            assert_eq!(Some(ct.len() as u64), ciphertext_size(len as u64));
            assert_eq!(plaintext_size(ct.len() as u64), Ok(len as u64));
            assert_eq!(decrypt(&key, b"ctx", &ct).unwrap(), msg);
            assert_eq!(decrypt(&key, b"", &ct), Err(Error::InvalidCommitment));
        }
    }

    #[test]
    fn truncation() {
        let key = Key::generate();
        let ct = encrypt(&key, b"", &[7; CHUNK_SIZE]).unwrap();
        assert_eq!(
            decrypt(&key, b"", &ct[..HEADER_SIZE - 1]),
            Err(Error::Truncated)
        );
        assert_eq!(
            decrypt(&key, b"", &ct[..HEADER_SIZE]),
            Err(Error::Truncated)
        );
        assert_eq!(
            decrypt(&key, b"", &ct[..HEADER_SIZE + ENC_CHUNK_SIZE]),
            Err(Error::Truncated)
        );
        assert_eq!(
            decrypt(&key, b"", &ct[..ct.len() - 1]),
            Err(Error::DecryptionFailed { chunk: 1 })
        );
        assert_eq!(
            decrypt(&key, b"", &ct[..HEADER_SIZE + TAG_SIZE - 1]),
            Err(Error::DecryptionFailed { chunk: 0 })
        );
    }
}
