//! Raw mode of c2sp.org/chunked-encryption: the chunking layer, with the AEAD
//! key and base nonce supplied by the caller.
//!
//! This is not exposed publicly (the spec says libraries SHOULD NOT expose it to
//! applications), but it's kept separate so that it can be tested against the
//! raw mode test vectors, and so that it could become a hazmat API later.

use aes_gcm::Aes128Gcm;
#[cfg(feature = "cobblestone-256")]
use aes_gcm::Aes256Gcm;
use aes_gcm::aead::{
    AeadCore, AeadInOut, Nonce, Tag, TagPosition,
    consts::{U12, U16},
    inout::InOutBuf,
};

use crate::Error;

/// The size of a plaintext chunk. Every chunk is this size except the final one,
/// which is always shorter (and may be empty).
pub(crate) const CHUNK_SIZE: usize = 16 * 1024;
/// The size of the AEAD authentication tag appended to each chunk.
pub(crate) const TAG_SIZE: usize = 16;
/// The size of an encrypted full chunk.
pub(crate) const ENC_CHUNK_SIZE: usize = CHUNK_SIZE + TAG_SIZE;
/// The maximum number of chunks in a message, including the final one.
pub(crate) const MAX_CHUNKS: u64 = 1 << 38;
/// The width of the chunk counter XOR'd into the end of the base nonce.
const COUNTER_SIZE: usize = 5;

/// Returns the number of encrypted chunks in a raw ciphertext of the given size,
/// or an error if no message encrypts to that size.
pub(crate) fn encrypted_chunk_count(encrypted_size: u64) -> Result<u64, Error> {
    let enc_chunk = ENC_CHUNK_SIZE as u64;
    // There's always a final chunk of at least TAG_SIZE bytes, so the size is
    // valid iff its remainder modulo a full encrypted chunk is at least that.
    let chunks = encrypted_size / enc_chunk + 1;
    if encrypted_size % enc_chunk < TAG_SIZE as u64 {
        return Err(Error::InvalidSize);
    }
    if chunks > MAX_CHUNKS {
        return Err(Error::MessageTooLarge);
    }
    Ok(chunks)
}

/// Returns the plaintext size of a raw ciphertext of the given size.
pub(crate) fn plaintext_size(encrypted_size: u64) -> Result<u64, Error> {
    let chunks = encrypted_chunk_count(encrypted_size)?;
    Ok(encrypted_size - chunks * TAG_SIZE as u64)
}

/// Returns the raw ciphertext size of a plaintext of the given size, or `None`
/// if it exceeds the maximum message size.
pub(crate) fn ciphertext_size(plaintext_size: u64) -> Option<u64> {
    let chunks = plaintext_size / CHUNK_SIZE as u64 + 1;
    if chunks > MAX_CHUNKS {
        return None;
    }
    Some(plaintext_size + chunks * TAG_SIZE as u64)
}

/// The AEAD of either instantiation, so that the streaming types don't need a
/// type parameter for it.
// The size difference is small next to the 16 KiB chunk buffer every stream
// holds, so boxing the larger variant isn't worth the indirection.
#[allow(clippy::large_enum_variant)]
pub(crate) enum AesGcm {
    Aes128(Aes128Gcm),
    #[cfg(feature = "cobblestone-256")]
    Aes256(Aes256Gcm),
}

impl AeadCore for AesGcm {
    type NonceSize = U12;
    type TagSize = U16;
    const TAG_POSITION: TagPosition = TagPosition::Postfix;
}

impl AeadInOut for AesGcm {
    fn encrypt_inout_detached(
        &self,
        nonce: &Nonce<Self>,
        associated_data: &[u8],
        buffer: InOutBuf<'_, '_, u8>,
    ) -> aes_gcm::aead::Result<Tag<Self>> {
        match self {
            AesGcm::Aes128(a) => a.encrypt_inout_detached(nonce, associated_data, buffer),
            #[cfg(feature = "cobblestone-256")]
            AesGcm::Aes256(a) => a.encrypt_inout_detached(nonce, associated_data, buffer),
        }
    }

    fn decrypt_inout_detached(
        &self,
        nonce: &Nonce<Self>,
        associated_data: &[u8],
        buffer: InOutBuf<'_, '_, u8>,
        tag: &Tag<Self>,
    ) -> aes_gcm::aead::Result<()> {
        match self {
            AesGcm::Aes128(a) => a.decrypt_inout_detached(nonce, associated_data, buffer, tag),
            #[cfg(feature = "cobblestone-256")]
            AesGcm::Aes256(a) => a.decrypt_inout_detached(nonce, associated_data, buffer, tag),
        }
    }
}

/// An AEAD and base nonce, which can encrypt and decrypt chunks at any index.
pub(crate) struct ChunkCipher<A> {
    aead: A,
    base_nonce: [u8; 12],
}

impl<A> ChunkCipher<A>
where
    A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
{
    pub(crate) fn new(aead: A, base_nonce: &[u8; 12]) -> Self {
        ChunkCipher {
            aead,
            base_nonce: *base_nonce,
        }
    }

    /// The base nonce XOR'd with the chunk index as a big-endian integer.
    fn nonce(&self, index: u64) -> Nonce<A> {
        assert!(index < MAX_CHUNKS, "chunk index out of range");
        let mut nonce = Nonce::<A>::from(self.base_nonce);
        let counter = index.to_be_bytes();
        let n = nonce.len();
        for (b, c) in nonce[n - COUNTER_SIZE..]
            .iter_mut()
            .zip(&counter[8 - COUNTER_SIZE..])
        {
            *b ^= c;
        }
        nonce
    }

    /// Encrypts `chunk` in place and returns the tag to append to it.
    pub(crate) fn seal(&self, index: u64, chunk: &mut [u8]) -> [u8; TAG_SIZE] {
        debug_assert!(chunk.len() <= CHUNK_SIZE);
        let tag = self
            .aead
            .encrypt_inout_detached(&self.nonce(index), &[], chunk.into())
            .expect("chunk is within AES-GCM limits");
        tag.into()
    }

    /// Decrypts an encrypted chunk (including its trailing tag) in place,
    /// returning the plaintext length.
    pub(crate) fn open(&self, index: u64, chunk: &mut [u8]) -> Result<usize, Error> {
        debug_assert!(chunk.len() <= ENC_CHUNK_SIZE);
        let Some(len) = chunk.len().checked_sub(TAG_SIZE) else {
            return Err(Error::DecryptionFailed { chunk: index });
        };
        let (data, tag) = chunk.split_at_mut(len);
        let tag = Tag::<A>::try_from(&*tag).expect("tag length is fixed");
        self.aead
            .decrypt_inout_detached(&self.nonce(index), &[], data.into(), &tag)
            .map_err(|_| Error::DecryptionFailed { chunk: index })?;
        Ok(len)
    }
}

/// Sequential encryption state: assigns chunk indexes and enforces the chunk
/// count limit.
pub(crate) struct Encryptor<A> {
    cipher: ChunkCipher<A>,
    next: u64,
    finished: bool,
}

impl<A> Encryptor<A>
where
    A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
{
    pub(crate) fn new(cipher: ChunkCipher<A>) -> Self {
        Encryptor {
            cipher,
            next: 0,
            finished: false,
        }
    }

    /// Encrypts the next chunk in place and returns its tag. A full chunk must
    /// be exactly [`CHUNK_SIZE`] bytes, and the final chunk must be shorter.
    pub(crate) fn seal(&mut self, chunk: &mut [u8], last: bool) -> Result<[u8; TAG_SIZE], Error> {
        assert!(!self.finished, "chunk sealed after the final chunk");
        if last {
            assert!(chunk.len() < CHUNK_SIZE, "final chunk must be short");
        } else {
            assert!(chunk.len() == CHUNK_SIZE, "non-final chunk must be full");
            // A full chunk must be followed by a final chunk, which must also
            // fit in the counter space.
            if self.next >= MAX_CHUNKS - 1 {
                return Err(Error::MessageTooLarge);
            }
        }
        let tag = self.cipher.seal(self.next, chunk);
        self.next += 1;
        self.finished = last;
        Ok(tag)
    }
}

/// Sequential decryption state: assigns chunk indexes, detects the final chunk
/// from its length, and makes errors sticky.
pub(crate) struct Decryptor<A> {
    cipher: ChunkCipher<A>,
    next: u64,
    done: bool,
    failed: Option<Error>,
}

impl<A> Decryptor<A>
where
    A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
{
    pub(crate) fn new(cipher: ChunkCipher<A>) -> Self {
        Decryptor {
            cipher,
            next: 0,
            done: false,
            failed: None,
        }
    }

    /// Returns true once the final chunk has been successfully decrypted.
    pub(crate) fn is_done(&self) -> bool {
        self.done
    }

    /// Returns the error that previously caused decryption to fail, if any.
    pub(crate) fn failed(&self) -> Option<&Error> {
        self.failed.as_ref()
    }

    /// Decrypts the next encrypted chunk in place, returning the plaintext
    /// length.
    ///
    /// The caller must pass either exactly [`ENC_CHUNK_SIZE`] bytes, or all
    /// remaining bytes up to the end of the ciphertext. Anything shorter is
    /// treated as the final chunk. A final chunk shorter than a tag, including
    /// an empty one, means the ciphertext was truncated: the spec requires a
    /// truncation error for it.
    pub(crate) fn open(&mut self, chunk: &mut [u8]) -> Result<usize, Error> {
        if let Some(err) = &self.failed {
            return Err(err.clone());
        }
        assert!(!self.done, "chunk opened after the final chunk");
        let result = self.open_inner(chunk);
        if let Err(err) = &result {
            self.failed = Some(err.clone());
        }
        result
    }

    fn open_inner(&mut self, chunk: &mut [u8]) -> Result<usize, Error> {
        let last = chunk.len() < ENC_CHUNK_SIZE;
        if chunk.len() < TAG_SIZE {
            return Err(Error::Truncated);
        }
        if !last && self.next >= MAX_CHUNKS - 1 {
            return Err(Error::MessageTooLarge);
        }
        let len = self.cipher.open(self.next, chunk)?;
        self.next += 1;
        self.done = last;
        Ok(len)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use aes_gcm::{Aes256Gcm, KeyInit};

    #[test]
    fn sizes() {
        let enc = ENC_CHUNK_SIZE as u64;
        let tag = TAG_SIZE as u64;
        assert_eq!(ciphertext_size(0), Some(tag));
        assert_eq!(ciphertext_size(CHUNK_SIZE as u64), Some(enc + tag));
        assert_eq!(plaintext_size(tag), Ok(0));
        assert_eq!(plaintext_size(enc + tag), Ok(CHUNK_SIZE as u64));
        for invalid in [0, tag - 1, enc, enc + tag - 1, 2 * enc] {
            assert_eq!(
                plaintext_size(invalid),
                Err(Error::InvalidSize),
                "{invalid}"
            );
        }
        let max = (1u64 << 52) - 1;
        let max_ct = ciphertext_size(max).unwrap();
        assert_eq!(plaintext_size(max_ct), Ok(max));
        assert_eq!(ciphertext_size(max + 1), None);
        assert_eq!(plaintext_size(max_ct + enc), Err(Error::MessageTooLarge));
        assert!(plaintext_size(u64::MAX).is_err());
    }

    #[test]
    fn nonce_counter() {
        let cipher = ChunkCipher::new(Aes128Gcm::new(&[0; 16].into()), &[0xff; 12]);
        let n = cipher.nonce(0x12_3456_789a);
        assert_eq!(n[..7], [0xff; 7]);
        assert_eq!(
            n[7..],
            [
                0xff ^ 0x12,
                0xff ^ 0x34,
                0xff ^ 0x56,
                0xff ^ 0x78,
                0xff ^ 0x9a
            ]
        );
        assert_eq!(cipher.nonce(MAX_CHUNKS - 1)[7], 0xff ^ 0x3f);
    }

    #[test]
    fn chunk_count_limit() {
        let cipher = || ChunkCipher::new(Aes128Gcm::new(&[0; 16].into()), &[0; 12]);

        // The last allowed index can only hold the final chunk.
        let mut enc = Encryptor::new(cipher());
        enc.next = MAX_CHUNKS - 2;
        let mut full = vec![0; CHUNK_SIZE];
        let tag = enc.seal(&mut full, false).unwrap();
        assert_eq!(
            enc.seal(&mut [0; CHUNK_SIZE], false),
            Err(Error::MessageTooLarge)
        );
        let mut last = vec![1, 2, 3];
        let last_tag = enc.seal(&mut last, true).unwrap();

        let mut dec = Decryptor::new(cipher());
        dec.next = MAX_CHUNKS - 2;
        let mut chunk = [full, tag.to_vec()].concat();
        assert_eq!(dec.open(&mut chunk), Ok(CHUNK_SIZE));
        let mut chunk = [last, last_tag.to_vec()].concat();
        assert_eq!(dec.open(&mut chunk), Ok(3));
        assert!(dec.is_done());

        let mut dec = Decryptor::new(cipher());
        dec.next = MAX_CHUNKS - 1;
        assert_eq!(
            dec.open(&mut [0; ENC_CHUNK_SIZE]),
            Err(Error::MessageTooLarge)
        );
    }

    #[test]
    fn short_chunks_fail_without_panicking() {
        let cipher = ChunkCipher::new(Aes128Gcm::new(&[0; 16].into()), &[0; 12]);
        for len in [0, 1, TAG_SIZE - 1] {
            let mut chunk = vec![0; len];
            assert!(cipher.open(0, &mut chunk).is_err());
        }
    }

    use crate::test_vectors as vectors;

    /// Decrypts a raw ciphertext sequentially, returning the plaintext
    /// produced before any error.
    fn decrypt_raw<A>(cipher: ChunkCipher<A>, mut body: &[u8]) -> (Vec<u8>, Result<(), Error>)
    where
        A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
    {
        let mut dec = Decryptor::new(cipher);
        let mut out = Vec::new();
        while !dec.is_done() {
            let n = body.len().min(ENC_CHUNK_SIZE);
            let mut chunk = body[..n].to_vec();
            body = &body[n..];
            match dec.open(&mut chunk) {
                Ok(len) => out.extend_from_slice(&chunk[..len]),
                Err(err) => {
                    // Errors are sticky.
                    assert_eq!(dec.open(&mut [0; TAG_SIZE]), Err(err.clone()));
                    return (out, Err(err));
                }
            }
        }
        (out, Ok(()))
    }

    fn encrypt_raw<A>(cipher: ChunkCipher<A>, msg: &[u8]) -> Vec<u8>
    where
        A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
    {
        let mut enc = Encryptor::new(cipher);
        let mut out = Vec::new();
        let full = msg.len() / CHUNK_SIZE * CHUNK_SIZE;
        let chunks = msg[..full].chunks(CHUNK_SIZE).map(|c| (c, false));
        for (chunk, last) in chunks.chain([(&msg[full..], true)]) {
            let mut buf = chunk.to_vec();
            let tag = enc.seal(&mut buf, last).unwrap();
            out.extend_from_slice(&buf);
            out.extend_from_slice(&tag);
        }
        out
    }

    /// Authenticates the message length by decrypting the final chunk, like
    /// a random access implementation does.
    fn final_chunk_valid<A>(cipher: &ChunkCipher<A>, body: &[u8]) -> bool
    where
        A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
    {
        let Ok(chunks) = encrypted_chunk_count(body.len() as u64) else {
            return false;
        };
        let off = ((chunks - 1) * ENC_CHUNK_SIZE as u64) as usize;
        cipher.open(chunks - 1, &mut body[off..].to_vec()).is_ok()
    }

    fn check_vector<A>(v: &vectors::Vector, new_cipher: impl Fn() -> ChunkCipher<A>)
    where
        A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
    {
        let body = &v.ct[crate::HEADER_SIZE..];
        let (msg, result) = decrypt_raw(new_cipher(), body);
        if v.valid {
            result.unwrap();
            v.check_message(&msg);
            assert_eq!(plaintext_size(body.len() as u64), Ok(msg.len() as u64));
            assert_eq!(
                encrypt_raw(new_cipher(), &msg),
                body,
                "{}: re-encryption",
                v.name
            );
            assert!(final_chunk_valid(&new_cipher(), body), "{}", v.name);
        } else {
            assert!(result.is_err(), "{}: decryption succeeded", v.name);
            v.check_prefix(&msg);
            assert_eq!(msg.len(), v.prefix_length(), "{}: prefix", v.name);
            assert_eq!(
                final_chunk_valid(&new_cipher(), body),
                v.has("ValidFinalChunk"),
                "{}: final chunk",
                v.name
            );
        }
    }

    #[test]
    fn wycheproof_raw_mode() {
        let mut count = 0;
        for v in vectors::load() {
            // Raw mode applies to vectors that provide the derived AEAD key
            // and base nonce, for both instantiations.
            let (Some(key), Some(nonce)) = (&v.aead_key, &v.base_nonce) else {
                assert!(v.has("HeaderFailure"), "{}", v.name);
                continue;
            };
            assert!(!v.has("HeaderFailure"), "{}", v.name);
            count += 1;
            match v.aead.as_str() {
                "AEAD_AES_128_GCM" => check_vector(&v, || {
                    ChunkCipher::new(Aes128Gcm::new_from_slice(key).unwrap(), nonce)
                }),
                "AEAD_AES_256_GCM" => check_vector(&v, || {
                    ChunkCipher::new(Aes256Gcm::new_from_slice(key).unwrap(), nonce)
                }),
                aead => panic!("unknown AEAD {aead}"),
            }
        }
        assert!(count > 0);
    }
}
