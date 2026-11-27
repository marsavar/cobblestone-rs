//! The message header: HKDF-Expand, the derivation of the AEAD key, base nonce
//! and commitment, and the commitment check.
//!
//! The primitives are behind small traits, and the salt and scratch buffers are
//! passed in, so that Charon can extract this module for the Lean proofs.

use crate::Error;
use crate::raw::{ChunkAead, ChunkCipher, Encryptor, NONCE_SIZE};

pub(crate) const SALT_SIZE: usize = 24;
pub(crate) const COMMITMENT_SIZE: usize = 32;
pub(crate) const HEADER_SIZE: usize = SALT_SIZE + COMMITMENT_SIZE;
/// The largest input key, which is also the largest AEAD key.
pub(crate) const MAX_KEY_SIZE: usize = 32;
/// The output size of HMAC-SHA-512.
pub(crate) const HASH_SIZE: usize = 64;
/// The size of the HKDF output buffer: the largest AEAD key, the base nonce and
/// the commitment.
pub(crate) const OKM_SIZE: usize = MAX_KEY_SIZE + NONCE_SIZE + COMMITMENT_SIZE;

/// The instantiation, which selects the AEAD and the HKDF info label.
#[derive(Clone, Copy)]
pub(crate) enum Suite {
    Aes128,
    #[cfg(feature = "cobblestone-256")]
    Aes256,
}

/// HMAC-SHA-512, as an incremental MAC.
pub(crate) trait Mac: Sized {
    fn new(key: &[u8]) -> Self;
    fn update(&mut self, data: &[u8]);
    fn finalize(self) -> [u8; HASH_SIZE];
}

/// Creates the AEAD of an instantiation from its key.
pub(crate) trait AeadInit: ChunkAead + Sized {
    fn new(suite: Suite, key: &[u8]) -> Self;
}

/// Constant-time equality of commitments.
pub(crate) trait CtEq {
    fn ct_eq(a: &[u8; COMMITMENT_SIZE], b: &[u8; COMMITMENT_SIZE]) -> bool;
}

/// One HKDF-Expand block: HMAC(prk, prev || info || counter), with the info
/// `label || salt || context`. The info parts are separate parameters rather
/// than a slice of slices, which Aeneas can't translate.
fn hkdf_block<M: Mac>(
    prk: &[u8],
    prev: &[u8],
    label: &[u8],
    salt: &[u8],
    context: &[u8],
    counter: u8,
) -> [u8; HASH_SIZE] {
    let mut mac = M::new(prk);
    mac.update(prev);
    mac.update(label);
    mac.update(salt);
    mac.update(context);
    mac.update(&[counter]);
    mac.finalize()
}

/// HKDF-Expand (RFC 5869) with the MAC and the info `label || salt || context`,
/// filling `out`. `t` is scratch space for the previous block.
///
/// The hkdf crate is not used because it rejects PRKs shorter than the hash
/// output, and Cobblestone uses the input key directly as the PRK.
pub(crate) fn hkdf_expand<M: Mac>(
    prk: &[u8],
    label: &[u8],
    salt: &[u8],
    context: &[u8],
    out: &mut [u8],
    t: &mut [u8; HASH_SIZE],
) {
    // T(i) = HMAC(prk, T(i-1) || info || i), with T(0) empty. Cobblestone-128
    // needs one block, and Cobblestone-256 two.
    assert!(out.len() <= 255 * HASH_SIZE);
    let mut start = 0;
    while start < out.len() {
        // The block index is start / HASH_SIZE, at most 254. T(0) is empty, and
        // every later T(i) fills `t`. No branches in the body, which keeps the
        // Lean proof of this loop manageable.
        let prev_len = start.min(HASH_SIZE);
        let counter = (start / HASH_SIZE + 1) as u8;
        *t = hkdf_block::<M>(prk, &t[..prev_len], label, salt, context, counter);
        let len = (out.len() - start).min(HASH_SIZE);
        out[start..start + len].copy_from_slice(&t[..len]);
        start += len;
    }
}

/// Derives the AEAD key, base nonce, and commitment for a message. `okm` and `t`
/// are scratch space, which the caller wipes.
pub(crate) fn derive<M: Mac, A: AeadInit>(
    suite: Suite,
    key: &[u8],
    salt: &[u8; SALT_SIZE],
    context: &[u8],
    okm: &mut [u8; OKM_SIZE],
    t: &mut [u8; HASH_SIZE],
) -> (ChunkCipher<A>, [u8; COMMITMENT_SIZE]) {
    // key || base nonce || commitment = HKDF-Expand(prk = input key,
    //     info = "c2sp.org/chunked-encryption@v1+" || aead || 0x00 || salt || context)
    let info_prefix: &[u8] = match suite {
        Suite::Aes128 => b"c2sp.org/chunked-encryption@v1+AEAD_AES_128_GCM\x00",
        #[cfg(feature = "cobblestone-256")]
        Suite::Aes256 => b"c2sp.org/chunked-encryption@v1+AEAD_AES_256_GCM\x00",
    };
    // The AEAD key is the same size as the input key.
    let key_size = key.len();
    let out = &mut okm[..key_size + NONCE_SIZE + COMMITMENT_SIZE];
    hkdf_expand::<M>(key, info_prefix, salt, context, out, t);

    let (aead_key, rest) = out.split_at(key_size);
    let (nonce, commitment) = rest.split_at(NONCE_SIZE);
    let cipher = ChunkCipher::new(A::new(suite, aead_key), nonce.try_into().unwrap());
    (cipher, commitment.try_into().unwrap())
}

/// Returns the header and the encryptor for a new message with the given salt.
pub(crate) fn new_header<M: Mac, A: AeadInit>(
    suite: Suite,
    key: &[u8],
    salt: &[u8; SALT_SIZE],
    context: &[u8],
    okm: &mut [u8; OKM_SIZE],
    t: &mut [u8; HASH_SIZE],
) -> ([u8; HEADER_SIZE], Encryptor<A>) {
    let (cipher, commitment) = derive::<M, A>(suite, key, salt, context, okm, t);
    // Not named `header`, which would shadow the module's namespace in Lean.
    let mut bytes = [0; HEADER_SIZE];
    bytes[..SALT_SIZE].copy_from_slice(salt);
    bytes[SALT_SIZE..].copy_from_slice(&commitment);
    (bytes, Encryptor::new(cipher))
}

/// Checks the commitment in a header and returns the cipher for the message.
pub(crate) fn open_header<M: Mac, A: AeadInit, C: CtEq>(
    suite: Suite,
    key: &[u8],
    context: &[u8],
    bytes: &[u8; HEADER_SIZE],
    okm: &mut [u8; OKM_SIZE],
    t: &mut [u8; HASH_SIZE],
) -> Result<ChunkCipher<A>, Error> {
    let (salt, commitment) = bytes.split_at(SALT_SIZE);
    let (cipher, expected) = derive::<M, A>(suite, key, salt.try_into().unwrap(), context, okm, t);
    if !C::ct_eq(commitment.try_into().unwrap(), &expected) {
        return Err(Error::InvalidCommitment);
    }
    Ok(cipher)
}
