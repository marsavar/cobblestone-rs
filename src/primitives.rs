//! The primitives behind the traits of the chunk layer and the header: AES-GCM,
//! HMAC-SHA-512, and constant-time comparison.

#[cfg(feature = "cobblestone-256")]
use aes_gcm::Aes256Gcm;
use aes_gcm::aead::{
    AeadCore, AeadInOut, Nonce, Tag, TagPosition,
    consts::{U12, U16},
    inout::InOutBuf,
};
use aes_gcm::{Aes128Gcm, KeyInit};
use hmac::{Hmac, Mac as _};
use sha2::Sha512;
use subtle::ConstantTimeEq;

use crate::header::{AeadInit, COMMITMENT_SIZE, CtEq, HASH_SIZE, Mac, Suite};
use crate::raw::{ChunkAead, NONCE_SIZE, TAG_SIZE};

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

impl<A> ChunkAead for A
where
    A: AeadInOut + AeadCore<NonceSize = U12, TagSize = U16>,
{
    fn seal(&self, nonce: &[u8; NONCE_SIZE], buf: &mut [u8]) -> [u8; TAG_SIZE] {
        self.encrypt_inout_detached(&Nonce::<A>::from(*nonce), &[], buf.into())
            .expect("chunk is within AES-GCM limits")
            .into()
    }

    fn open(&self, nonce: &[u8; NONCE_SIZE], buf: &mut [u8], tag: &[u8; TAG_SIZE]) -> bool {
        self.decrypt_inout_detached(
            &Nonce::<A>::from(*nonce),
            &[],
            buf.into(),
            &Tag::<A>::from(*tag),
        )
        .is_ok()
    }
}

impl AeadInit for AesGcm {
    fn new(suite: Suite, key: &[u8]) -> Self {
        match suite {
            Suite::Aes128 => {
                AesGcm::Aes128(Aes128Gcm::new_from_slice(key).expect("key size is correct"))
            }
            #[cfg(feature = "cobblestone-256")]
            Suite::Aes256 => {
                AesGcm::Aes256(Aes256Gcm::new_from_slice(key).expect("key size is correct"))
            }
        }
    }
}

pub(crate) struct HmacSha512(Hmac<Sha512>);

impl Mac for HmacSha512 {
    fn new(key: &[u8]) -> Self {
        HmacSha512(Hmac::new_from_slice(key).expect("HMAC accepts any key size"))
    }

    fn update(&mut self, data: &[u8]) {
        self.0.update(data);
    }

    fn finalize(self) -> [u8; HASH_SIZE] {
        self.0.finalize().into_bytes().into()
    }
}

pub(crate) struct Subtle;

impl CtEq for Subtle {
    fn ct_eq(a: &[u8; COMMITMENT_SIZE], b: &[u8; COMMITMENT_SIZE]) -> bool {
        a.ct_eq(b).into()
    }
}
