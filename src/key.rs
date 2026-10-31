//! The key types, and the [`CobblestoneKey`] trait.

use std::fmt;

use subtle::{Choice, ConstantTimeEq};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// The size of a Cobblestone-128 key, in bytes.
pub const KEY_SIZE: usize = 16;

/// The size of a Cobblestone-256 key, in bytes.
#[cfg(feature = "cobblestone-256")]
#[cfg_attr(docsrs, doc(cfg(feature = "cobblestone-256")))]
pub const KEY256_SIZE: usize = 32;

/// The error returned when a key is created from a slice of the wrong size.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidKeySize {
    len: usize,
    expected: usize,
}

impl fmt::Display for InvalidKeySize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid key size: {} bytes, expected {}",
            self.len, self.expected
        )
    }
}

impl std::error::Error for InvalidKeySize {}

/// A Cobblestone-128 key.
///
/// A single key can be used to encrypt a practically unlimited number of
/// messages. It must be kept secret, and must be uniformly random: generate it
/// with [`Key::generate`], or derive it with a KDF. It must not be, for
/// example, a password.
///
/// The key is zeroized when dropped, compares in constant time, and is
/// redacted from its [`Debug`] output.
///
/// # Examples
///
/// ```
/// use cobblestone::Key;
///
/// let key = Key::generate();
///
/// // Store the key, and load it back.
/// let bytes: [u8; 16] = *key.as_bytes();
/// let loaded = Key::from_bytes(&bytes);
/// assert_eq!(loaded, key);
///
/// // Keys of the wrong size are rejected.
/// assert!(Key::try_from(&[0u8; 32][..]).is_err());
/// ```
#[derive(Clone)]
pub struct Key([u8; KEY_SIZE]);

/// A Cobblestone-256 key.
///
/// Cobblestone-256 uses AES-256-GCM instead of AES-128-GCM. The spec
/// describes it as a compliance-oriented instantiation, and recommends
/// Cobblestone-128 ([`Key`]) absent other requirements. Use it only if a
/// policy requires 256-bit keys, or to interoperate with messages encrypted
/// with it. It is only available with the `cobblestone-256` feature.
///
/// Every API accepts either key type, and the key type selects the
/// instantiation. Ciphertexts don't record which one was used, so a message
/// can only be decrypted with the same type of key it was encrypted with.
///
/// Like [`Key`], it must be kept secret and uniformly random. It is zeroized
/// when dropped, compares in constant time, and is redacted from its
/// [`Debug`] output.
///
/// # Examples
///
/// ```
/// use cobblestone::{Key256, decrypt, encrypt};
///
/// let key = Key256::generate();
/// let ciphertext = encrypt(&key, b"file.txt", b"hello world")?;
/// assert_eq!(decrypt(&key, b"file.txt", &ciphertext)?, b"hello world");
///
/// // Keys of the wrong size are rejected.
/// assert!(Key256::try_from(&[0u8; 16][..]).is_err());
/// # Ok::<(), cobblestone::Error>(())
/// ```
#[cfg(feature = "cobblestone-256")]
#[cfg_attr(docsrs, doc(cfg(feature = "cobblestone-256")))]
#[derive(Clone)]
pub struct Key256([u8; KEY256_SIZE]);

/// Implements the shared methods and traits of a key type.
macro_rules! key_impls {
    ($name:ident, $size:ident) => {
        impl $name {
            /// Generates a new random key with the operating system's random
            /// number generator.
            ///
            /// # Panics
            ///
            /// Panics if the operating system's random number generator fails,
            /// which doesn't happen on supported platforms.
            #[must_use]
            pub fn generate() -> $name {
                let mut key = $name([0; $size]);
                crate::fill_random(&mut key.0);
                key
            }

            /// Creates a key from its bytes.
            #[must_use]
            pub fn from_bytes(bytes: &[u8; $size]) -> $name {
                $name(*bytes)
            }

            /// Returns the bytes of the key.
            #[must_use]
            pub fn as_bytes(&self) -> &[u8; $size] {
                &self.0
            }
        }

        impl From<[u8; $size]> for $name {
            fn from(bytes: [u8; $size]) -> $name {
                $name(bytes)
            }
        }

        impl TryFrom<&[u8]> for $name {
            type Error = InvalidKeySize;

            /// Creates a key from a slice of bytes.
            ///
            /// # Errors
            ///
            #[doc = concat!("Returns [`InvalidKeySize`] if the slice is not [`", stringify!($size), "`] bytes")]
            /// long.
            fn try_from(bytes: &[u8]) -> Result<$name, InvalidKeySize> {
                let key = bytes.try_into().map_err(|_| InvalidKeySize {
                    len: bytes.len(),
                    expected: $size,
                })?;
                Ok($name(key))
            }
        }

        impl ConstantTimeEq for $name {
            fn ct_eq(&self, other: &$name) -> Choice {
                self.0.ct_eq(&other.0)
            }
        }

        impl PartialEq for $name {
            fn eq(&self, other: &$name) -> bool {
                self.ct_eq(other).into()
            }
        }

        impl Eq for $name {}

        impl fmt::Debug for $name {
            fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
                f.write_str(concat!(stringify!($name), "(..)"))
            }
        }

        impl Drop for $name {
            fn drop(&mut self) {
                self.0.zeroize();
            }
        }

        impl ZeroizeOnDrop for $name {}
    };
}

key_impls!(Key, KEY_SIZE);
#[cfg(feature = "cobblestone-256")]
key_impls!(Key256, KEY256_SIZE);

/// A key for either instantiation: [`Key`] for Cobblestone-128, or `Key256`
/// for Cobblestone-256, with the `cobblestone-256` feature.
///
/// Every API takes `&impl CobblestoneKey`, and the type of the key selects the
/// instantiation. Without the feature, [`Key`] is the only implementation.
/// This trait is sealed: it can't be implemented outside this crate.
pub trait CobblestoneKey: sealed::Sealed {}

impl CobblestoneKey for Key {}
#[cfg(feature = "cobblestone-256")]
impl CobblestoneKey for Key256 {}

pub(crate) mod sealed {
    use super::Key;
    #[cfg(feature = "cobblestone-256")]
    use super::Key256;

    /// A borrowed key of either instantiation, for the internals. Borrowing
    /// avoids leaving copies of the key in memory, which can't be zeroized.
    #[derive(Clone, Copy)]
    pub enum VariantRef<'a> {
        Cobblestone128(&'a Key),
        #[cfg(feature = "cobblestone-256")]
        Cobblestone256(&'a Key256),
    }

    impl VariantRef<'_> {
        /// Copies the key, for a decryptor that must keep it until the header
        /// is read.
        pub(crate) fn into_owned(self) -> Variant {
            match self {
                VariantRef::Cobblestone128(k) => Variant::Cobblestone128(k.clone()),
                #[cfg(feature = "cobblestone-256")]
                VariantRef::Cobblestone256(k) => Variant::Cobblestone256(k.clone()),
            }
        }
    }

    /// An owned key of either instantiation.
    pub enum Variant {
        Cobblestone128(Key),
        #[cfg(feature = "cobblestone-256")]
        Cobblestone256(Key256),
    }

    impl Variant {
        pub(crate) fn as_ref(&self) -> VariantRef<'_> {
            match self {
                Variant::Cobblestone128(k) => VariantRef::Cobblestone128(k),
                #[cfg(feature = "cobblestone-256")]
                Variant::Cobblestone256(k) => VariantRef::Cobblestone256(k),
            }
        }
    }

    pub trait Sealed {
        fn variant(&self) -> VariantRef<'_>;
    }

    impl Sealed for Key {
        fn variant(&self) -> VariantRef<'_> {
            VariantRef::Cobblestone128(self)
        }
    }

    #[cfg(feature = "cobblestone-256")]
    impl Sealed for Key256 {
        fn variant(&self) -> VariantRef<'_> {
            VariantRef::Cobblestone256(self)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate() {
        assert_ne!(Key::generate(), Key::generate());
        #[cfg(feature = "cobblestone-256")]
        assert_ne!(Key256::generate(), Key256::generate());
    }

    #[test]
    fn conversions() {
        let bytes = [7; KEY_SIZE];
        assert_eq!(Key::from(bytes), Key::from_bytes(&bytes));
        assert_eq!(Key::try_from(&bytes[..]), Ok(Key::from(bytes)));
        let err = Key::try_from(&[0; 15][..]).unwrap_err();
        assert_eq!(
            err,
            InvalidKeySize {
                len: 15,
                expected: 16
            }
        );
        assert_eq!(err.to_string(), "invalid key size: 15 bytes, expected 16");
        assert_ne!(Key::from([1; KEY_SIZE]), Key::from(bytes));
    }

    #[cfg(feature = "cobblestone-256")]
    #[test]
    fn conversions_256() {
        let bytes = [7; KEY256_SIZE];
        assert_eq!(Key256::from(bytes), Key256::from_bytes(&bytes));
        assert_eq!(Key256::try_from(&bytes[..]), Ok(Key256::from(bytes)));
        // A Cobblestone-128 key is not a valid Cobblestone-256 key.
        let err = Key256::try_from(&[0; KEY_SIZE][..]).unwrap_err();
        assert_eq!(err.to_string(), "invalid key size: 16 bytes, expected 32");
        assert!(Key::try_from(&bytes[..]).is_err());
        assert_ne!(Key256::from([1; KEY256_SIZE]), Key256::from(bytes));
    }

    #[test]
    fn debug_is_redacted() {
        assert_eq!(format!("{:?}", Key::from([0xab; KEY_SIZE])), "Key(..)");
        #[cfg(feature = "cobblestone-256")]
        assert_eq!(
            format!("{:?}", Key256::from([0xab; KEY256_SIZE])),
            "Key256(..)"
        );
    }
}
