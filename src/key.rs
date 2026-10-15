//! The [`Key`] type.

use std::fmt;

use subtle::{Choice, ConstantTimeEq};
use zeroize::{Zeroize, ZeroizeOnDrop};

/// The size of a Cobblestone-128 key, in bytes.
pub const KEY_SIZE: usize = 16;

/// The error returned when a [`Key`] is created from a slice that is not
/// [`KEY_SIZE`] bytes long.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct InvalidKeySize {
    len: usize,
}

impl fmt::Display for InvalidKeySize {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            f,
            "invalid key size: {} bytes, expected {KEY_SIZE}",
            self.len
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

impl Key {
    /// Generates a new random key with the operating system's random number
    /// generator.
    ///
    /// # Panics
    ///
    /// Panics if the operating system's random number generator fails, which
    /// doesn't happen on supported platforms.
    #[must_use]
    pub fn generate() -> Key {
        let mut key = Key([0; KEY_SIZE]);
        crate::fill_random(&mut key.0);
        key
    }

    /// Creates a key from its bytes.
    #[must_use]
    pub fn from_bytes(bytes: &[u8; KEY_SIZE]) -> Key {
        Key(*bytes)
    }

    /// Returns the bytes of the key.
    #[must_use]
    pub fn as_bytes(&self) -> &[u8; KEY_SIZE] {
        &self.0
    }
}

impl From<[u8; KEY_SIZE]> for Key {
    fn from(bytes: [u8; KEY_SIZE]) -> Key {
        Key(bytes)
    }
}

impl TryFrom<&[u8]> for Key {
    type Error = InvalidKeySize;

    /// Creates a key from a slice of bytes.
    ///
    /// # Errors
    ///
    /// Returns [`InvalidKeySize`] if the slice is not [`KEY_SIZE`] bytes
    /// long.
    fn try_from(bytes: &[u8]) -> Result<Key, InvalidKeySize> {
        let bytes = bytes
            .try_into()
            .map_err(|_| InvalidKeySize { len: bytes.len() })?;
        Ok(Key(bytes))
    }
}

impl ConstantTimeEq for Key {
    fn ct_eq(&self, other: &Key) -> Choice {
        self.0.ct_eq(&other.0)
    }
}

impl PartialEq for Key {
    fn eq(&self, other: &Key) -> bool {
        self.ct_eq(other).into()
    }
}

impl Eq for Key {}

impl fmt::Debug for Key {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str("Key(..)")
    }
}

impl Drop for Key {
    fn drop(&mut self) {
        self.0.zeroize();
    }
}

impl ZeroizeOnDrop for Key {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn generate() {
        assert_ne!(Key::generate(), Key::generate());
    }

    #[test]
    fn conversions() {
        let bytes = [7; KEY_SIZE];
        assert_eq!(Key::from(bytes), Key::from_bytes(&bytes));
        assert_eq!(Key::try_from(&bytes[..]), Ok(Key::from(bytes)));
        let err = Key::try_from(&[0; 15][..]).unwrap_err();
        assert_eq!(err, InvalidKeySize { len: 15 });
        assert_eq!(err.to_string(), "invalid key size: 15 bytes, expected 16");
        assert_ne!(Key::from([1; KEY_SIZE]), Key::from(bytes));
    }

    #[test]
    fn debug_is_redacted() {
        assert_eq!(format!("{:?}", Key::from([0xab; KEY_SIZE])), "Key(..)");
    }
}
