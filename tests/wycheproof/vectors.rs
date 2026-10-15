//! Loading of the Wycheproof c2sp.org/chunked-encryption test vectors, as
//! described in https://github.com/C2SP/wycheproof/blob/main/doc/c2sp_chunked_encryption.md
//!
//! The files are vendored unmodified; see tests/testdata/README.md for the
//! upstream commit and license. The raw mode unit tests use a reduced copy in
//! src/test_vectors.rs.

use std::collections::HashSet;
use std::io::Read;

use serde::Deserialize;
use sha2::{Digest, Sha512};

pub const FILES: [&str; 2] = [
    "c2sp_chunked_encryption_aes_128_gcm_test.json",
    "c2sp_chunked_encryption_aes_256_gcm_test.json",
];

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct File {
    algorithm: String,
    number_of_tests: usize,
    test_groups: Vec<Group>,
}

#[derive(Deserialize)]
struct Group {
    #[serde(rename = "type")]
    kind: String,
    aead: String,
    sha: String,
    tests: Vec<RawVector>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct RawVector {
    tc_id: u64,
    comment: String,
    key: String,
    ctx: String,
    ct: String,
    msg_length: Option<usize>,
    msg_sha512: Option<String>,
    result: String,
    flags: Vec<String>,
}

pub struct Vector {
    pub name: String,
    /// The AEAD of the instantiation, like "AEAD_AES_128_GCM".
    pub aead: String,
    pub key: Vec<u8>,
    pub ctx: Vec<u8>,
    /// The inflated ciphertext.
    pub ct: Vec<u8>,
    pub msg_length: Option<usize>,
    pub msg_sha512: Option<String>,
    pub valid: bool,
    pub flags: HashSet<String>,
}

impl Vector {
    pub fn is_cobblestone_128(&self) -> bool {
        self.aead == "AEAD_AES_128_GCM"
    }

    /// The input key, which must be valid.
    pub fn input_key(&self) -> cobblestone::Key {
        cobblestone::Key::try_from(&self.key[..]).unwrap()
    }

    pub fn has(&self, flag: &str) -> bool {
        self.flags.contains(flag)
    }

    /// For valid vectors, the message length. For invalid ones, the length of
    /// the longest valid message prefix, which may be empty.
    pub fn prefix_length(&self) -> usize {
        self.msg_length.unwrap_or(0)
    }

    /// Checks that `msg` is the expected message of a valid vector.
    pub fn check_message(&self, msg: &[u8]) {
        assert_eq!(
            Some(msg.len()),
            self.msg_length,
            "{}: message length",
            self.name
        );
        assert_eq!(
            Some(hex::encode(Sha512::digest(msg))),
            self.msg_sha512,
            "{}: message hash",
            self.name
        );
    }

    /// Checks that `data`, produced before a decryption error, is no more
    /// than the valid prefix of the message.
    pub fn check_prefix(&self, data: &[u8]) {
        assert!(
            data.len() <= self.prefix_length(),
            "{}: produced {} bytes, more than the valid prefix of {}",
            self.name,
            data.len(),
            self.prefix_length()
        );
        if data.len() == self.prefix_length()
            && let Some(hash) = &self.msg_sha512
        {
            assert_eq!(
                &hex::encode(Sha512::digest(data)),
                hash,
                "{}: prefix hash",
                self.name
            );
        }
    }
}

pub fn load() -> Vec<Vector> {
    let dir = concat!(env!("CARGO_MANIFEST_DIR"), "/tests/testdata");
    let mut vectors = Vec::new();
    for name in FILES {
        let data = std::fs::read(format!("{dir}/{name}")).unwrap();
        let file: File = serde_json::from_slice(&data).unwrap();
        let mut count = 0;
        for group in file.test_groups {
            assert_eq!(group.kind, "ChunkedEncryption");
            // The hash is always SHA-512, and the instantiation is selected
            // by the AEAD.
            assert_eq!(group.sha, "SHA-512");
            for v in group.tests {
                count += 1;
                let mut ct = Vec::new();
                flate2::read::ZlibDecoder::new(&hex::decode(&v.ct).unwrap()[..])
                    .read_to_end(&mut ct)
                    .unwrap();
                assert!(v.result == "valid" || v.result == "invalid");
                vectors.push(Vector {
                    name: format!("{}/tc{}: {}", file.algorithm, v.tc_id, v.comment),
                    aead: group.aead.clone(),
                    key: hex::decode(&v.key).unwrap(),
                    ctx: hex::decode(&v.ctx).unwrap(),
                    ct,
                    msg_length: v.msg_length,
                    msg_sha512: v.msg_sha512,
                    valid: v.result == "valid",
                    flags: v.flags.into_iter().collect(),
                });
            }
        }
        assert_eq!(count, file.number_of_tests, "{name}: vector count");
    }
    vectors
}
