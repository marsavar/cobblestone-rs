//! Loading of the Wycheproof test vectors for the raw mode unit tests.
//!
//! This is a reduced version of the loader in tests/wycheproof/vectors.rs,
//! which the integration tests use. Unit tests can't share code with integration tests,
//! and the raw layer is private, so it can only be tested from here.

use std::collections::HashSet;
use std::io::Read;

use serde_json::Value;
use sha2::{Digest, Sha512};

pub(crate) struct Vector {
    pub(crate) name: String,
    /// The AEAD of the instantiation, like "AEAD_AES_128_GCM".
    pub(crate) aead: String,
    /// The inflated ciphertext.
    pub(crate) ct: Vec<u8>,
    pub(crate) aead_key: Option<Vec<u8>>,
    pub(crate) base_nonce: Option<[u8; 12]>,
    msg_length: Option<usize>,
    msg_sha512: Option<String>,
    pub(crate) valid: bool,
    flags: HashSet<String>,
}

impl Vector {
    pub(crate) fn has(&self, flag: &str) -> bool {
        self.flags.contains(flag)
    }

    /// For valid vectors, the message length. For invalid ones, the length of
    /// the longest valid message prefix, which may be empty.
    pub(crate) fn prefix_length(&self) -> usize {
        self.msg_length.unwrap_or(0)
    }

    /// Checks that `msg` is the expected message of a valid vector.
    pub(crate) fn check_message(&self, msg: &[u8]) {
        assert_eq!(
            Some(msg.len()),
            self.msg_length,
            "{}: message length",
            self.name
        );
        let hash = hex::encode(Sha512::digest(msg));
        assert_eq!(Some(hash), self.msg_sha512, "{}: message hash", self.name);
    }

    /// Checks that `data`, produced before a decryption error, is no more
    /// than the valid prefix of the message.
    pub(crate) fn check_prefix(&self, data: &[u8]) {
        assert!(
            data.len() <= self.prefix_length(),
            "{}: past the valid prefix",
            self.name
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

pub(crate) fn load() -> Vec<Vector> {
    let hex_field = |v: &Value, key: &str| v[key].as_str().map(|s| hex::decode(s).unwrap());
    let mut vectors = Vec::new();
    for name in [
        "c2sp_chunked_encryption_aes_128_gcm_test.json",
        "c2sp_chunked_encryption_aes_256_gcm_test.json",
    ] {
        let path = format!("{}/tests/testdata/{name}", env!("CARGO_MANIFEST_DIR"));
        let file: Value = serde_json::from_slice(&std::fs::read(path).unwrap()).unwrap();
        let mut count = 0;
        for group in file["testGroups"].as_array().unwrap() {
            assert_eq!(group["sha"], "SHA-512");
            for v in group["tests"].as_array().unwrap() {
                count += 1;
                let mut ct = Vec::new();
                flate2::read::ZlibDecoder::new(&hex_field(v, "ct").unwrap()[..])
                    .read_to_end(&mut ct)
                    .unwrap();
                vectors.push(Vector {
                    name: format!(
                        "{}/tc{}: {}",
                        file["algorithm"].as_str().unwrap(),
                        v["tcId"],
                        v["comment"].as_str().unwrap()
                    ),
                    aead: group["aead"].as_str().unwrap().to_string(),
                    ct,
                    aead_key: hex_field(v, "aeadKey"),
                    base_nonce: hex_field(v, "baseNonce").map(|n| n.try_into().unwrap()),
                    msg_length: v["msgLength"].as_u64().map(|n| n as usize),
                    msg_sha512: v["msgSha512"].as_str().map(String::from),
                    valid: v["result"] == "valid",
                    flags: v["flags"]
                        .as_array()
                        .unwrap()
                        .iter()
                        .map(|f| f.as_str().unwrap().to_string())
                        .collect(),
                });
            }
        }
        assert_eq!(
            Some(count),
            file["numberOfTests"].as_u64(),
            "{name}: vector count"
        );
    }
    vectors
}
