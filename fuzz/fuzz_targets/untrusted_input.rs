//! Arbitrary bytes given to a decryptor must never make it panic, and every
//! way to decrypt must agree on whether they are a valid ciphertext.
//!
//! The fuzzer can't forge a commitment, so its own inputs are all rejected
//! at the header or by the size checks. To reach the chunk decryption, seed
//! the corpus with ciphertexts for the key and context below.

#![no_main]

use std::io::{Cursor, Read};

use cobblestone::{
    CobblestoneKey, DecryptReader, Key, Key256, RandomAccessDecryptor, ciphertext_size, decrypt,
    plaintext_size,
};
use libfuzzer_sys::fuzz_target;

const CONTEXT: &[u8] = b"fuzz";

fuzz_target!(|data: &[u8]| {
    run(&Key::from([0x42; 16]), data);
    run(&Key256::from([0x42; 32]), data);

    // The size functions are each other's inverse, for any size.
    if let Some(bytes) = data.first_chunk() {
        let n = u64::from_le_bytes(*bytes);
        if let Some(size) = ciphertext_size(n) {
            assert_eq!(plaintext_size(size), Ok(n));
        }
        if let Ok(size) = plaintext_size(n) {
            assert_eq!(ciphertext_size(size), Some(n));
        }
    }
});

fn run(key: &impl CobblestoneKey, data: &[u8]) {
    let one_shot = decrypt(key, CONTEXT, data);

    let mut streamed = Vec::new();
    let result = DecryptReader::new(key, CONTEXT, data).read_to_end(&mut streamed);
    assert_eq!(result.is_ok(), one_shot.is_ok());

    let random_access = RandomAccessDecryptor::new(key, CONTEXT, Cursor::new(data));
    match one_shot {
        Ok(msg) => {
            assert_eq!(streamed, msg);
            assert_eq!(plaintext_size(data.len() as u64), Ok(msg.len() as u64));
            let mut r = random_access.unwrap();
            let mut out = Vec::new();
            r.read_to_end(&mut out).unwrap();
            assert_eq!(out, msg);
        }
        // Nothing is released before the header is checked. Random access
        // may still open a ciphertext whose final chunk is valid.
        Err(_) if data.len() < 56 => {
            assert!(streamed.is_empty());
            assert!(random_access.is_err());
        }
        Err(_) => {}
    }
}
