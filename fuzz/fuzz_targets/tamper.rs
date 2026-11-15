//! A ciphertext that was modified in any way must be rejected by every way
//! to decrypt, and a decryptor may only release a prefix of the message
//! before it fails. The wrong key or context must fail the commitment check.

#![no_main]

use std::io::{Cursor, Read};

use arbitrary::Arbitrary;
use cobblestone::{
    CobblestoneKey, DecryptReader, Error, Key, Key256, RandomAccessDecryptor, decrypt, encrypt,
};
use cobblestone_fuzz::{
    AnyKey, ENC_CHUNK_SIZE, HEADER_SIZE, Len, Pacing, Source, message, read_all,
};
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
struct Input {
    key: AnyKey,
    context: Vec<u8>,
    other_context: Vec<u8>,
    len: Len,
    seed: u8,
    tamper: Tamper,
    /// How the ciphertext is read by a decryptor.
    ciphertext: Pacing,
    /// How the output of a decryptor is read.
    output: Pacing,
}

/// A modification of a ciphertext.
#[derive(Arbitrary, Debug)]
enum Tamper {
    /// Cut the ciphertext off at this offset.
    Truncate(u32),
    /// XOR the byte at this offset with a mask.
    Flip {
        offset: u32,
        mask: u8,
    },
    Append(Vec<u8>),
    /// Remove a full chunk.
    RemoveChunk(u8),
    /// Exchange two full chunks.
    SwapChunks(u8, u8),
}

impl Tamper {
    /// Returns the modified ciphertext, or `None` if this modification
    /// doesn't apply to it.
    fn apply(&self, ct: &[u8]) -> Option<Vec<u8>> {
        let mut t = ct.to_vec();
        let full_chunks = (ct.len() - HEADER_SIZE) / ENC_CHUNK_SIZE;
        let chunk = |i: u8| {
            let start = HEADER_SIZE + i as usize % full_chunks * ENC_CHUNK_SIZE;
            start..start + ENC_CHUNK_SIZE
        };
        match self {
            Tamper::Truncate(offset) => t.truncate(*offset as usize % ct.len()),
            Tamper::Flip { offset, mask } => t[*offset as usize % ct.len()] ^= mask,
            Tamper::Append(extra) => t.extend_from_slice(extra),
            Tamper::RemoveChunk(i) if full_chunks > 0 => drop(t.drain(chunk(*i))),
            Tamper::SwapChunks(a, b) if full_chunks > 0 => {
                t[chunk(*a)].copy_from_slice(&ct[chunk(*b)]);
                t[chunk(*b)].copy_from_slice(&ct[chunk(*a)]);
            }
            Tamper::RemoveChunk(_) | Tamper::SwapChunks(..) => return None,
        }
        (t != ct).then_some(t)
    }
}

fuzz_target!(|input: Input| match &input.key {
    AnyKey::Cobblestone128(k) => {
        let mut other = *k;
        other[0] ^= 1;
        run(&Key::from(*k), &Key::from(other), &input)
    }
    AnyKey::Cobblestone256(k) => {
        let mut other = *k;
        other[0] ^= 1;
        run(&Key256::from(*k), &Key256::from(other), &input)
    }
});

fn run(key: &impl CobblestoneKey, other_key: &impl CobblestoneKey, input: &Input) {
    let ctx = &input.context[..];
    let msg = message(&input.len, input.seed);
    let ct = encrypt(key, ctx, &msg).unwrap();

    assert_eq!(decrypt(other_key, ctx, &ct), Err(Error::InvalidCommitment));
    if input.other_context != input.context {
        assert_eq!(
            decrypt(key, &input.other_context, &ct),
            Err(Error::InvalidCommitment)
        );
    }

    let Some(tampered) = input.tamper.apply(&ct) else {
        return;
    };
    assert!(decrypt(key, ctx, &tampered).is_err());

    let mut r = DecryptReader::new(key, ctx, Source::new(&tampered, &input.ciphertext));
    let (out, err) = read_all(&mut r, &input.output);
    assert!(
        err.is_some(),
        "DecryptReader accepted a modified ciphertext"
    );
    assert!(msg.starts_with(&out), "DecryptReader released wrong data");
    // Errors are sticky.
    assert!(r.read(&mut [0; 16]).is_err());

    // Random access only fails when it reads a modified chunk, but the
    // length is authenticated up front, and reading everything must fail.
    if let Ok(mut r) = RandomAccessDecryptor::new(key, ctx, Cursor::new(&tampered)) {
        assert_eq!(r.plaintext_len(), msg.len() as u64);
        let (out, err) = read_all(&mut r, &input.output);
        assert!(
            err.is_some(),
            "random access accepted a modified ciphertext"
        );
        assert!(msg.starts_with(&out), "random access released wrong data");
    }
}
