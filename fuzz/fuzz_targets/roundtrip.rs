//! Every way to encrypt a message must produce a ciphertext of the right
//! size that every way to decrypt turns back into the message, however the
//! streams are driven.

#![no_main]

use std::io::{self, Cursor, Read, Write};

use arbitrary::Arbitrary;
use cobblestone::{
    CobblestoneKey, DecryptReader, EncryptReader, EncryptWriter, Key, Key256,
    RandomAccessDecryptor, ciphertext_size, decrypt, encrypt, plaintext_size,
};
use cobblestone_fuzz::{AnyKey, Len, Pace, Pacing, Sink, Source, message, read_all};
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
struct Input {
    key: AnyKey,
    context: Vec<u8>,
    len: Len,
    seed: u8,
    /// How plaintext is written to, or read by, an encryptor.
    plaintext: Pacing,
    /// How ciphertext is written by an encryptor, or read by a decryptor.
    ciphertext: Pacing,
    /// How the output of a reader is read.
    output: Pacing,
}

fuzz_target!(|input: Input| match &input.key {
    AnyKey::Cobblestone128(k) => run(&Key::from(*k), &input),
    AnyKey::Cobblestone256(k) => run(&Key256::from(*k), &input),
});

fn run(key: &impl CobblestoneKey, input: &Input) {
    let ctx = &input.context[..];
    let msg = message(&input.len, input.seed);

    let one_shot = encrypt(key, ctx, &msg).unwrap();
    let written = encrypt_writer(key, input, &msg);
    let r = EncryptReader::new(key, ctx, Source::new(&msg, &input.plaintext));
    let (read, err) = read_all(r, &input.output);
    assert!(err.is_none(), "EncryptReader failed: {err:?}");

    let size = ciphertext_size(msg.len() as u64).unwrap();
    assert_eq!(plaintext_size(size), Ok(msg.len() as u64));
    for ct in [one_shot, written, read] {
        assert_eq!(ct.len() as u64, size);
        assert_eq!(decrypt(key, ctx, &ct).unwrap(), msg);

        let mut r = DecryptReader::new(key, ctx, Source::new(&ct, &input.ciphertext));
        let (out, err) = read_all(&mut r, &input.output);
        assert!(err.is_none(), "DecryptReader failed: {err:?}");
        assert_eq!(out, msg);
        // Reads after the end keep returning EOF.
        assert_eq!(r.read(&mut [0; 16]).unwrap(), 0);

        let mut r = RandomAccessDecryptor::new(key, ctx, Cursor::new(&ct)).unwrap();
        assert_eq!(r.plaintext_len(), msg.len() as u64);
        let (out, err) = read_all(&mut r, &input.output);
        assert!(err.is_none(), "RandomAccessDecryptor failed: {err:?}");
        assert_eq!(out, msg);
    }
}

/// Encrypts with an `EncryptWriter` over a sink that takes partial writes and
/// fails with `WouldBlock`, flushing at arbitrary points.
fn encrypt_writer(key: &impl CobblestoneKey, input: &Input, msg: &[u8]) -> Vec<u8> {
    let sink = Sink::new(&input.ciphertext);
    let mut w = EncryptWriter::new(key, &input.context, sink);
    let mut pace = Pace::new(&input.plaintext);
    let mut rest = msg;
    while !rest.is_empty() {
        let result = match pace.advance() {
            Some(size) => w.write(&rest[..size.min(rest.len())]),
            None => w.flush().map(|()| 0),
        };
        match result {
            Ok(n) => rest = &rest[n..],
            // Nothing was accepted, so the same data is written again.
            Err(e) if e.kind() == io::ErrorKind::WouldBlock => {}
            Err(e) => panic!("EncryptWriter failed: {e}"),
        }
    }
    w.get_ref().set_reliable();
    w.finish().unwrap().out
}
