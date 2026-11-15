//! A `RandomAccessDecryptor` must behave like a cursor over the message,
//! whatever sequence of seeks and reads it's given.

#![no_main]

use std::io::{self, Cursor, Read, Seek, SeekFrom};

use arbitrary::Arbitrary;
use cobblestone::{CobblestoneKey, Key, Key256, RandomAccessDecryptor, encrypt};
use cobblestone_fuzz::{AnyKey, Len, message};
use libfuzzer_sys::fuzz_target;

#[derive(Arbitrary, Debug)]
struct Input {
    key: AnyKey,
    context: Vec<u8>,
    len: Len,
    seed: u8,
    ops: Vec<Op>,
}

#[derive(Arbitrary, Debug)]
enum Op {
    SeekStart(u16),
    SeekCurrent(i16),
    SeekEnd(i16),
    Read(u16),
    ReadExactAt { offset: u16, len: u16 },
    // Positions far outside the message, for the overflow checks. The
    // variants above keep most positions inside it.
    SeekStartFar(u64),
    SeekCurrentFar(i64),
    SeekEndFar(i64),
    ReadExactAtFar { offset: u64, len: u16 },
}

fuzz_target!(|input: Input| match &input.key {
    AnyKey::Cobblestone128(k) => run(&Key::from(*k), &input),
    AnyKey::Cobblestone256(k) => run(&Key256::from(*k), &input),
});

fn run(key: &impl CobblestoneKey, input: &Input) {
    let msg = message(&input.len, input.seed);
    let len = msg.len() as u64;
    let ct = encrypt(key, &input.context, &msg).unwrap();
    let mut r = RandomAccessDecryptor::new(key, &input.context, Cursor::new(&ct)).unwrap();
    assert_eq!(r.plaintext_len(), len);

    // The position a cursor over the message would be at.
    let mut pos = 0u64;
    for op in &input.ops {
        match *op {
            Op::SeekStart(n) => seek(&mut r, &mut pos, SeekFrom::Start(n.into()), len),
            Op::SeekCurrent(n) => seek(&mut r, &mut pos, SeekFrom::Current(n.into()), len),
            Op::SeekEnd(n) => seek(&mut r, &mut pos, SeekFrom::End(n.into()), len),
            Op::SeekStartFar(n) => seek(&mut r, &mut pos, SeekFrom::Start(n), len),
            Op::SeekCurrentFar(n) => seek(&mut r, &mut pos, SeekFrom::Current(n), len),
            Op::SeekEndFar(n) => seek(&mut r, &mut pos, SeekFrom::End(n), len),
            Op::Read(n) => {
                let mut buf = vec![0; n as usize];
                let got = r.read(&mut buf).unwrap();
                if pos >= len || n == 0 {
                    assert_eq!(got, 0);
                } else {
                    assert!(got > 0, "read returned EOF before the end");
                    assert_eq!(buf[..got], msg[pos as usize..][..got]);
                    pos += got as u64;
                }
            }
            Op::ReadExactAt { offset, len: n } => read_exact_at(&mut r, &msg, offset.into(), n),
            Op::ReadExactAtFar { offset, len: n } => read_exact_at(&mut r, &msg, offset, n),
        }
        assert_eq!(r.stream_position().unwrap(), pos);
    }
}

fn seek(r: &mut RandomAccessDecryptor<Cursor<&Vec<u8>>>, pos: &mut u64, to: SeekFrom, len: u64) {
    let expected = match to {
        SeekFrom::Start(n) => Some(n),
        SeekFrom::Current(n) => pos.checked_add_signed(n),
        SeekFrom::End(n) => len.checked_add_signed(n),
    };
    match (r.seek(to), expected) {
        (Ok(new), Some(expected)) => {
            assert_eq!(new, expected);
            *pos = new;
        }
        // A failed seek leaves the position alone.
        (Err(_), None) => {}
        (result, expected) => panic!("seek to {to:?}: got {result:?}, expected {expected:?}"),
    }
}

/// Positional reads don't move the cursor, and fail without reading anything
/// if the range isn't inside the message.
fn read_exact_at(r: &mut RandomAccessDecryptor<Cursor<&Vec<u8>>>, msg: &[u8], offset: u64, n: u16) {
    let mut buf = vec![0; n as usize];
    let result = r.read_exact_at(&mut buf, offset);
    match offset.checked_add(n.into()) {
        Some(end) if end <= msg.len() as u64 => {
            result.unwrap();
            assert_eq!(buf, msg[offset as usize..end as usize]);
        }
        _ => assert_eq!(result.unwrap_err().kind(), io::ErrorKind::UnexpectedEof),
    }
}
