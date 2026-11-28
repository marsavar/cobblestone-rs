module
public import Aeneas
@[expose] public section

/-!
# Chunked encryption, from the specification

This file states the scheme at https://c2sp.org/chunked-encryption directly
from the specification, without reference to the Rust code or its Lean model.
It is meant to be read and checked by a human against the specification. The
conformance theorems in `Proofs/Conformance.lean` prove that the Rust code
computes it.

The hash and the AEAD are parameters: HMAC-SHA-512 and AES-GCM are not
specified here, only how the scheme uses them.
-/

open Aeneas Aeneas.Std

namespace cobblestone.spec

abbrev Bytes := List U8

/-- The two instantiations. Both use SHA-512 as the hash. -/
inductive Instantiation
  | cobblestone128  -- AES-128-GCM
  | cobblestone256  -- AES-256-GCM

/-- The AEAD's name in the IANA AEAD registry, as used in the HKDF info. -/
def aeadName : Instantiation → String
  | .cobblestone128 => "AEAD_AES_128_GCM"
  | .cobblestone256 => "AEAD_AES_256_GCM"

/-- len(key): the input key and the AEAD key have the same size. -/
def keyLen : Instantiation → Nat
  | .cobblestone128 => 16
  | .cobblestone256 => 32

def saltLen : Nat := 24
def commitmentLen : Nat := 32
/-- len(nonce): AES-GCM's nonce size. -/
def nonceLen : Nat := 12
def chunkSize : Nat := 16384
def maxChunks : Nat := 2 ^ 38

/-- The primitives the scheme is built on, as functions. -/
structure Primitives where
  /-- HMAC-SHA-512(key, message). -/
  hmac : Bytes → Bytes → Std.Array U8 64#usize
  /-- AEAD encryption with the given key, nonce and plaintext, and empty
  associated data: the ciphertext followed by the tag. -/
  aeadSeal : Instantiation → Bytes → Bytes → Bytes → Bytes

/-- The bytes of an ASCII string. -/
def ascii (s : String) : Bytes := s.toList.map fun c => ⟨BitVec.ofNat 8 c.toNat⟩

/-- `x` as a big-endian integer of `width` bytes, modulo 2^(8 * width). -/
def bigEndian (width x : Nat) : Bytes :=
  (List.range width).map fun j => ⟨BitVec.ofNat 8 (x / 256 ^ (width - 1 - j))⟩

/-! ## HKDF-Expand, from RFC 5869 section 2.3 -/

/-- T(i) = HMAC(PRK, T(i - 1) || info || i), with T(0) empty. -/
def hkdfT (P : Primitives) (prk info : Bytes) : Nat → Bytes
  | 0 => []
  | i + 1 => (P.hmac prk (hkdfT P prk info i ++ info ++ [⟨BitVec.ofNat 8 (i + 1)⟩])).val

/-- The first `L` bytes of T(1) || T(2) || ... || T(N), N = ceil(L / 64), for
`L ≤ 255 * 64`. -/
def hkdfExpand (P : Primitives) (prk info : Bytes) (L : Nat) : Bytes :=
  ((List.range ((L + 63) / 64)).flatMap fun i => hkdfT P prk info (i + 1)).take L

/-! ## The scheme -/

/-- info = "c2sp.org/chunked-encryption@v1+" || aead || 0x00 || salt || context -/
def info (inst : Instantiation) (salt context : Bytes) : Bytes :=
  ascii "c2sp.org/chunked-encryption@v1+" ++ ascii (aeadName inst) ++ [⟨0#8⟩] ++ salt ++ context

/-- key || base nonce || commitment = HKDF-Expand(input key, info,
len(key) + len(nonce) + 32). -/
def derived (P : Primitives) (inst : Instantiation) (inputKey salt context : Bytes) : Bytes :=
  hkdfExpand P inputKey (info inst salt context) (keyLen inst + nonceLen + commitmentLen)

def aeadKey (P : Primitives) (inst : Instantiation) (inputKey salt context : Bytes) : Bytes :=
  (derived P inst inputKey salt context).take (keyLen inst)

def baseNonce (P : Primitives) (inst : Instantiation) (inputKey salt context : Bytes) : Bytes :=
  ((derived P inst inputKey salt context).drop (keyLen inst)).take nonceLen

def commitment (P : Primitives) (inst : Instantiation) (inputKey salt context : Bytes) : Bytes :=
  (derived P inst inputKey salt context).drop (keyLen inst + nonceLen)

/-- The number of chunks: full 16 KiB chunks, then a final chunk shorter than
16 KiB, which is empty if the length is a multiple of 16 KiB. -/
def numChunks (m : Bytes) : Nat := m.length / chunkSize + 1

/-- Chunk `i` of the plaintext, numbering from zero. -/
def chunk (m : Bytes) (i : Nat) : Bytes := (m.drop (chunkSize * i)).take chunkSize

/-- The nonce of chunk `i`: the base nonce XOR `i` as a big-endian integer as
wide as the nonce. -/
def chunkNonce (base : Bytes) (i : Nat) : Bytes :=
  List.zipWith (· ^^^ ·) base (bigEndian nonceLen i)

/-- The ciphertext of `m`, or `none` if it exceeds 2^38 chunks: salt ||
commitment || the AEAD ciphertexts of the chunks. The input key must be
`keyLen inst` bytes and the salt `saltLen` bytes. -/
def encrypt (P : Primitives) (inst : Instantiation) (inputKey salt context m : Bytes) :
    Option Bytes :=
  if numChunks m > maxChunks then none
  else
    let key := aeadKey P inst inputKey salt context
    let base := baseNonce P inst inputKey salt context
    some (salt ++ commitment P inst inputKey salt context ++
      (List.range (numChunks m)).flatMap fun i => P.aeadSeal inst key (chunkNonce base i) (chunk m i))

end cobblestone.spec
