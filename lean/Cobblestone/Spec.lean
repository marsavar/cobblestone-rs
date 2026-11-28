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

/-- The ciphertext of `m`: salt || commitment || the AEAD ciphertexts of the
chunks. `none` if the input key isn't `keyLen inst` bytes, the salt isn't
`saltLen` bytes, or `m` exceeds 2^38 chunks. -/
def encrypt (P : Primitives) (inst : Instantiation) (inputKey salt context m : Bytes) :
    Option Bytes :=
  if inputKey.length ≠ keyLen inst ∨ salt.length ≠ saltLen ∨ numChunks m > maxChunks then none
  else
    let key := aeadKey P inst inputKey salt context
    let base := baseNonce P inst inputKey salt context
    some (salt ++ commitment P inst inputKey salt context ++
      (List.range (numChunks m)).flatMap fun i => P.aeadSeal inst key (chunkNonce base i) (chunk m i))

/-! ## Checks on the definitions

These follow from the definitions above, and confirm that `encrypt` only uses
the primitives as the specification does.
-/

theorem hkdfT_length (P : Primitives) (prk info : Bytes) (i : Nat) (hi : 0 < i) :
    (hkdfT P prk info i).length = 64 := by
  cases i with
  | zero => omega
  | succ i => simp [hkdfT]

theorem hkdfExpand_length (P : Primitives) (prk info : Bytes) (L : Nat) :
    (hkdfExpand P prk info L).length = L := by
  have h : ∀ n, ((List.range n).flatMap fun i => hkdfT P prk info (i + 1)).length = 64 * n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [List.range_succ, List.flatMap_append, List.length_append, ih]
      simp [hkdfT_length]; ring
  simp only [hkdfExpand, List.length_take, h]; omega

/-- The AEAD key is `keyLen inst` bytes. -/
theorem aeadKey_length (P : Primitives) (inst : Instantiation) (inputKey salt context : Bytes) :
    (aeadKey P inst inputKey salt context).length = keyLen inst := by
  simp [aeadKey, derived, hkdfExpand_length]; omega

/-- The base nonce is `nonceLen` bytes. -/
theorem baseNonce_length (P : Primitives) (inst : Instantiation)
    (inputKey salt context : Bytes) :
    (baseNonce P inst inputKey salt context).length = nonceLen := by
  simp [baseNonce, derived, hkdfExpand_length]; omega

/-- The commitment is `commitmentLen` bytes. -/
theorem commitment_length (P : Primitives) (inst : Instantiation)
    (inputKey salt context : Bytes) :
    (commitment P inst inputKey salt context).length = commitmentLen := by
  simp [commitment, derived, hkdfExpand_length]

/-- Chunk nonces are `nonceLen` bytes. -/
theorem chunkNonce_length (base : Bytes) (h : base.length = nonceLen) (i : Nat) :
    (chunkNonce base i).length = nonceLen := by
  simp [chunkNonce, bigEndian, h]

/-- Every chunk but the last is a full chunk, and the last is shorter. -/
theorem chunk_length (m : Bytes) (i : Nat) (hi : i < numChunks m) :
    (chunk m i).length = if i + 1 < numChunks m then chunkSize else m.length % chunkSize := by
  have hn : numChunks m = m.length / 16384 + 1 := rfl
  rw [hn] at hi
  by_cases h : i + 1 < numChunks m
  · simp only [h, ite_true, chunk, chunkSize, List.length_take, List.length_drop]
    rw [hn] at h; omega
  · simp only [h, ite_false, chunk, chunkSize, List.length_take, List.length_drop]
    rw [hn] at h; omega

/-- The plaintext is the concatenation of its chunks. -/
theorem chunks_concat (m : Bytes) :
    (List.range (numChunks m)).flatMap (chunk m) = m := by
  by_cases hs : m.length < chunkSize
  · have hn : numChunks m = 1 := by simp only [numChunks, chunkSize] at *; omega
    simp [hn, chunk, List.take_of_length_le (le_of_lt hs)]
  · have hn : numChunks m = numChunks (m.drop chunkSize) + 1 := by
      simp only [numChunks, chunkSize, List.length_drop] at *; omega
    have h2 : ∀ j, chunk m (j + 1) = chunk (m.drop chunkSize) j := by
      intro j; simp only [chunk, List.drop_drop]; congr 2; ring
    rw [hn, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    have hf : (fun j => chunk m (Nat.succ j)) = chunk (m.drop chunkSize) := by
      funext j; exact h2 j
    simp only [hf, chunks_concat (m.drop chunkSize)]
    simp [chunk, List.take_append_drop]
termination_by m.length
decreasing_by
  have : chunkSize = 16384 := rfl
  simp only [List.length_drop]; omega

/-- Every AEAD call `encrypt` makes uses a key of `keyLen inst` bytes, a nonce of
`nonceLen` bytes, and a chunk index below `maxChunks`, so `bigEndian`'s
reduction modulo 2^96 never applies. -/
theorem encrypt_calls (P : Primitives) (inst : Instantiation) (inputKey salt context m : Bytes)
    (ct : Bytes) (h : encrypt P inst inputKey salt context m = some ct) (i : Nat)
    (hi : i < numChunks m) :
    (aeadKey P inst inputKey salt context).length = keyLen inst ∧
    (chunkNonce (baseNonce P inst inputKey salt context) i).length = nonceLen ∧
    i < maxChunks := by
  have hb : numChunks m ≤ maxChunks := by
    by_contra hc
    simp only [encrypt] at h
    rw [ite_eq_left (Or.inr (Or.inr (by omega)))] at h
    cases h
  exact ⟨aeadKey_length .., chunkNonce_length _ (baseNonce_length ..) i, by omega⟩

end cobblestone.spec
