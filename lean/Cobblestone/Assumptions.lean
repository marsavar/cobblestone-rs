module
public import Cobblestone.Funs
public import Cobblestone.Spec
@[expose] public section

/-!
# What the proofs assume

Every theorem about the Rust code takes some of these as hypotheses. They are
the only facts assumed about the code outside the Lean model: AES-GCM,
HMAC-SHA-512 and the constant-time comparison, reached through the traits in
`src/raw.rs` and `src/header.rs` and implemented in `src/primitives.rs`. None
of them is an axiom, so a false one could only make the theorems that use it
inapplicable, not prove anything else.

Each one is a functional property of the real primitive, with no cryptographic
assumption:

- `AeadTotal`: sealing and opening a chunk always return, and keep the buffer
  length.
- `AeadCorrect`: opening a sealed chunk gives back its plaintext.
- `AeadTagCheck`: a tag is accepted only if re-sealing the plaintext gives the
  same ciphertext and tag. True of AES-GCM because decryption is the same
  keystream XOR, and the tag is checked against the one encryption computes.
- `SealImplements`: sealing computes the specification's AEAD.
- `MacLaws`: the incremental MAC computes the specification's HMAC.
- `AeadInitLaws`: creating the AEAD succeeds for a key of the right size.
- `CtEqLaws`: the constant-time comparison returns equality.

See `Theorems.lean` for what is proved from them.
-/

open Aeneas Aeneas.Std Result

namespace cobblestone.raw

-- The only facts assumed about the AEAD for the chunk-level specs. The length
-- conditions are guaranteed by Rust (the buffer is a `&mut [u8]`); totality holds
-- because the AES-GCM glue in src/primitives.rs never returns an error for a chunk.
structure AeadTotal {A : Type} (inst : ChunkAead A) (aead : A) : Prop where
  seal_ok : ∀ n (b : Slice U8), inst.seal aead n b ⦃ t c =>
    inst.seal aead n b = ok (t, c) ∧ c.length = b.length ⦄
  open_ok : ∀ n (c : Slice U8) t, inst.open aead n c t ⦃ v p =>
    inst.open aead n c t = ok (v, p) ∧ p.length = c.length ⦄

-- The two AEAD properties the message theorems assume, on top of AeadTotal.
-- Both hold for AES-GCM as plain functional facts, without any cryptographic
-- assumption: decryption inverts encryption, and a tag is accepted only if it
-- equals the one encryption computes, so re-sealing an accepted plaintext
-- reproduces the same ciphertext and tag.
structure AeadCorrect {A : Type} (inst : ChunkAead A) (aead : A) : Prop where
  open_seal : ∀ n b t c, inst.seal aead n b = ok (t, c) → inst.open aead n c t = ok (true, b)

structure AeadTagCheck {A : Type} (inst : ChunkAead A) (aead : A) : Prop where
  seal_open : ∀ n c t b, inst.open aead n c t = ok (true, b) → inst.seal aead n b = ok (t, c)

end cobblestone.raw

namespace cobblestone.header

-- The only facts assumed about the MAC: through an abstraction of its state,
-- `new` starts an empty message, `update` appends to it, and `finalize` returns
-- `hmac key message`. `hmac` itself is left abstract.
structure MacLaws {M : Type} (inst : Mac M) (hmac : List U8 → List U8 → Std.Array U8 64#usize)
    (st : M → List U8 × List U8) : Prop where
  new_spec : ∀ k : Slice U8, inst.new k ⦃ m => st m = (k.val, []) ⦄
  update_spec : ∀ m (d : Slice U8), inst.update m d ⦃ m' => st m' = ((st m).1, (st m).2 ++ d.val) ⦄
  finalize_spec : ∀ m, inst.finalize m ⦃ t => t = hmac (st m).1 (st m).2 ⦄

def suiteKeyLen : Suite → Nat
  | .Aes128 => 16
  | .Aes256 => 32

-- The only fact assumed about creating the AEAD: it succeeds for a key of the
-- instantiation's size. It is deterministic because it is a function.
structure AeadInitLaws {A : Type} (inst : AeadInit A) : Prop where
  new_ok : ∀ s (k : Slice U8), k.length = suiteKeyLen s → inst.new s k ⦃ a => inst.new s k = ok a ⦄

-- The only fact assumed about the comparison: it is equality. That it runs in
-- constant time is outside what these proofs can express.
structure CtEqLaws {C : Type} (inst : CtEq C) : Prop where
  ct_eq_spec : ∀ a b, inst.ct_eq a b ⦃ r => r = decide (a = b) ⦄

end cobblestone.header

namespace cobblestone.conformance

open spec header

def toSuite : Instantiation → Suite
  | .cobblestone128 => .Aes128
  | .cobblestone256 => .Aes256

/-- The AEAD the implementation creates and calls computes the specification's
AEAD: sealing `b` under nonce `n` with the AEAD created from key `k` gives the
ciphertext followed by the tag, `aeadSeal k n b`. -/
structure SealImplements {A : Type} (P : Primitives) (initI : AeadInit A) : Prop where
  sealed : ∀ i (k : Slice U8) a, initI.new (toSuite i) k = ok a →
    ∀ n (b : Slice U8) t c, initI.rawChunkAeadInst.seal a n b = ok (t, c) →
      c.val ++ t.val = P.aeadSeal i k.val n.val b.val

end cobblestone.conformance
