module
public import Cobblestone.Theorems
@[expose] public section

/-!
# The assumptions can all hold at once

The theorems take the assumptions in `Assumptions.lean` as hypotheses. If they
contradicted each other, every theorem would hold vacuously. This file gives
primitives that satisfy all of them together, so they don't.

The primitives are deliberately trivial: an "AEAD" that leaves the data as it
is and whose tag is the nonce, a "MAC" that ignores its input, and equality as
the comparison. They only show consistency, and have no security at all.
-/

open Aeneas Aeneas.Std Result

namespace cobblestone.consistency

open spec raw header conformance

def tagOf (n : Std.Array U8 12#usize) : Std.Array U8 16#usize :=
  Std.Array.from (n.val ++ List.replicate 4 0#u8) (by simp)

def toyAead : ChunkAead Unit where
  «seal» _ n b := ok (tagOf n, b)
  «open» _ n c t := ok (decide (t = tagOf n), c)

def toyInit : AeadInit Unit where
  rawChunkAeadInst := toyAead
  new _ _ := ok ()

def toyMac : Mac (List U8 × List U8) where
  new k := ok (k.val, [])
  update m d := ok (m.1, m.2 ++ d.val)
  finalize _ := ok (Std.Array.repeat 64#usize 0#u8)

def toyCtEq : CtEq Unit where
  ct_eq a b := ok (decide (a = b))

def toyPrimitives : Primitives where
  hmac _ _ := Std.Array.repeat 64#usize 0#u8
  aeadSeal _ _ n b := b ++ n ++ List.replicate 4 0#u8

theorem toy_total (a : Unit) : AeadTotal toyInit.rawChunkAeadInst a :=
  ⟨fun n b => by simp [toyInit, toyAead], fun n c t => by simp [toyInit, toyAead]⟩

theorem toy_correct (a : Unit) : AeadCorrect toyInit.rawChunkAeadInst a :=
  ⟨fun n b t c h => by
    simp only [toyInit, toyAead, ok_eq_ok_iff, Prod.mk.injEq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    simp⟩

theorem toy_tagCheck (a : Unit) : AeadTagCheck toyInit.rawChunkAeadInst a :=
  ⟨fun n c t b h => by
    simp only [toyInit, toyAead, ok_eq_ok_iff, Prod.mk.injEq, decide_eq_true_eq] at h ⊢
    obtain ⟨rfl, rfl⟩ := h
    simp⟩

theorem toy_mac : MacLaws toyMac toyPrimitives.hmac id :=
  ⟨fun k => by simp [toyMac], fun m d => by simp [toyMac], fun m => by simp [toyMac, toyPrimitives]⟩

theorem toy_init : AeadInitLaws toyInit :=
  ⟨fun s k _ => by simp [toyInit]⟩

theorem toy_ctEq : CtEqLaws toyCtEq :=
  ⟨fun a b => by simp [toyCtEq]⟩

theorem toy_seal : SealImplements toyPrimitives toyInit :=
  ⟨fun i k a _ n b t c h => by
    simp only [toyInit, toyAead, ok_eq_ok_iff, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp [tagOf, toyPrimitives]⟩

/-- All the assumptions hold together for some primitives. -/
theorem assumptions_consistent :
    ∃ (M A C : Type) (macI : Mac M) (initI : AeadInit A) (ctI : CtEq C) (P : Primitives)
      (st : M → List U8 × List U8),
      MacLaws macI P.hmac st ∧ AeadInitLaws initI ∧ CtEqLaws ctI ∧ SealImplements P initI ∧
      (∀ a, AeadTotal initI.rawChunkAeadInst a) ∧ (∀ a, AeadCorrect initI.rawChunkAeadInst a) ∧
      (∀ a, AeadTagCheck initI.rawChunkAeadInst a) :=
  ⟨_, _, _, toyMac, toyInit, toyCtEq, toyPrimitives, id, toy_mac, toy_init, toy_ctEq, toy_seal,
    toy_total, toy_correct, toy_tagCheck⟩

/-- The top-level theorems apply to these primitives: encrypting the empty message
with Cobblestone-128 conforms to the specification. -/
example (salt : Std.Array U8 24#usize) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) :
    ∃ ct, spec.encrypt toyPrimitives .cobblestone128 (List.replicate 16 0#u8) salt.val [] [] =
        some ct ∧
      encryptMsg toyMac toyInit (toSuite .cobblestone128) (Slice.from (List.replicate 16 0#u8)
        (by scalar_tac)) salt (Slice.from [] (by simp)) okm t [] = ok (.Ok ct) := by
  have := theorems.encrypt_conforms toy_mac toy_init toy_seal toy_total .cobblestone128
    (Slice.from (List.replicate 16 0#u8) (by scalar_tac)) (by simp [Slice.length, keyLen]) salt
    (Slice.from [] (by simp)) okm t [] (by simp [numChunks, maxChunks, chunkSize])
  simpa using this

end cobblestone.consistency
