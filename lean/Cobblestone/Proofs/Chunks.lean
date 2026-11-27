module
public import Cobblestone.Proofs.Nonce
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow

namespace cobblestone.raw

theorem spec_ok_eq {α : Type} {m : Result α} {p : α → Prop} (h : m ⦃ p ⦄) :
    ∃ v, m = ok v ∧ p v := by
  cases m <;> simp_all

-- The only facts assumed about the AEAD for the chunk-level specs. The length
-- conditions are guaranteed by Rust (the buffer is a `&mut [u8]`); totality holds
-- because the AES-GCM glue in src/aead.rs never returns an error for a chunk.
structure AeadTotal {A : Type} (inst : ChunkAead A) (aead : A) : Prop where
  seal_ok : ∀ n (b : Slice U8), inst.seal aead n b ⦃ t c =>
    inst.seal aead n b = ok (t, c) ∧ c.length = b.length ⦄
  open_ok : ∀ n (c : Slice U8) t, inst.open aead n c t ⦃ v p =>
    inst.open aead n c t = ok (v, p) ∧ p.length = c.length ⦄

@[step]
theorem ChunkCipher.seal_spec {A : Type} (inst : ChunkAead A) (self : ChunkCipher A)
    (hA : AeadTotal inst self.aead) (index : U64) (chunk : Slice U8)
    (hi : index.val < 2 ^ 38) (hc : chunk.length ≤ 16384) :
    ChunkCipher.seal inst self index chunk ⦃ tag c =>
      ∃ n, ChunkCipher.nonce inst self index = ok n ∧
        inst.seal self.aead n chunk = ok (tag, c) ∧ c.length = chunk.length ⦄ := by
  obtain ⟨n, hn, -⟩ := spec_ok_eq (ChunkCipher.nonce_spec inst self index hi)
  unfold ChunkCipher.seal
  simp only [hn]
  step*
  exact WP.spec_mono (hA.seal_ok n chunk) (fun _ h => h)

def OpenedAt {A : Type} (inst : ChunkAead A) (cipher : ChunkCipher A) (index : U64)
    (chunk : Slice U8) (v : Bool) (c : Slice U8) : Prop :=
  ∃ (n : Std.Array U8 12#usize) (d : Slice U8) (t : Std.Array U8 16#usize) (p : Slice U8),
    ChunkCipher.nonce inst cipher index = ok n ∧
    d.val = chunk.val.take (chunk.length - 16) ∧
    t.val = chunk.val.drop (chunk.length - 16) ∧
    inst.open cipher.aead n d t = ok (v, p) ∧
    c.val = p.val ++ t.val

theorem ChunkCipher.open_spec_aux {A : Type} (inst : ChunkAead A) (self : ChunkCipher A)
    (hA : AeadTotal inst self.aead) (index : U64) (chunk : Slice U8)
    (hi : index.val < 2 ^ 38) (hc : chunk.length ≤ 16400) :
    ChunkCipher.open inst self index chunk ⦃ r c =>
      c.length = chunk.length ∧
      if chunk.length < 16 then r = .Err (.DecryptionFailed index) ∧ c = chunk
      else ∃ (n : Std.Array U8 12#usize) (d : Slice U8) (t : Std.Array U8 16#usize) (v : Bool)
          (p : Slice U8),
        ChunkCipher.nonce inst self index = ok n ∧
        d.val = chunk.val.take (chunk.length - 16) ∧
        t.val = chunk.val.drop (chunk.length - 16) ∧
        inst.open self.aead n d t = ok (v, p) ∧
        c.val = p.val ++ t.val ∧
        if v then ∃ len : Usize, r = .Ok len ∧ len.val = chunk.length - 16
        else r = .Err (.DecryptionFailed index) ⦄ := by
  obtain ⟨n, hn, -⟩ := spec_ok_eq (ChunkCipher.nonce_spec inst self index hi)
  unfold ChunkCipher.open
  simp only [hn]
  step*
  · rename_i len hsome
    have htl : tag.len = 16#usize := by scalar_tac
    have hO := hA.open_ok
    simp only [core.array.TryFromSharedArraySlice.try_from, htl, _root_.dite_true,
      core.result.Result.expect]
    step as ⟨v, p, ho, hp⟩
    simp only [hsome] at o_post
    have hlen : len.val = chunk.length - 16 := by scalar_tac
    have hge : ¬ chunk.length < 16 := by scalar_tac
    have hb := data_post4 p tag (by scalar_tac) (by scalar_tac)
    have hd : data.val = chunk.val.take (chunk.length - 16) := by rw [data_post2, hlen]
    have ht : (Std.Array.from tag.val (by scalar_tac) : Std.Array U8 16#usize).val =
        chunk.val.drop (chunk.length - 16) := by simp [data_post3, hlen]
    by_cases hv : v = true
    · simp only [hv, ite_true, WP.spec_ok, WP.uncurry'_pair, hge, ite_false]
      exact ⟨hb.2, n, data, _, v, p, rfl, hd, ht, ho, by rw [hb.1]; simp, by simp [hv, hlen]⟩
    · simp only [hv, Bool.false_eq_true, ite_false, WP.spec_ok, WP.uncurry'_pair, hge]
      exact ⟨hb.2, n, data, _, v, p, rfl, hd, ht, ho, by rw [hb.1]; simp, by simp [hv]⟩

theorem Encryptor.seal_spec {A : Type} (inst : ChunkAead A) (enc : Encryptor A)
    (hA : AeadTotal inst enc.cipher.aead) (chunk : Slice U8) (last : Bool)
    (hf : ¬ enc.finished) (hn : enc.next.val < 2 ^ 38)
    (hlen : if last then chunk.length < 16384 else chunk.length = 16384) :
    Encryptor.seal inst enc chunk last ⦃ r enc' c =>
      enc'.cipher = enc.cipher ∧ c.length = chunk.length ∧
      match r with
      | .Ok tag =>
        (∃ n, ChunkCipher.nonce inst enc.cipher enc.next = ok n ∧
          inst.seal enc.cipher.aead n chunk = ok (tag, c)) ∧
        enc'.next.val = enc.next.val + 1 ∧ enc'.finished = last ∧
        (¬ last → enc'.next.val < 2 ^ 38)
      | .Err e =>
        e = .MessageTooLarge ∧ ¬ last ∧ enc.next.val = 2 ^ 38 - 1 ∧ enc' = enc ∧ c = chunk ⦄ := by
  unfold Encryptor.seal
  step*

@[step]
theorem ChunkCipher.open_spec {A : Type} (inst : ChunkAead A) (self : ChunkCipher A)
    (hA : AeadTotal inst self.aead) (index : U64) (chunk : Slice U8)
    (hi : index.val < 2 ^ 38) (hc : chunk.length ≤ 16400) :
    ChunkCipher.open inst self index chunk ⦃ r c =>
      c.length = chunk.length ∧
      (chunk.length < 16 → r = .Err (.DecryptionFailed index) ∧ c = chunk) ∧
      (16 ≤ chunk.length →
        match r with
        | .Ok len => len.val = chunk.length - 16 ∧ OpenedAt inst self index chunk true c
        | .Err e => e = .DecryptionFailed index ∧ OpenedAt inst self index chunk false c) ⦄ := by
  apply WP.spec_mono (ChunkCipher.open_spec_aux inst self hA index chunk hi hc)
  rintro ⟨r, c⟩ ⟨hl, h⟩
  refine ⟨hl, fun hlt => by simpa [hlt] using h, fun hge => ?_⟩
  simp only [show ¬ chunk.length < 16 by omega, ite_false] at h
  obtain ⟨n, d, t, v, p, hn, hd, ht, ho, hcv, hv⟩ := h
  cases v
  · simp only [Bool.false_eq_true, ite_false] at hv
    subst hv
    exact ⟨rfl, n, d, t, p, hn, hd, ht, ho, hcv⟩
  · simp only [ite_true] at hv
    obtain ⟨len, rfl, hlen⟩ := hv
    exact ⟨hlen, n, d, t, p, hn, hd, ht, ho, hcv⟩

def OpenOk {A : Type} (inst : ChunkAead A) (dec : Decryptor A) (chunk : Slice U8)
    (len : Usize) (dec' : Decryptor A) (c : Slice U8) : Prop :=
  16 ≤ chunk.length ∧ len.val = chunk.length - 16 ∧
  (chunk.length = 16400 → dec.next.val < 2 ^ 38 - 1) ∧
  OpenedAt inst dec.cipher dec.next chunk true c ∧
  dec'.next.val = dec.next.val + 1 ∧ dec'.done = decide (chunk.length < 16400)

def OpenErr {A : Type} (inst : ChunkAead A) (dec : Decryptor A) (chunk : Slice U8)
    (e : Error) (dec' : Decryptor A) (c : Slice U8) : Prop :=
  dec'.next = dec.next ∧ dec'.done = dec.done ∧
  (chunk.length < 16 → e = .Truncated) ∧
  (16 ≤ chunk.length → chunk.length = 16400 → dec.next.val = 2 ^ 38 - 1 →
    e = .MessageTooLarge) ∧
  (16 ≤ chunk.length → (chunk.length < 16400 ∨ dec.next.val < 2 ^ 38 - 1) →
    e = .DecryptionFailed dec.next ∧ OpenedAt inst dec.cipher dec.next chunk false c)

theorem Decryptor.open_inner_spec {A : Type} (inst : ChunkAead A) (dec : Decryptor A)
    (hA : AeadTotal inst dec.cipher.aead) (chunk : Slice U8)
    (hn : dec.next.val < 2 ^ 38) (hc : chunk.length ≤ 16400) :
    Decryptor.open_inner inst dec chunk ⦃ r dec' c =>
      dec'.cipher = dec.cipher ∧ dec'.failed = dec.failed ∧ c.length = chunk.length ∧
      match r with
      | .Ok len => OpenOk inst dec chunk len dec' c
      | .Err e => OpenErr inst dec chunk e dec' c ⦄ := by
  simp only [OpenOk, OpenErr]
  unfold Decryptor.open_inner
  step*
  all_goals
    have h16 : 16 ≤ chunk.length := by scalar_tac
    have hT : TAG_SIZE.val = 16 := TAG_SIZE_val
    have := r_post2 h16
    cases r <;> simp_all
  all_goals scalar_tac

theorem Decryptor.open_spec {A : Type} (inst : ChunkAead A) (dec : Decryptor A)
    (hA : AeadTotal inst dec.cipher.aead) (chunk : Slice U8)
    (hn : dec.next.val < 2 ^ 38) (hc : chunk.length ≤ 16400)
    (hd : dec.failed = none → ¬ dec.done) :
    Decryptor.open inst dec chunk ⦃ r dec' c =>
      dec'.cipher = dec.cipher ∧ c.length = chunk.length ∧
      match dec.failed with
      | some e => r = .Err e ∧ dec' = dec ∧ c = chunk
      | none =>
        match r with
        | .Ok len => OpenOk inst dec chunk len dec' c ∧ dec'.failed = none
        | .Err e => OpenErr inst dec chunk e dec' c ∧ dec'.failed = some e ⦄ := by
  unfold Decryptor.open
  have hI := Decryptor.open_inner_spec inst dec hA chunk hn hc
  have hClone : ∀ e : Error, Error.Insts.CoreCloneClone.clone e = ok e := by
    intro e; cases e <;> simp [Error.Insts.CoreCloneClone.clone, core.clone.impls.CloneU64.clone, lift]
  cases hf : dec.failed with
  | some e => simp [hClone]
  | none =>
    simp only [hClone]
    step*
    rename_i e he
    subst he
    simp only [OpenErr] at *
    simp_all

end cobblestone.raw
