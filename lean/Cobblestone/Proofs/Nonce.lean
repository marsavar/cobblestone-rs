module
public import Cobblestone.Proofs.Sizes
@[expose] public section

open Aeneas Aeneas.Std Result ControlFlow

namespace cobblestone.raw

@[scalar_tac_simps] theorem COUNTER_SIZE_val : COUNTER_SIZE.val = 5 := by simp [global_simps]
@[scalar_tac_simps] theorem NONCE_SIZE_val : NONCE_SIZE.val = 12 := by simp [global_simps]

@[step]
theorem ChunkCipher.nonce_loop_spec (base : Array U8 12#usize) (counter : Array U8 8#usize) :
    ChunkCipher.nonce_loop base counter 0#usize ⦃ r =>
      ∀ k < 12, r.val[k]! =
        if 7 ≤ k then base.val[k]! ^^^ counter.val[k - 4]! else base.val[k]! ⦄ := by
  unfold ChunkCipher.nonce_loop
  apply loop.spec_decr_nat (fun p => 5 - p.2.val)
    (fun p => p.2.val ≤ 5 ∧ ∀ k < 12, p.1.val[k]! =
      if 7 ≤ k ∧ k < 7 + p.2.val then base.val[k]! ^^^ counter.val[k - 4]! else base.val[k]!)
  · rintro ⟨nonce, i⟩ ⟨hi, hinv⟩
    simp only at hi hinv
    unfold ChunkCipher.nonce_loop.body
    step*
    · refine ⟨by scalar_tac, fun k hk => ?_, by scalar_tac⟩
      have hi5 : i5.val = 7 + i.val := by scalar_tac
      have hi2 : i2.val = 3 + i.val := by scalar_tac
      have hi7 : i7 = i6 ^^^ i3 := UScalar.eq_of_val_eq i7_post
      subst a_post hi7 i6_post i3_post
      simp only [Std.Array.set_val_eq]
      by_cases hki : k = 7 + i.val
      · have h := hinv k hk
        simp only [hki, show ¬(7 + i.val < 7 + i.val) from by omega, and_false, ite_false] at h
        have h8 : 7 + i.val < 7 + i8.val := by scalar_tac
        simp_lists [hki, hi5, hi2]
        simp only [show 7 ≤ 7 + i.val by omega, h8, and_self, ite_true,
          show 7 + i.val - 4 = 3 + i.val by omega]
        simp_lists at h
        rw [h]
      · have h := hinv k hk
        have h8 : k < 7 + i.val ↔ k < 7 + i8.val := by scalar_tac
        simp_lists [hki, hi5, h, h8]
    · intro k hk
      have h := hinv k hk
      have h5 : i.val = 5 := by scalar_tac
      rw [h, h5]
      by_cases h7 : 7 ≤ k <;> simp [h7, show k < 12 from hk]
  · simp

def counterBytes (index : U64) : List U8 :=
  index.bv.toBEBytes.map (@UScalar.mk UScalarTy.U8)

@[step]
theorem ChunkCipher.nonce_spec {A : Type} (inst : ChunkAead A) (self : ChunkCipher A)
    (index : U64) (h : index.val < 2 ^ 38) :
    ChunkCipher.nonce inst self index ⦃ r =>
      ∀ k < 12, r.val[k]! =
        if 7 ≤ k then self.base_nonce.val[k]! ^^^ (counterBytes index)[k - 4]!
        else self.base_nonce.val[k]! ⦄ := by
  unfold ChunkCipher.nonce counterBytes
  step*
  rw [← counter_post]; exact r_post k k_post

theorem toBEBytes_low_inj (x y : BitVec 64) (hx : x.toNat < 2 ^ 38) (hy : y.toNat < 2 ^ 38)
    (h : ∀ k, 3 ≤ k → k < 8 → x.toBEBytes[k]! = y.toBEBytes[k]!) : x = y := by
  have h3 := h 3 (by omega) (by omega)
  have h4 := h 4 (by omega) (by omega)
  have h5 := h 5 (by omega) (by omega)
  have h6 := h 6 (by omega) (by omega)
  have h7 := h 7 (by omega) (by omega)
  simp [BitVec.toBEBytes, BitVec.toLEBytes] at h3 h4 h5 h6 h7
  clear h
  bv_omega

theorem u8_xor_left_cancel (a b c : U8) (h : a ^^^ b = a ^^^ c) : b = c := by
  rw [UScalar.eq_equiv_bv_eq] at h ⊢
  simp at h
  exact h

theorem counterBytes_getElem! (x : U64) (k : Nat) (hk : k < 8) :
    (counterBytes x)[k]! = @UScalar.mk UScalarTy.U8 (x.bv.toBEBytes[k]!) := by
  unfold counterBytes
  simp_lists

theorem ChunkCipher.nonce_injective {A : Type} (inst : ChunkAead A) (self : ChunkCipher A)
    (i j : U64) (hi : i.val < 2 ^ 38) (hj : j.val < 2 ^ 38) (n : Std.Array U8 12#usize)
    (hni : ChunkCipher.nonce inst self i = ok n) (hnj : ChunkCipher.nonce inst self j = ok n) :
    i = j := by
  have si := ChunkCipher.nonce_spec inst self i hi
  have sj := ChunkCipher.nonce_spec inst self j hj
  rw [hni, WP.spec_ok] at si
  rw [hnj, WP.spec_ok] at sj
  rw [UScalar.eq_equiv_bv_eq]
  apply toBEBytes_low_inj
  · rw [UScalar.bv_toNat]; exact hi
  · rw [UScalar.bv_toNat]; exact hj
  · intro k hk3 hk8
    have a := si (k + 4) (by omega)
    have b := sj (k + 4) (by omega)
    simp only [show 7 ≤ k + 4 by omega, ite_true, show k + 4 - 4 = k by omega] at a b
    rw [a] at b
    have c := u8_xor_left_cancel _ _ _ b
    rw [counterBytes_getElem! _ _ hk8, counterBytes_getElem! _ _ hk8] at c
    exact UScalar.mk.inj c

end cobblestone.raw
