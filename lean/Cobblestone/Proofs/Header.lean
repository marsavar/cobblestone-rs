module
public import Cobblestone.Proofs.Message
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone.header

def hkdfT (hmac : List U8 → List U8 → Std.Array U8 64#usize) (prk info : List U8) :
    Nat → List U8
  | 0 => []
  | i + 1 => (hmac prk (hkdfT hmac prk info i ++ info ++ [⟨BitVec.ofNat 8 (i + 1)⟩])).val

def hkdfBlocks (hmac : List U8 → List U8 → Std.Array U8 64#usize) (prk info : List U8) :
    Nat → List U8
  | 0 => []
  | n + 1 => hkdfBlocks hmac prk info n ++ hkdfT hmac prk info (n + 1)

/-- HKDF-Expand from RFC 5869, for `L ≤ 255 * 64`. -/
def hkdfExpand (hmac : List U8 → List U8 → Std.Array U8 64#usize) (prk info : List U8)
    (L : Nat) : List U8 :=
  (hkdfBlocks hmac prk info 255).take L

variable {M : Type} {inst : Mac M} {hmac : List U8 → List U8 → Std.Array U8 64#usize}
  {st : M → List U8 × List U8}

@[step]
theorem hkdf_block_spec (hM : MacLaws inst hmac st) (prk prev label salt context : Slice U8)
    (counter : U8) :
    hkdf_block inst prk prev label salt context counter ⦃ t =>
      t = hmac prk.val (prev.val ++ label.val ++ salt.val ++ context.val ++ [counter]) ⦄ := by
  have hN := hM.new_spec
  have hU := hM.update_spec
  have hF := hM.finalize_spec
  unfold hkdf_block
  step*

theorem hkdfT_length (prk info : List U8) (i : Nat) (hi : 0 < i) :
    (hkdfT hmac prk info i).length = 64 := by
  cases i with
  | zero => omega
  | succ i => simp [hkdfT]

theorem hkdfBlocks_length (prk info : List U8) (n : Nat) :
    (hkdfBlocks hmac prk info n).length = 64 * n := by
  induction n with
  | zero => simp [hkdfBlocks]
  | succ n ih => simp [hkdfBlocks, ih, hkdfT_length]; ring

theorem hkdfBlocks_prefix (prk info : List U8) (k n : Nat) (h : k ≤ n) :
    ∃ rest, hkdfBlocks hmac prk info n = hkdfBlocks hmac prk info k ++ rest := by
  induction n with
  | zero => exact ⟨[], by simp [show k = 0 by omega]⟩
  | succ n ih =>
    by_cases hk : k = n + 1
    · exact ⟨[], by simp [hk]⟩
    · obtain ⟨rest, hr⟩ := ih (by omega)
      exact ⟨rest ++ hkdfT hmac prk info (n + 1), by simp [hkdfBlocks, hr]⟩

theorem hkdfExpand_length (prk info : List U8) (L : Nat) (hL : L ≤ 255 * 64) :
    (hkdfExpand hmac prk info L).length = L := by
  simp [hkdfExpand, hkdfBlocks_length]; omega

theorem hkdfBlocks_take (prk info : List U8) (k L : Nat) (hk : k ≤ 255) (hL : L ≤ 64 * k) :
    (hkdfBlocks hmac prk info k).take L = hkdfExpand hmac prk info L := by
  obtain ⟨rest, hr⟩ := hkdfBlocks_prefix (hmac := hmac) prk info k 255 hk
  rw [hkdfExpand, hr, List.take_append_of_le_length (by rw [hkdfBlocks_length]; exact hL)]

theorem take_setSlice {α : Type} (l s : List α) (i : Nat) (h : i + s.length ≤ l.length) :
    (l.setSlice! i s).take (i + s.length) = l.take i ++ s := by
  have hm : min s.length (l.length - i) = s.length := by omega
  have hi : (List.take i l).length = i := by simp; omega
  simp only [List.setSlice!, hm, List.take_length, List.append_assoc, List.take_append, hi]
  simp

theorem hkdfBlocks_succ_take (prk info : List U8) (k len : Nat) (hlen : len ≤ 64) :
    (hkdfBlocks hmac prk info (k + 1)).take (64 * k + len) =
      hkdfBlocks hmac prk info k ++ (hkdfT hmac prk info (k + 1)).take len := by
  rw [hkdfBlocks, List.take_append, hkdfBlocks_length,
    List.take_of_length_le (by rw [hkdfBlocks_length]; omega)]
  simp

theorem u8_eq_ofNat (c : U8) (n : Nat) (h : c.val = n) (hn : n < 256) :
    c = ⟨BitVec.ofNat 8 n⟩ := by
  apply UScalar.eq_of_val_eq
  rw [h]
  show n = (BitVec.ofNat 8 n).toNat
  rw [BitVec.toNat_ofNat]; omega

theorem hkdfT_zero (prk info : List U8) : hkdfT hmac prk info 0 = [] := rfl

theorem hkdfT_succ (prk info : List U8) (k : Nat) :
    hkdfT hmac prk info (k + 1) =
      (hmac prk (hkdfT hmac prk info k ++ info ++ [⟨BitVec.ofNat 8 (k + 1)⟩])).val := rfl

theorem take64_array (a : Std.Array U8 64#usize) : a.val.take 64 = a.val := by
  apply List.take_of_length_le; simp

@[scalar_tac_simps] theorem COMMITMENT_SIZE_val : COMMITMENT_SIZE.val = 32 := by simp [global_simps]
@[scalar_tac_simps] theorem SALT_SIZE_val : SALT_SIZE.val = 24 := by simp [global_simps]

@[scalar_tac_simps] theorem HASH_SIZE_val : HASH_SIZE.val = 64 := by simp [global_simps]

@[step]
theorem hkdf_expand_loop_spec (hM : MacLaws inst hmac st)
    (prk label salt context out : Slice U8) (t : Std.Array U8 64#usize)
    (hlen : out.length ≤ 255 * 64) :
    hkdf_expand_loop inst prk label salt context out t 0#usize ⦃ out' _ =>
      out'.val = hkdfExpand hmac prk.val (label.val ++ salt.val ++ context.val) out.length ⦄ := by
  have hB := hkdf_block_spec hM
  unfold hkdf_expand_loop
  apply loop.spec_decr_nat (fun p => out.length - p.2.2.val)
    (fun p => p.1.length = out.length ∧ ∃ k, k ≤ 255 ∧ p.2.2.val = min (64 * k) out.length ∧
      (0 < k → p.2.1.val = hkdfT hmac prk.val (label.val ++ salt.val ++ context.val) k) ∧
      p.1.val.take p.2.2.val =
        (hkdfBlocks hmac prk.val (label.val ++ salt.val ++ context.val) k).take p.2.2.val)
  · rintro ⟨out1, t1, start⟩ ⟨hl1, k, hk, hstart, ht, hpre⟩
    simp only at hl1 hstart ht hpre
    unfold hkdf_expand_loop.body
    step*
    · rw [s1_post1, s2_post1, i5_post]; omega
    · have hHS : HASH_SIZE.val = 64 := HASH_SIZE_val
      have hl1' : out1.val.length = out.length := hl1
      have hlt : start.val < out.length := by
        have h := ‹start < out1.len›
        rw [UScalar.lt_equiv, Slice.len_val] at h; omega
      have hs64 : start.val = 64 * k := by omega
      have hk1 : k + 1 ≤ 255 := by omega
      have hpl : prev_len.val = min start.val 64 := by
        rw [prev_len_post, core.cmp.impls.OrdUsize.min_val, hHS]
      have hcv : counter.val = k + 1 := by
        rw [counter_post, UScalar.cast_val_eq, i2_post, i1_post, hHS, hs64,
          show 64 * k / 64 = k by omega, UScalarTy.U8_numBits_eq]
        exact Nat.mod_eq_of_lt (by omega)
      have hlv : len.val = min (out.length - start.val) 64 := by
        rw [len_post, core.cmp.impls.OrdUsize.min_val, i4_post, hHS, Slice.len_val, hl1]
      have hcnt : counter = ⟨BitVec.ofNat 8 (k + 1)⟩ := u8_eq_ofNat _ _ hcv (by omega)
      have hsv : s.val = hkdfT hmac prk.val (label.val ++ salt.val ++ context.val) k := by
        rw [s_post, List.slice_zero_j, Aeneas.Std.Array.val_to_slice, hpl]
        rcases Nat.eq_zero_or_pos k with h0 | h0
        · subst h0; simp [hs64, hkdfT_zero]
        · rw [show min start.val 64 = 64 by omega, ← ht h0]; exact take64_array _
      have hT : t1.val = hkdfT hmac prk.val (label.val ++ salt.val ++ context.val) (k + 1) := by
        rw [t1_post, hkdfT_succ, ← hsv, hcnt]
        simp only [List.append_assoc]
      have hpre' : out1.val.take start.val =
          hkdfBlocks hmac prk.val (label.val ++ salt.val ++ context.val) k := by
        rw [hpre, hs64, List.take_of_length_le (by rw [hkdfBlocks_length])]
      have hs2 : s2.val = (hkdfT hmac prk.val (label.val ++ salt.val ++ context.val)
          (k + 1)).take len.val := by
        rw [s2_post, ← hT, List.slice_zero_j, Aeneas.Std.Array.val_to_slice]
      have hs2l : s2.val.length = len.val := by
        rw [hs2, List.length_take, hkdfT_length _ _ _ (by omega)]; omega
      have hl3 : (index_mut_back s3).length = out.length := by
        rw [s3_post, s1_post2, Slice.setSlice!_length]; exact hl1
      refine ⟨hl3, ⟨k + 1, hk1, by omega, fun _ => hT, ?_⟩, by omega⟩
      rw [s3_post, s1_post2, Slice.setSlice!_val,
        show i5.val = start.val + s2.val.length by omega,
        take_setSlice _ _ _ (by omega), hpre', hs2, List.length_take,
        hkdfT_length _ _ _ (by omega),
        show min len.val 64 = len.val by omega, hs64,
        hkdfBlocks_succ_take _ _ _ _ (by omega)]
    · have hge : out.length ≤ start.val := by
        have h := ‹¬ start < out1.len›
        rw [UScalar.lt_equiv, Slice.len_val] at h; omega
      have hl1' : out1.val.length = out.length := hl1
      rw [← hkdfBlocks_take _ _ k _ hk (by omega), ← List.take_of_length_le (le_of_eq hl1'),
        show out.length = start.val by omega, hpre]
  · exact ⟨rfl, 0, by omega, by simp, by simp, by simp⟩

@[step]
theorem hkdf_expand_spec (hM : MacLaws inst hmac st)
    (prk label salt context out : Slice U8) (t : Std.Array U8 64#usize)
    (hlen : out.length ≤ 255 * 64) :
    hkdf_expand inst prk label salt context out t ⦃ out' _ =>
      out'.val = hkdfExpand hmac prk.val (label.val ++ salt.val ++ context.val) out.length ∧
      out'.length = out.length ⦄ := by
  have hL := hkdf_expand_loop_spec hM prk label salt context out t hlen
  unfold hkdf_expand
  step*
  simp [Slice.length, out'_post, hkdfExpand_length _ _ _ hlen]

-- Character codes rather than String.toUTF8, which the kernel can't evaluate.
-- They are the same bytes for the ASCII labels below.
def asciiBytes (s : String) : List U8 :=
  s.toList.map fun c => ⟨BitVec.ofNat 8 c.toNat⟩

def suiteLabel : Suite → List U8
  | .Aes128 => asciiBytes "c2sp.org/chunked-encryption@v1+AEAD_AES_128_GCM" ++ [⟨0#8⟩]
  | .Aes256 => asciiBytes "c2sp.org/chunked-encryption@v1+AEAD_AES_256_GCM" ++ [⟨0#8⟩]

def Derived {A : Type} (initI : AeadInit A) (hmac : List U8 → List U8 → Std.Array U8 64#usize)
    (suite : Suite) (key salt context : List U8) (cipher : raw.ChunkCipher A)
    (commitment : Std.Array U8 32#usize) : Prop :=
  let okm := hkdfExpand hmac key (suiteLabel suite ++ salt ++ context) (key.length + 44)
  (∃ k : Slice U8, k.val = okm.take key.length ∧ initI.new suite k = ok cipher.aead) ∧
  cipher.base_nonce.val = (okm.drop key.length).take 12 ∧
  commitment.val = okm.drop (key.length + 12)

theorem suiteLabel_aes128 : suiteLabel .Aes128 = [99#u8, 50#u8, 115#u8, 112#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 99#u8, 104#u8, 117#u8, 110#u8, 107#u8, 101#u8, 100#u8, 45#u8, 101#u8, 110#u8, 99#u8, 114#u8, 121#u8, 112#u8, 116#u8, 105#u8, 111#u8, 110#u8, 64#u8, 118#u8, 49#u8, 43#u8, 65#u8, 69#u8, 65#u8, 68#u8, 95#u8, 65#u8, 69#u8, 83#u8, 95#u8, 49#u8, 50#u8, 56#u8, 95#u8, 71#u8, 67#u8, 77#u8, 0#u8] := by decide

theorem suiteLabel_aes256 : suiteLabel .Aes256 = [99#u8, 50#u8, 115#u8, 112#u8, 46#u8, 111#u8, 114#u8, 103#u8, 47#u8, 99#u8, 104#u8, 117#u8, 110#u8, 107#u8, 101#u8, 100#u8, 45#u8, 101#u8, 110#u8, 99#u8, 114#u8, 121#u8, 112#u8, 116#u8, 105#u8, 111#u8, 110#u8, 64#u8, 118#u8, 49#u8, 43#u8, 65#u8, 69#u8, 65#u8, 68#u8, 95#u8, 65#u8, 69#u8, 83#u8, 95#u8, 50#u8, 53#u8, 54#u8, 95#u8, 71#u8, 67#u8, 77#u8, 0#u8] := by decide

@[step]
theorem derive_spec {A : Type} {initI : AeadInit A} (hM : MacLaws inst hmac st)
    (hI : AeadInitLaws initI) (suite : Suite) (key : Slice U8) (salt : Std.Array U8 24#usize)
    (context : Slice U8) (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize)
    (hk : key.length = suiteKeyLen suite) :
    derive inst initI suite key salt context okm t ⦃ cc _ _ =>
      Derived initI hmac suite key.val salt.val context.val cc.1 cc.2 ⦄ := by
  have hH := hkdf_expand_spec hM
  have hN := hI.new_ok
  unfold derive
  cases suite <;> simp only [suiteKeyLen] at hk <;> step*
  all_goals first
    | (simp only [suiteKeyLen]; scalar_tac)
    | have hnl : nonce.len = 12#usize := by scalar_tac
      simp only [core.array.TryFromSharedArraySlice.try_from, hnl, _root_.dite_true,
        core.result.Result.unwrap, bind_ok, raw.ChunkCipher.new]
      step*
      have hcl : commitment.length = 32 := by scalar_tac
      have hol : out.length = key.length + 44 := by scalar_tac
      cases r1 with
      | Err e => simp only at r1_post; exact absurd hcl r1_post
      | Ok a1 =>
        obtain ⟨ha1, -⟩ := r1_post
        simp only [bind_ok, WP.spec_ok, WP.uncurry'_pair]
        simp only [s_post, Aeneas.Std.Array.val_to_slice, Aeneas.Std.Array.make_val, hol]
          at out1_post
        unfold Derived
        simp only [suiteLabel_aes128, suiteLabel_aes256]
        refine ⟨⟨aead_key, ?_, t2_post⟩, ?_, ?_⟩
        · rw [aead_key_post2, out1_post]; rfl
        · simp only [Std.Array.from_val, nonce_post2, aead_key_post3, out1_post,
            raw.NONCE_SIZE_val, Slice.len_val]
        · rw [ha1, nonce_post3, aead_key_post3, out1_post, raw.NONCE_SIZE_val, Slice.len_val,
            List.drop_drop]

theorem Derived_unique {A : Type} {initI : AeadInit A} {suite : Suite} {key salt context : List U8}
    {c c' : raw.ChunkCipher A} {cm cm' : Std.Array U8 32#usize}
    (h : Derived initI hmac suite key salt context c cm)
    (h' : Derived initI hmac suite key salt context c' cm') : c = c' ∧ cm = cm' := by
  obtain ⟨⟨k, hk, hn⟩, hb, hc⟩ := h
  obtain ⟨⟨k', hk', hn'⟩, hb', hc'⟩ := h'
  have hkk : k = k' := by rw [Slice.eq_iff, hk, hk']
  subst hkk
  rw [hn, raw.ok_eq_ok_iff] at hn'
  refine ⟨?_, Std.Array.ext _ _ (by rw [hc, hc'])⟩
  cases c; cases c'
  simp only at hn' hb hb'
  rw [raw.ChunkCipher.mk.injEq]
  exact ⟨hn', Std.Array.ext _ _ (by rw [hb, hb'])⟩

@[step]
theorem new_header_spec {A : Type} {initI : AeadInit A} (hM : MacLaws inst hmac st)
    (hI : AeadInitLaws initI) (suite : Suite) (key : Slice U8) (salt : Std.Array U8 24#usize)
    (context : Slice U8) (okm : Std.Array U8 76#usize) (t : Std.Array U8 64#usize)
    (hk : key.length = suiteKeyLen suite) :
    new_header inst initI suite key salt context okm t ⦃ he _ _ =>
      ∃ cm, Derived initI hmac suite key.val salt.val context.val he.2.cipher cm ∧
        he.1.val = salt.val ++ cm.val ∧ he.2.next = 0#u64 ∧ he.2.finished = false ⦄ := by
  unfold new_header
  step as ⟨cc, okm1, t1, hD⟩
  obtain ⟨cipher, cm⟩ := cc
  step*
  simp only [raw.Encryptor.new, bind_ok, WP.spec_ok, WP.uncurry'_pair]
  refine ⟨cm, hD, ?_, trivial, trivial⟩
  rw [s3_post2, s5_post, s4_post, s_post2, s2_post, s1_post]
  simp [List.setSlice!, SALT_SIZE_val, Aeneas.Std.Array.val_to_slice]
  rw [List.take_of_length_le (by simp), List.take_of_length_le (by simp)]

@[step]
theorem open_header_spec {A C : Type} {initI : AeadInit A} {ctI : CtEq C}
    (hM : MacLaws inst hmac st) (hI : AeadInitLaws initI) (hC : CtEqLaws ctI) (suite : Suite)
    (key context : Slice U8) (bytes : Std.Array U8 56#usize) (okm : Std.Array U8 76#usize)
    (t : Std.Array U8 64#usize) (hk : key.length = suiteKeyLen suite) :
    open_header inst initI ctI suite key context bytes okm t ⦃ r _ _ =>
      ∃ c cm, Derived initI hmac suite key.val (bytes.val.take 24) context.val c cm ∧
        if bytes.val.drop 24 = cm.val then r = .Ok c else r = .Err .InvalidCommitment ⦄ := by
  have hE := hC.ct_eq_spec
  unfold open_header
  step*
  have hsl : salt.len = 24#usize := by scalar_tac
  have hcl : commitment.len = 32#usize := by scalar_tac
  simp only [core.array.TryFromSharedArraySlice.try_from, hsl, hcl, _root_.dite_true,
    core.result.Result.unwrap, bind_ok]
  step as ⟨cc, okm1, t1, hD⟩
  obtain ⟨cipher, cm⟩ := cc
  step as ⟨b, hb⟩
  have hsv : salt.val = bytes.val.take 24 := by
    rw [salt_post2, s_post, Aeneas.Std.Array.val_to_slice, SALT_SIZE_val]
  have hcv : commitment.val = bytes.val.drop 24 := by
    rw [salt_post3, s_post, Aeneas.Std.Array.val_to_slice, SALT_SIZE_val]
  simp only [Std.Array.from_val, hsv] at hD
  have heq : (Std.Array.from commitment.val (by scalar_tac) : Std.Array U8 32#usize) = cm ↔
      bytes.val.drop 24 = cm.val := by
    rw [Std.Array.eq_iff, Std.Array.from_val, hcv]
  by_cases hc : bytes.val.drop 24 = cm.val
  · have hbt : b = true := by rw [hb]; exact decide_eq_true (heq.mpr hc)
    simp only [hbt, ite_true, WP.spec_ok, WP.uncurry'_pair]
    exact ⟨cipher, cm, hD, by simp [hc]⟩
  · have hbf : b = false := by rw [hb]; exact decide_eq_false (fun h => hc (heq.mp h))
    simp only [hbf, Bool.false_eq_true, ite_false, WP.spec_ok, WP.uncurry'_pair]
    exact ⟨cipher, cm, hD, by simp [hc]⟩

end cobblestone.header
