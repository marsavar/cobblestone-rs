module
public import Cobblestone.Funs
@[expose] public section

open Aeneas Aeneas.Std Result

namespace cobblestone.raw

@[step]
theorem CHUNK_SIZE_spec : CHUNK_SIZE ⦃ r => r.val = 16384 ⦄ := by
  simp only [global_simps]; step*

@[step]
theorem MAX_CHUNKS_spec : MAX_CHUNKS ⦃ r => r.val = 2 ^ 38 ⦄ := by
  simp only [global_simps]; step*

@[step]
theorem ENC_CHUNK_SIZE_spec : ENC_CHUNK_SIZE ⦃ r => r.val = 16400 ⦄ := by
  simp only [global_simps]; step*

@[scalar_tac_simps] theorem TAG_SIZE_val : TAG_SIZE.val = 16 := by simp [global_simps]

theorem ciphertext_size_spec (n : Std.U64) :
    ciphertext_size n ⦃ r =>
      if n.val / 16384 + 1 ≤ 2 ^ 38
      then r.map (·.val) = some (n.val + (n.val / 16384 + 1) * 16)
      else r = none ⦄ := by
  unfold ciphertext_size
  step* <;> simp_all; scalar_tac
