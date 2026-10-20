import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Ring

/-! Dimension-free logarithmic powers appearing in the Gaussian tube moments.
The moment degree plus the number of active faces controls the total power. -/

namespace RectangleCLT

theorem sqrt_pow_mul_sqrt_pow_le_fourth {L : ℝ} (hL : 1 ≤ L)
    {q k : ℕ} (hqk : q + k ≤ 4) :
    (Real.sqrt L) ^ q * (Real.sqrt L) ^ k ≤ L ^ 2 := by
  have hroot : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).2 hL
  calc
    _ = (Real.sqrt L) ^ (q + k) := (pow_add _ _ _).symm
    _ ≤ (Real.sqrt L) ^ 4 := pow_le_pow_right₀ hroot hqk
    _ = L ^ 2 := by
      calc
        _ = ((Real.sqrt L) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt (zero_le_one.trans hL)]

theorem sqrt_pow_mul_sqrt_pow_le_third {L : ℝ} (hL : 1 ≤ L)
    {q k : ℕ} (hqk : q + k ≤ 3) :
    (Real.sqrt L) ^ q * (Real.sqrt L) ^ k ≤ L * Real.sqrt L := by
  have hroot : 1 ≤ Real.sqrt L := (Real.one_le_sqrt).2 hL
  calc
    _ = (Real.sqrt L) ^ (q + k) := (pow_add _ _ _).symm
    _ ≤ (Real.sqrt L) ^ 3 := pow_le_pow_right₀ hroot hqk
    _ = L * Real.sqrt L := by
      rw [pow_succ, Real.sq_sqrt (zero_le_one.trans hL)]

theorem sqrt_pow_mul_sqrt_pow_le_fourth_of_face_degree {L : ℝ} (hL : 1 ≤ L)
    {q k : ℕ} (hq : q ≤ 4) (hk : k ≤ 4 - q) :
    (Real.sqrt L) ^ q * (Real.sqrt L) ^ k ≤ L ^ 2 :=
  sqrt_pow_mul_sqrt_pow_le_fourth hL (by omega)

theorem sqrt_pow_mul_sqrt_pow_le_third_of_face_degree {L : ℝ} (hL : 1 ≤ L)
    {q k : ℕ} (hq : q ≤ 3) (hk : k ≤ 3 - q) :
    (Real.sqrt L) ^ q * (Real.sqrt L) ^ k ≤ L * Real.sqrt L :=
  sqrt_pow_mul_sqrt_pow_le_third hL (by omega)

end RectangleCLT
