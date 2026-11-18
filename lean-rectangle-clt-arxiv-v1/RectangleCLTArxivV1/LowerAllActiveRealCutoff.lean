import RectangleCLTCompanion.SplitV4.SymmetricFamilyAllActive
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The literal real-cutoff form of the all-active-column estimate. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem familyActivationCount_real_cutoff_event {n m : ℕ} {b : ℝ} (hb : 0≤b) :
    {z : Fin n → FamilyRestSeed m | (⌊b⌋₊ : ℝ)<familyActivationCount z}=
      {z | b<familyActivationCount z} := by
  ext z
  rw [mem_setOf_eq,mem_setOf_eq,familyActivationCount_columns]
  constructor
  · intro h
    exact (Nat.floor_lt hb).mp (by exact_mod_cast h)
  · intro h
    exact_mod_cast (Nat.floor_lt hb).mpr h

theorem familyMaskedSignMaximum_all_active_bound_real
    (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] {b : ℝ} (hb : 0≤b) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z≠familyActivationCount z} ≤
      (familyRestArrayLaw P n m).real {z | b<familyActivationCount z}+
        Real.exp (-(m:ℝ)*(P.pi/2)^b) := by
  have h := familyMaskedSignMaximum_all_active_bound P n m ⌊b⌋₊
  rw [familyActivationCount_real_cutoff_event hb] at h
  apply h.trans
  apply add_le_add_left
  apply Real.exp_le_exp.mpr
  have hp : 0<P.pi/2 := by linarith [P.pi_pos]
  have hp1 : P.pi/2≤1 := by linarith [P.pi_le_one]
  have hpow : (P.pi/2)^b ≤ (P.pi/2)^(⌊b⌋₊ : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hp hp1 (Nat.floor_le hb)
  rw [Real.rpow_natCast] at hpow
  exact mul_le_mul_of_nonpos_left hpow (neg_nonpos.mpr (Nat.cast_nonneg m))
end
end RectangleCLTArxivV1
