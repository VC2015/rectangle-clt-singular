import RectangleCLT.BernoulliPath
import Mathlib.Logic.Equiv.Prod

/-! Exact finite selector identities used in differentiation of the Bernoulli
interpolation. The statements are polynomial identities for every real
selector parameter; positivity is not assumed. -/

open scoped BigOperators

namespace RectangleCLT.BernoulliSelectorAlgebra

abbrev Rest (n : ℕ) (i : Fin n) := {j : Fin n // j ≠ i} → Bool

def joinMask {n : ℕ} (i : Fin n) (b : Bool) (r : Rest n i) : Kane.Cube n :=
  (Equiv.funSplitAt i Bool).symm (b, r)

@[simp] theorem joinMask_at {n : ℕ} (i : Fin n) (b : Bool) (r : Rest n i) :
    joinMask i b r i = b := by simp [joinMask, Equiv.funSplitAt, Equiv.piSplitAt]

@[simp] theorem joinMask_away {n : ℕ} (i : Fin n) (b : Bool) (r : Rest n i)
    (j : Fin n) (hj : j ≠ i) : joinMask i b r j = r ⟨j, hj⟩ := by
  simp [joinMask, Equiv.funSplitAt, Equiv.piSplitAt, hj]

@[simp] theorem update_joinMask {n : ℕ} (i : Fin n) (b c : Bool) (r : Rest n i) :
    Function.update (joinMask i b r) i c = joinMask i c r := by
  funext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj, hj]

theorem sum_cube_split {n : ℕ} (i : Fin n) (f : Kane.Cube n → ℝ) :
    (∑ mask, f mask) = ∑ r : Rest n i, (f (joinMask i true r) + f (joinMask i false r)) := by
  calc
    _ = ∑ z : Bool × Rest n i, f ((Equiv.funSplitAt i Bool).symm z) :=
      (Equiv.sum_comp (Equiv.funSplitAt i Bool).symm f).symm
    _ = _ := by simp [Fintype.sum_prod_type, Fintype.sum_bool, Finset.sum_add_distrib, joinMask]

def weightExcept {n : ℕ} (q : ℝ) (i : Fin n) (mask : Kane.Cube n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if mask j then q else 1 - q

theorem maskWeight_eq_factor_mul_except {n : ℕ} (q : ℝ) (i : Fin n) (mask : Kane.Cube n) :
    Kane.maskWeight q mask = (if mask i then q else 1 - q) * weightExcept q i mask := by
  exact (Finset.mul_prod_erase (Finset.univ : Finset (Fin n))
    (fun j => if mask j then q else 1 - q) (Finset.mem_univ i)).symm

@[simp] theorem weightExcept_joinMask {n : ℕ} (q : ℝ) (i : Fin n)
    (b : Bool) (r : Rest n i) : weightExcept q i (joinMask i b r) =
      weightExcept q i (joinMask i false r) := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji : j ≠ i := (Finset.mem_erase.mp hj).1
  simp [joinMask_away, hji]

@[simp] theorem maskWeight_joinMask {n : ℕ} (q : ℝ) (i : Fin n)
    (b : Bool) (r : Rest n i) :
    Kane.maskWeight q (joinMask i b r) =
      (if b then q else 1 - q) * weightExcept q i (joinMask i false r) := by
  rw [maskWeight_eq_factor_mul_except q i]
  simp

/-- A coordinate contribution to the derivative of the selector mass. -/
def coordinateMassDerivative {n : ℕ} (q q' : ℝ) (i : Fin n) (mask : Kane.Cube n) : ℝ :=
  weightExcept q i mask * (if mask i then q' else -q')

/-- The derivative of the product mass with a common scalar derivative `q'`. -/
def massDerivative {n : ℕ} (q q' : ℝ) (mask : Kane.Cube n) : ℝ :=
  ∑ i, coordinateMassDerivative q q' i mask

theorem coordinate_mass_derivative_regroup {n : ℕ}
    (q q' : ℝ) (i : Fin n) (f : Kane.Cube n → ℝ) :
    (∑ mask, coordinateMassDerivative q q' i mask * f mask) =
      q' * ∑ mask, Kane.maskWeight q mask *
        (f (Function.update mask i true) - f (Function.update mask i false)) := by
  rw [sum_cube_split i]
  conv_rhs => rw [sum_cube_split i]
  simp only [coordinateMassDerivative, joinMask_at, weightExcept_joinMask,
    maskWeight_joinMask, update_joinMask, Bool.false_eq_true, ↓reduceIte]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Differentiated selector weights regroup into forced-coordinate
increments with the original product mask law. -/
theorem mass_derivative_regroup {n : ℕ} (q q' : ℝ) (f : Kane.Cube n → ℝ) :
    (∑ mask, massDerivative q q' mask * f mask) =
      q' * ∑ i, ∑ mask, Kane.maskWeight q mask *
        (f (Function.update mask i true) - f (Function.update mask i false)) := by
  unfold massDerivative
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  simp_rw [coordinate_mass_derivative_regroup]
  rw [Finset.mul_sum]

theorem coordinate_retained_amplitude_regroup {n : ℕ} (q : ℝ) (i : Fin n)
    (g : Kane.Cube n → ℝ) :
    (∑ mask, Kane.maskWeight q mask * (if mask i then g mask else 0)) =
      q * ∑ mask, Kane.maskWeight q mask * g (Function.update mask i true) := by
  rw [sum_cube_split i]
  conv_rhs => rw [sum_cube_split i]
  simp only [maskWeight_joinMask, joinMask_at, update_joinMask,
    Bool.false_eq_true, ↓reduceIte, mul_zero, add_zero]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  ring

/-- Retained-coordinate amplitude terms factor one power of the selector
probability, with that coordinate forced true in the remaining integrand. -/
theorem retained_amplitude_regroup {n : ℕ} (q : ℝ) (g : Fin n → Kane.Cube n → ℝ) :
    (∑ mask, Kane.maskWeight q mask * ∑ i, if mask i then g i mask else 0) =
      q * ∑ i, ∑ mask, Kane.maskWeight q mask * g i (Function.update mask i true) := by
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  simp_rw [coordinate_retained_amplitude_regroup]
  simp only [Finset.mul_sum]

/-- Averaging a freshly resampled selector coordinate preserves its full
product-law average. This remains a polynomial identity for every real `q`. -/
theorem conditional_coordinate_average {n : ℕ} (q : ℝ) (i : Fin n)
    (f : Kane.Cube n → ℝ) :
    (∑ mask, Kane.maskWeight q mask *
      ((1 - q) * f (Function.update mask i false) +
        q * f (Function.update mask i true))) =
      ∑ mask, Kane.maskWeight q mask * f mask := by
  rw [sum_cube_split i]
  conv_rhs => rw [sum_cube_split i]
  simp only [maskWeight_joinMask, update_joinMask, Bool.false_eq_true, ↓reduceIte]
  apply Finset.sum_congr rfl
  intro r _
  ring

end RectangleCLT.BernoulliSelectorAlgebra
