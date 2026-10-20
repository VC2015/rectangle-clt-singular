import Kane.Base
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.BigOperators

/-! Uniform finite averages and the exponential moment of an oriented cube sum. -/

open scoped BigOperators

namespace Kane

section Averages

variable {α : Type*} [Fintype α]

theorem avg_congr {f g : α → ℝ} (h : ∀ x, f x = g x) : avg f = avg g := by
  unfold avg
  congr 1
  exact Finset.sum_congr rfl (fun x _ => h x)

@[simp] theorem avg_const [Nonempty α] (c : ℝ) : avg (fun _ : α => c) = c := by
  have hc : (Fintype.card α : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := α))
  simp only [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]

@[simp] theorem avg_zero : avg (fun _ : α => (0 : ℝ)) = 0 := by simp [avg]

theorem avg_add (f g : α → ℝ) : avg (fun x => f x + g x) = avg f + avg g := by
  simp only [avg, Finset.sum_add_distrib, mul_add]

theorem avg_sub (f g : α → ℝ) : avg (fun x => f x - g x) = avg f - avg g := by
  simp only [avg, Finset.sum_sub_distrib, mul_sub]

theorem avg_neg (f : α → ℝ) : avg (fun x => -f x) = -avg f := by
  simp [avg]

theorem avg_const_mul (c : ℝ) (f : α → ℝ) :
    avg (fun x => c * f x) = c * avg f := by
  simp only [avg, ← Finset.mul_sum]
  ring

theorem avg_mul_const (f : α → ℝ) (c : ℝ) :
    avg (fun x => f x * c) = avg f * c := by
  simp only [avg, ← Finset.sum_mul]
  ring

theorem avg_sum {ι : Type*} [Fintype ι] (f : ι → α → ℝ) :
    avg (fun x => ∑ i, f i x) = ∑ i, avg (f i) := by
  simp only [avg, Finset.mul_sum]
  exact Finset.sum_comm

theorem avg_mono {f g : α → ℝ} (h : ∀ x, f x ≤ g x) : avg f ≤ avg g := by
  unfold avg
  exact mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun x _ => h x)
    (inv_nonneg.mpr (Nat.cast_nonneg _))

theorem avg_nonneg {f : α → ℝ} (h : ∀ x, 0 ≤ f x) : 0 ≤ avg f := by
  simpa only [avg_zero] using avg_mono h

end Averages

@[simp] theorem flip_flip {n : ℕ} (x : Cube n) (i : Fin n) :
    flip (flip x i) i = x := by
  funext j
  by_cases h : j = i
  · subst j
    simp [flip]
  · simp [flip, h]

theorem avg_flip {n : ℕ} (f : Cube n → ℝ) (i : Fin n) :
    avg (fun x => f (flip x i)) = avg f := by
  let e : Cube n ≃ Cube n :=
    { toFun := fun x => flip x i
      invFun := fun x => flip x i
      left_inv := fun x => flip_flip x i
      right_inv := fun x => flip_flip x i }
  unfold avg
  congr 1
  exact e.sum_comp f

@[simp] theorem signedCoord_flip_self {n : ℕ} (s x : Cube n) (i : Fin n) :
    signedCoord s (flip x i) i = -signedCoord s x i := by
  cases hs : s i <;> cases hx : x i <;> simp [signedCoord, flip, hs, hx]

theorem avg_exp_signedSum {n : ℕ} (s : Cube n) (t : ℝ) :
    avg (fun x => Real.exp (t * signedSum s x)) = Real.cosh t ^ n := by
  have hfactor : (∑ x : Cube n, Real.exp (t * signedSum s x)) =
      ∏ i : Fin n, ∑ b : Bool,
        Real.exp (t * (if b = s i then (1 : ℝ) else -1)) := by
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro x _
    simp [signedSum, signedCoord, Finset.mul_sum, Real.exp_sum]
  have hcoord (i : Fin n) : (∑ b : Bool,
      Real.exp (t * (if b = s i then (1 : ℝ) else -1))) = 2 * Real.cosh t := by
    rw [Fintype.sum_bool, Real.cosh_eq]
    cases hs : s i <;> simp [hs] <;> ring
  simp_rw [hcoord] at hfactor
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hfactor
  unfold avg
  rw [hfactor]
  have hcard : Fintype.card (Cube n) = 2 ^ n := by simp [Cube, Fintype.card_fun]
  rw [hcard]
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [← inv_pow, ← mul_pow]
  congr 1
  ring

theorem avg_exp_signedSum_le {n : ℕ} (s : Cube n) (t : ℝ) :
    avg (fun x => Real.exp (t * signedSum s x)) ≤ Real.exp ((n : ℝ) * t ^ 2 / 2) := by
  rw [avg_exp_signedSum]
  calc
    Real.cosh t ^ n ≤ Real.exp (t ^ 2 / 2) ^ n := by
      exact pow_le_pow_left₀ (Real.cosh_pos t).le (Real.cosh_le_exp_half_sq t) n
    _ = Real.exp ((n : ℝ) * t ^ 2 / 2) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

end Kane
