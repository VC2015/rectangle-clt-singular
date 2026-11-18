import RectangleCLTArxivV1.SupplementalHSelectorReductions
import RectangleCLTCompanion.SplitV4.Printed.CovariancePotential
import Mathlib.Analysis.MeanInequalities

/-! Actual positive and negative directional weights in H's cubic
matrix estimate. Their vanishing halfspaces require multiplicative
log-concavity, rather than a globally defined logarithm. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHPositiveDirection {r : ℕ} (u g : Vector r) : ℝ := max (faceDot u g) 0

theorem supplementalHPositiveDirection_nonneg {r : ℕ} (u g : Vector r) :
    0 ≤ supplementalHPositiveDirection u g := le_max_right _ _

theorem supplementalH_nonnegative_logConcave_mul {r : ℕ}
    (w z : Vector r → ℝ) (hw : ∀ x, 0 ≤ w x) (hz : ∀ x, 0 ≤ z x)
    (hwlog : Printed.NonnegativeLogConcave w) (hzlog : Printed.NonnegativeLogConcave z) :
    Printed.NonnegativeLogConcave (fun x => w x*z x) := by
  intro x y t ht ht1
  rw [Real.mul_rpow (hw x) (hz x), Real.mul_rpow (hw y) (hz y)]
  calc
    _ = (w x^(1-t)*w y^t)*(z x^(1-t)*z y^t) := by ring
    _ ≤ _ := mul_le_mul (hwlog x y t ht ht1) (hzlog x y t ht ht1)
      (mul_nonneg (Real.rpow_nonneg (hz x) _) (Real.rpow_nonneg (hz y) _)) (hw _)

/-- The positive part of any actual linear Gaussian coordinate is
log-concave, with its zero halfspace retained exactly. -/
theorem supplementalHPositiveDirection_logConcave {r : ℕ} (u : Vector r) :
    Printed.NonnegativeLogConcave (supplementalHPositiveDirection u) := by
  intro x y t ht ht1
  have htm : 0 < 1-t := by linarith
  by_cases hx : 0 < faceDot u x
  · by_cases hy : 0 < faceDot u y
    · have hm : faceDot u ((1-t) • x+t • y) = (1-t)*faceDot u x+t*faceDot u y := by
        simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
          mul_add, Finset.sum_add_distrib]
        simp_rw [mul_left_comm (u _) _ _]
        rw [← Finset.mul_sum, ← Finset.mul_sum]
      simp only [supplementalHPositiveDirection, max_eq_left hx.le, max_eq_left hy.le]
      exact (Real.geom_mean_le_arith_mean2_weighted htm.le ht.le hx.le hy.le (by ring)).trans
        (by rw [← hm]; exact le_max_left _ _)
    · have hy0 : supplementalHPositiveDirection u y = 0 := max_eq_right (le_of_not_gt hy)
      rw [hy0, Real.zero_rpow ht.ne', mul_zero]
      exact supplementalHPositiveDirection_nonneg _ _
  · have hx0 : supplementalHPositiveDirection u x = 0 := max_eq_right (le_of_not_gt hx)
    rw [hx0, Real.zero_rpow htm.ne', zero_mul]
    exact supplementalHPositiveDirection_nonneg _ _

/-- Every number of additional selector factors is allowed. -/
theorem supplementalH_positive_selector_logConcave {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (ha : ∀ i, α i ∈ s.faces) (u : Vector r) :
    Printed.NonnegativeLogConcave (fun g => supplementalHPositiveDirection u g*
      selectorWeight s α (A.mulVec g+v)) := by
  have hs : Printed.NonnegativeLogConcave (fun g => selectorWeight s α (A.mulVec g+v)) :=
    Printed.nonnegativeLogConcave_of_concave_log _ (fun g => selectorWeight_pos s α ha _)
      (concaveOn_log_selectorWeight_affine s α ha A v)
  exact supplementalH_nonnegative_logConcave_mul _ _
    (supplementalHPositiveDirection_nonneg u) (fun g => selectorWeight_nonneg s α _)
    (supplementalHPositiveDirection_logConcave u) hs

/-- Difference and sum of the two signed halfspace factors. -/
theorem supplementalHPositiveDirection_sub {r : ℕ} (u g : Vector r) :
    supplementalHPositiveDirection u g-supplementalHPositiveDirection (-u) g=faceDot u g := by
  have he : faceDot (-u) g = -faceDot u g := by
    simp [faceDot, Finset.sum_neg_distrib]
  unfold supplementalHPositiveDirection
  rw [he]
  rcases le_total (faceDot u g) 0 with h | h
  · rw [max_eq_right h,max_eq_left (by linarith)]
    ring
  · rw [max_eq_left h,max_eq_right (by linarith)]
    ring

theorem supplementalHPositiveDirection_add {r : ℕ} (u g : Vector r) :
    supplementalHPositiveDirection u g+supplementalHPositiveDirection (-u) g=|faceDot u g| := by
  have he : faceDot (-u) g = -faceDot u g := by
    simp [faceDot, Finset.sum_neg_distrib]
  unfold supplementalHPositiveDirection
  rw [he]
  rcases le_total (faceDot u g) 0 with h | h
  · rw [max_eq_right h,max_eq_left (by linarith),abs_of_nonpos h]
    ring
  · rw [max_eq_left h,max_eq_right (by linarith),abs_of_nonneg h]
    ring

end
end RectangleCLTArxivV1
