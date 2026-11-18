import RectangleCLTArxivV1.SupplementalGComplementary
import RectangleCLTArxivV1.SupplementalGCapOptimization
import RectangleCLTArxivV1.IntrinsicComparison

/- Actual seeded interpolation will supply the fourth-term majorant below.
The scalar FTC reductions keep that analytic obligation visible. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section

def capMinimumMajorant (A S B C v : ℝ) : ℝ :=
  min (C * A / v) (C * (min (A / v) (S / (v * Real.sqrt v)) + min (A / v) (B / Real.sqrt v)))

theorem capMinimumMajorant_nonneg {A S B C v : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hB : 0 ≤ B) (hC : 0 ≤ C) (hv : 0 < v) :
    0 ≤ capMinimumMajorant A S B C v := by
  unfold capMinimumMajorant
  positivity

theorem capMinimumMajorant_continuousOn {a b A S B C : ℝ} (ha : 0 < a) :
    ContinuousOn (capMinimumMajorant A S B C) (Icc a b) := by
  exact (cap_const_inv_continuousOn ha (C * A)).inf
    (continuousOn_const.mul (((cap_const_inv_continuousOn ha A).inf
      (cap_const_inv_mul_sqrt_continuousOn ha S)).add
        ((cap_const_inv_continuousOn ha A).inf (cap_const_inv_sqrt_continuousOn ha B))))

theorem cap_abs_le_split_min {x A S B C : ℝ}
    (hA : 0 ≤ A) (hS : 0 ≤ S) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hdir : |x| ≤ C * A) (hcomp : |x| ≤ C * (S + B)) :
    |x| ≤ C * (min A S + min A B) := by
  by_cases hAS : A ≤ S
  · rw [min_eq_left hAS]
    exact hdir.trans (by nlinarith [mul_nonneg hC (le_min hA hB)])
  · rw [min_eq_right (le_of_not_ge hAS)]
    by_cases hAB : A ≤ B
    · rw [min_eq_left hAB]
      exact hdir.trans (by nlinarith [mul_nonneg hC hS])
    · simpa only [min_eq_right (le_of_not_ge hAB)] using hcomp

theorem cap_integral_majorant_bound {ε A S B C L : ℝ}
    (hε : 0 < ε) (hεsmall : ε ≤ 1 / 4) (hA : 0 < A) (hS : 0 < S) (hB : 0 < B)
    (hC : 0 ≤ C) (hL : 1 ≤ L)
    (hlogS : max (Real.log (S / (A * Real.sqrt ε))) 0 ≤ 4 * L)
    (hlogB : max (Real.log (B / A)) 0 ≤ 6 * L) :
    (∫ t in (0 : ℝ)..1, capMinimumMajorant A S B C (t + ε)) ≤
      38 * C * A * min (1 + Real.log (1 / ε)) L := by
  have hab : ε ≤ 1 + ε := by linarith
  have hi : IntervalIntegrable (capMinimumMajorant A S B C) volume ε (1 + ε) :=
    (capMinimumMajorant_continuousOn hε).intervalIntegrable_of_Icc hab
  have hm (v : ℝ) (hv : v ∈ Ioo ε (1 + ε)) : 0 ≤ capMinimumMajorant A S B C v :=
    capMinimumMajorant_nonneg hA.le hS.le hB.le hC (hε.trans hv.1)
  have h := cap_integrated_remainder_min_bound hε hεsmall hA hS hB hC hL hlogS hlogB hi
    (fun v hv => by rw [abs_of_nonneg (hm v hv)]; exact min_le_right _ _)
    (fun v hv => by rw [abs_of_nonneg (hm v hv)]; exact min_le_left _ _)
  rw [intervalIntegral.integral_comp_add_right, zero_add]
  exact (intervalIntegral.integral_mono_on hab hi hi.abs (fun v _ => le_abs_self _)).trans h

/-- FTC with an integrable majorant does not require an integrability
premise for the derivative itself. -/
theorem cap_time_increment_le {P D M : ℝ → ℝ} {a : ℝ}
    (hP : ContinuousOn P (Icc (0 : ℝ) 1))
    (hD : ∀ t ∈ Ioo (0 : ℝ) 1, HasDerivAt P (D t) t)
    (hM : ContinuousOn M (Icc (0 : ℝ) 1))
    (hbound : ∀ t ∈ Ioo (0 : ℝ) 1, |D t| ≤ a + M t) :
    |P 1 - P 0| ≤ a + ∫ t in (0 : ℝ)..1, M t := by
  have hc : ContinuousOn (fun t => a + M t) (Icc (0 : ℝ) 1) := continuousOn_const.add hM
  have hi : IntegrableOn (fun t => a + M t) (Icc (0 : ℝ) 1) := hc.integrableOn_compact isCompact_Icc
  have hp := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hP (fun t ht => (hD t ht).hasDerivWithinAt) hi
    (fun t ht => (le_abs_self _).trans (hbound t ht))
  have hn := intervalIntegral.sub_le_integral_of_hasDeriv_right_of_le (by norm_num : (0 : ℝ) ≤ 1)
    hP.neg (fun t ht => (hD t ht).neg.hasDerivWithinAt) hi
    (fun t ht => (neg_le_abs _).trans (hbound t ht))
  have heq : (∫ t in (0 : ℝ)..1, a + M t) = a + ∫ t in (0 : ℝ)..1, M t := by
    rw [intervalIntegral.integral_add (intervalIntegrable_const)
      (hM.intervalIntegrable_of_Icc (by norm_num))]
    simp
  rw [heq] at hp hn
  exact abs_le.2 ⟨by linarith, hp⟩

end
end RectangleCLTArxivV1
