import RectangleCLT.LocalMoments
import RectangleCLT.TruncationTailMoments

/-! The third-moment tensor after truncation is controlled by the square
root of the coordinate fourth-moment sum, using the actual unit coordinate
variances and independence of the observations. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.BoundedIndependentHypotheses

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {ξ : Fin n → Ω → Vector p} {δ : ℝ}

/-- Fourth-moment control of the aggregate signed third tensor.  The
absolute value is taken after summing, as in the paper's definition. -/
theorem gamma3_le_sqrt_gamma4 (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) :
    gamma3 μ ξ ≤ Real.sqrt (gamma4 μ ξ) := by
  have hpow (i : Fin n) (j : Fin p) (m : ℕ) :=
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j m
  have hcoord (j : Fin p) :
      (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ gamma4 μ ξ := by
    exact (Finset.le_fold_max (0 : ℝ)).mpr
      (Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩)
  have htriple (j k l : Fin p) :
      |∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ| ≤ Real.sqrt (gamma4 μ ξ) := by
    have hpoint (a b : ℝ) : (a * b) ^ 2 ≤ (a ^ 4 + b ^ 4) / 2 := by
      nlinarith [sq_nonneg (a ^ 2 - b ^ 2)]
    have hg (i : Fin n) : Integrable (fun ω => (ξ i ω k * ξ i ω l) ^ 2) μ := by
      apply (((hpow i k 4).add (hpow i l 4)).div_const 2).mono'
        (((((measurable_pi_apply k).comp (h.measurable i)).mul
          ((measurable_pi_apply l).comp (h.measurable i))).pow_const 2).aestronglyMeasurable)
      exact ae_of_all _ fun ω => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)] using
          hpoint (ξ i ω k) (ξ i ω l)
    have hfg (i : Fin n) :
        Integrable (fun ω => ξ i ω j * (ξ i ω k * ξ i ω l)) μ := by
      simpa only [mul_assoc] using
        integrable_coordinate_triple_of_bounded h.measurable h.abs_coordinate_le
          h.delta_nonneg i j k l
    have hC := sum_integral_product_sq_le
      (f := fun i ω => ξ i ω j) (g := fun i ω => ξ i ω k * ξ i ω l)
      (fun i => hpow i j 2) hg hfg
    rw [h.coordinate_second_moments hunit j, one_mul] at hC
    have hprod (i : Fin n) : (∫ ω, (ξ i ω k * ξ i ω l) ^ 2 ∂μ) ≤
        ((∫ ω, ξ i ω k ^ 4 ∂μ) + (∫ ω, ξ i ω l ^ 4 ∂μ)) / 2 := by
      calc
        _ ≤ ∫ ω, (ξ i ω k ^ 4 + ξ i ω l ^ 4) / 2 ∂μ :=
          integral_mono (hg i) (((hpow i k 4).add (hpow i l 4)).div_const 2)
            fun ω => hpoint _ _
        _ = _ := by rw [integral_div, integral_add (hpow i k 4) (hpow i l 4)]
    have hsum : (∑ i, ∫ ω, (ξ i ω k * ξ i ω l) ^ 2 ∂μ) ≤ gamma4 μ ξ := by
      calc
        _ ≤ ∑ i, ((∫ ω, ξ i ω k ^ 4 ∂μ) + (∫ ω, ξ i ω l ^ 4 ∂μ)) / 2 :=
          Finset.sum_le_sum fun i _ => hprod i
        _ = ((∑ i, ∫ ω, ξ i ω k ^ 4 ∂μ) +
            (∑ i, ∫ ω, ξ i ω l ^ 4 ∂μ)) / 2 := by
          rw [← Finset.sum_div, Finset.sum_add_distrib]
        _ ≤ gamma4 μ ξ := by linarith [hcoord k, hcoord l]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt (gamma4_nonneg μ ξ)]
    simpa only [mul_assoc] using hC.trans hsum
  unfold gamma3
  apply (Finset.fold_max_le _).mpr
  exact ⟨Real.sqrt_nonneg _, fun jkl _ => htriple jkl.1 jkl.2.1 jkl.2.2⟩

end RectangleCLT.BoundedIndependentHypotheses
