import RectangleCLTCompanion.SplitV4.Printed.ObservationTransfer
import RectangleCLTCompanion.SplitV4.Printed.OrliczClosure
import RectangleCLTCompanion.SubexponentialMain

/-! Appendix D's actual clipping and covariance-restoration argument,
using admissibility at the stated K and the CURRENT bounded theorem.
No historical final CLT is used as an analytic input. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def printedSubexponentialConstant : ℝ :=
  16+16*relativeUniversalConstant+100*subexponentialGaussianBoundaryConstant

theorem one_le_printedSubexponentialConstant : 1 ≤ printedSubexponentialConstant := by
  unfold printedSubexponentialConstant
  linarith [one_le_relativeUniversalConstant,one_le_subexponentialGaussianBoundaryConstant]

private theorem printed_rectangleError_saturate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p)
    {C r : ℝ} (hC : 1 ≤ C) (hraw : rectangleError μ W A R ≤ C*r) :
    rectangleError μ W A R ≤ C*min 1 r :=
  (le_min (rectangleError_le_one μ W A R) hraw).trans
    (min_one_le_mul_min_one hC le_rfl)

theorem subexponential_via_printed_clipping : SubexponentialCLT.{u} printedSubexponentialConstant := by
  intro Ω _ μ _ p n hp hn X K A h hunit hA R
  let b := subexponentialScale n K
  let L := dimensionLog p
  have hbpos : 0 < b := subexponentialScale_pos hn h.one_le_scale
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  have hC := one_le_printedSubexponentialConstant
  apply printed_rectangleError_saturate μ (normalizedObservationSum X) A R hC
  by_cases hb : b < 1 / 16
  · let u := 4 * dimensionLog n
    let ξ := normalizedClippedRows μ X (K * u)
    let W := sumVector ξ
    let d : Vector p := fun j => Real.sqrt (covariance μ W j j)
    have hu : 0 ≤ u := mul_nonneg (by norm_num)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hn))
    have hcut : 0 ≤ K * u := mul_nonneg hK hu
    have hδ : 2 * (K * u) / Real.sqrt (n : ℝ) = 8 * b := by
      dsimp [u, b, subexponentialScale]
      ring
    have hbounded : BoundedIndependentHypotheses μ ξ (8 * b) := by
      rw [← hδ]
      exact normalizedClippedRows_boundedHypotheses h.measurable h.independent hcut
    obtain ⟨AT, hAT⟩ := gaussian_factor_exists_of_boundedIndependent hbounded
    have he : -(4 * dimensionLog n) / 2 = -2 * dimensionLog n := by ring
    have hsmall : 2 * K * Real.exp (-u / 2) ≤ 1 / 2 := by
      simpa only [u, he, subexponentialResidualSD, subexponentialTailFactor] using
        subexponentialResidualSD_le_half hn hK hb
    have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j :=
      clipped_standardDeviation_ge_half h hu hn hunit hsmall j
    have hvar (j : Fin p) : covariance μ W j j = d j ^ 2 := by
      have hnonneg : 0 ≤ covariance μ W j j := by
        rw [← hAT, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun k _ => by
          simpa only [Matrix.transpose_apply, ← pow_two] using sq_nonneg (AT j k))
      exact (Real.sq_sqrt hnonneg).symm
    have hcompare (S : Rect p) : rectangleError μ W AT S ≤
        (16 * relativeUniversalConstant) * unrestrictedRate b L := by
      have hc := bounded_after_standardization_via_current_theorem hbounded hp d hd hvar AT hAT S
      rw [show 2 * (8 * b) = 16 * b by ring] at hc
      have h16 := unrestrictedRate_mul_le (by norm_num : (1 : ℝ) ≤ 16) hbpos hLp
      have hmin : min 1 (unrestrictedRate (16 * b) L) ≤ 16 * unrestrictedRate b L :=
        (min_le_right _ _).trans h16
      have hcK : 0 ≤ relativeUniversalConstant := by
        exact zero_le_one.trans one_le_relativeUniversalConstant
      have hh := hc.trans (mul_le_mul_of_nonneg_left hmin hcK)
      convert hh using 1 <;> dsimp only [L] <;> ring
    have ht := subexponential_clipping_reduction h hp hn hunit A AT hA hAT hcompare R
    have ht' : rectangleError μ (normalizedObservationSum X) A R ≤
        (16 * relativeUniversalConstant) * unrestrictedRate b L +
        subexponentialGaussianBoundaryConstant *
          (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
          Real.sqrt L + 1 / (n : ℝ) := by
      simpa only [residualCouplingRadius, gaussianCouplingRadius,
        subexponentialResidualRadius, subexponentialGaussianRadius,
        subexponentialResidualSD, subexponentialTailFactor, subexponentialUnionLog,
        subexponentialGaussianBoundaryConstant, he, L] using ht
    have htransfer := subexponential_transfer_error_weighted_le hn hp h.one_le_scale
      one_le_subexponentialGaussianBoundaryConstant
    have hbase := unrestricted_base_le_rate hbpos.le hLp.le
    have hrate : 0 ≤ unrestrictedRate b L := unrestrictedRate_nonneg hbpos.le hLp.le
    have hG : 0 ≤ subexponentialGaussianBoundaryConstant :=
      zero_le_one.trans one_le_subexponentialGaussianBoundaryConstant
    have hscaled := mul_le_mul_of_nonneg_left hbase (show
      0 ≤ 100 * subexponentialGaussianBoundaryConstant by positivity)
    change _ ≤ (16 * relativeUniversalConstant) * unrestrictedRate b L +
      subexponentialGaussianBoundaryConstant *
        (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt L + 1 / (n : ℝ) at ht'
    change subexponentialGaussianBoundaryConstant *
        (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt L + 1 / (n : ℝ) ≤
      (100 * subexponentialGaussianBoundaryConstant) * b * L ^ (3 / 2 : ℝ) at htransfer
    unfold printedSubexponentialConstant
    nlinarith
  · have hblo : (1 / 16 : ℝ) ≤ b := le_of_not_gt hb
    have hbase := base_le_unrestrictedRate hbpos.le hL
    have hC16 : 16 ≤ printedSubexponentialConstant := by
      unfold printedSubexponentialConstant
      linarith [one_le_relativeUniversalConstant, one_le_subexponentialGaussianBoundaryConstant]
    have h16 : 1 ≤ 16 * unrestrictedRate b L := by nlinarith
    exact (rectangleError_le_one μ (normalizedObservationSum X) A R).trans
      (h16.trans (mul_le_mul_of_nonneg_right hC16
        (unrestrictedRate_nonneg hbpos.le hLp.le)))

/-- Corollary 2 through its printed closure-at-K, clipping, standardization,
current-Theorem-1 application and joint-covariance restoration chain. -/
theorem orlicz_transfer_via_printed_clipping
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1/(n : ℝ))*(∑ i, ∫ ω, X i ω j^2 ∂μ)=1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      printedSubexponentialConstant*min 1
        (unrestrictedRate (subexponentialScale n K) (dimensionLog p)) := by
  have he := psi1_hypotheses_exponential_at_same_scale h
  exact rectangleDistance_le μ (normalizedObservationSum X) A
    (subexponential_via_printed_clipping μ p n hp hn X K A
      he (normalizedObservationSum_unit_diagonal_of_average_secondMoments he haverage) hA)

end
end RectangleCLT.Companion.SplitV4.Printed
