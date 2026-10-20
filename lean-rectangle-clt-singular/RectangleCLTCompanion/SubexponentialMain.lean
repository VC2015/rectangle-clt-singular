import RectangleCLTCompanion.SubexponentialBounded
import RectangleCLTCompanion.SubexponentialReduction
import RectangleCLTCompanion.SubexponentialScales
import RectangleCLTCompanion.SubexponentialGap
import RectangleCLTCompanion.SubexponentialOrlicz
import RectangleCLTCompanion.FactorExistence

/-! Complete sub-exponential upper bounds. All clipping, concentration,
covariance-restoration and rectangle-transfer estimates are proved from
the actual observation hypotheses before the bounded theorem is applied. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

def subexponentialGaussianBoundaryConstant : ℝ := 12 * Real.exp (3 / 2 : ℝ)

theorem one_le_subexponentialGaussianBoundaryConstant :
    1 ≤ subexponentialGaussianBoundaryConstant := by
  have h := Real.one_le_exp (by norm_num : (0 : ℝ) ≤ 3 / 2)
  unfold subexponentialGaussianBoundaryConstant
  linarith

/-- One constant for the unrestricted exponential-moment theorem. -/
def subexponentialUniversalConstant : ℝ :=
  16 + 32 * companionUniversalConstant + 100 * subexponentialGaussianBoundaryConstant

theorem one_le_subexponentialUniversalConstant : 1 ≤ subexponentialUniversalConstant := by
  unfold subexponentialUniversalConstant
  linarith [one_le_companionUniversalConstant, one_le_subexponentialGaussianBoundaryConstant]

theorem unrestricted_base_le_rate {b L : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L) :
    b * L ^ (3 / 2 : ℝ) ≤ unrestrictedRate b L := by
  exact le_mul_of_one_le_right (mul_nonneg hb (Real.rpow_nonneg hL _))
    (Real.one_le_sqrt.mpr (one_le_D_L b L))

theorem fixedGap_base_le_rate {b L : ℝ} (hb : 0 ≤ b) (hL : 0 ≤ L) :
    b * L ^ (3 / 2 : ℝ) ≤ fixedGapSubexponentialRate b L := by
  unfold fixedGapSubexponentialRate
  nlinarith [mul_nonneg hb (mul_nonneg hL
    (Real.sqrt_nonneg (1 + logPlus (1 / (b * L)))))]

private theorem rectangleError_saturate
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p)
    {C r : ℝ} (hC : 1 ≤ C) (hraw : rectangleError μ W A R ≤ C * r) :
    rectangleError μ W A R ≤ C * min 1 r :=
  (le_min (rectangleError_le_one μ W A R) hraw).trans
    (min_one_le_mul_min_one hC le_rfl)

/-- The unrestricted tail bound under genuine coordinate exponential
moments. The constant has no dependence on dimensions or covariance. -/
theorem subexponentialCLT : SubexponentialCLT.{u} subexponentialUniversalConstant := by
  intro Ω _ μ _ p n hp hn X K A h hunit hA R
  let b := subexponentialScale n K
  let L := dimensionLog p
  have hbpos : 0 < b := subexponentialScale_pos hn h.one_le_scale
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  have hC := one_le_subexponentialUniversalConstant
  apply rectangleError_saturate μ (normalizedObservationSum X) A R hC
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
        (32 * companionUniversalConstant) * unrestrictedRate b L := by
      have hc := bounded_unrestrictedCLT_after_standardization hbounded hp hn d hd hvar AT hAT S
      rw [show 2 * (8 * b) = 16 * b by ring] at hc
      have h16 := unrestrictedRate_mul_le (by norm_num : (1 : ℝ) ≤ 16) hbpos hLp
      have hmin : min 1 (unrestrictedRate (16 * b) L) ≤ 16 * unrestrictedRate b L :=
        (min_le_right _ _).trans h16
      have hcK : 0 ≤ 2 * companionUniversalConstant := by
        linarith [one_le_companionUniversalConstant]
      have hh := hc.trans (mul_le_mul_of_nonneg_left hmin hcK)
      convert hh using 1 <;> dsimp only [L] <;> ring
    have ht := subexponential_clipping_reduction h hp hn hunit A AT hA hAT hcompare R
    have ht' : rectangleError μ (normalizedObservationSum X) A R ≤
        (32 * companionUniversalConstant) * unrestrictedRate b L +
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
    change _ ≤ (32 * companionUniversalConstant) * unrestrictedRate b L +
      subexponentialGaussianBoundaryConstant *
        (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt L + 1 / (n : ℝ) at ht'
    change subexponentialGaussianBoundaryConstant *
        (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt L + 1 / (n : ℝ) ≤
      (100 * subexponentialGaussianBoundaryConstant) * b * L ^ (3 / 2 : ℝ) at htransfer
    unfold subexponentialUniversalConstant
    nlinarith
  · have hblo : (1 / 16 : ℝ) ≤ b := le_of_not_gt hb
    have hbase := base_le_unrestrictedRate hbpos.le hL
    have hC16 : 16 ≤ subexponentialUniversalConstant := by
      unfold subexponentialUniversalConstant
      linarith [one_le_companionUniversalConstant, one_le_subexponentialGaussianBoundaryConstant]
    have h16 : 1 ≤ 16 * unrestrictedRate b L := by nlinarith
    exact (rectangleError_le_one μ (normalizedObservationSum X) A R).trans
      (h16.trans (mul_le_mul_of_nonneg_right hC16
        (unrestrictedRate_nonneg hbpos.le hLp.le)))

end
end RectangleCLT.Companion
