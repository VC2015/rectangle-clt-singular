import RectangleCLTArxivV1.SubexponentialIntrinsicWidth
import RectangleCLTArxivV1.SubexponentialIntrinsicReduction
import RectangleCLTArxivV1.TransfersBounded
import RectangleCLTArxivV1.SubexponentialIntrinsicOrlicz
import RectangleCLTCompanion.SubexponentialScales

/-! Corollary 2 with the actual Gaussian width. The universal coefficient is
chosen before the dimensions, probability space, observations, and covariance. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators
noncomputable section
universe u

def subexponentialWidthRate (n p : ℕ) (K g : ℝ) : ℝ :=
  subexponentialScale n K * g * dimensionLog p *
    Real.sqrt (D_L (subexponentialScale n K) (dimensionLog p))

def subexponentialWidthConstant : ℝ :=
  32 * intrinsicUniversalConstant + 200 * max 1 (1 / Real.sqrt (2 / Real.pi))

theorem one_le_subexponentialWidthConstant : 1 ≤ subexponentialWidthConstant := by
  have h := intrinsicUniversalConstant_pos
  have hK : 1 ≤ max 1 (1 / Real.sqrt (2 / Real.pi)) := le_max_left _ _
  unfold subexponentialWidthConstant
  linarith

theorem subexponentialCLT_intrinsic
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤ subexponentialWidthConstant *
      min 1 (subexponentialWidthRate n p K (gaussianMaximumMean A)) := by
  let b := subexponentialScale n K
  let L := dimensionLog p
  let g := gaussianMaximumMean A
  let R := subexponentialWidthRate n p K g
  let κ := max 1 (1 / Real.sqrt (2 / Real.pi))
  have hbpos : 0 < b := subexponentialScale_pos hn h.one_le_scale
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hg : 0 ≤ g := gaussianMaximumMean_nonneg A
  have hκ : 1 ≤ κ := le_max_left _ _
  have hdiag (j : Fin p) : (A*A.transpose) j j = 1 := by rw [hA,hunit j]
  have hglow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
  have hk : 0 < Real.sqrt (2 / Real.pi) := by positivity
  have hκg : 1 ≤ κ*g := by
    have hh := mul_le_mul_of_nonneg_left hglow (one_div_nonneg.mpr hk.le)
    rw [one_div_mul_cancel hk.ne'] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hg)
  have hD : 1 ≤ Real.sqrt (D_L b L) := Real.one_le_sqrt.mpr (one_le_D_L b L)
  have hbase : b*g ≤ R := by
    change b*g ≤ b*g*L*Real.sqrt (D_L b L)
    exact (le_mul_of_one_le_right (mul_nonneg hbpos.le hg) hL1).trans
      (le_mul_of_one_le_right (by positivity) hD)
  have hR : 0 ≤ R := (mul_nonneg hbpos.le hg).trans hbase
  have hC : 1 ≤ subexponentialWidthConstant := one_le_subexponentialWidthConstant
  have hraw : rectangleDistance μ (normalizedObservationSum X) A ≤
      subexponentialWidthConstant * R := by
    by_cases hb : b < 1/16
    · let u := 4 * dimensionLog n
      let ξ := normalizedClippedRows μ X (K*u)
      let W := sumVector ξ
      let d : Vector p := fun j => Real.sqrt (covariance μ W j j)
      have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
      have hu : 0 ≤ u := mul_nonneg (by norm_num)
        (zero_le_one.trans (log_exp_mul_nat_ge_one hn))
      have hδ : 2*(K*u)/Real.sqrt (n:ℝ) = 8*b := by dsimp [u,b,subexponentialScale]; ring
      have hbnd : BoundedIndependentHypotheses μ ξ (8*b) := by
        rw [←hδ]
        exact normalizedClippedRows_boundedHypotheses h.measurable h.independent (mul_nonneg hK hu)
      obtain ⟨AT,hAT⟩ := gaussian_factor_exists_of_boundedIndependent hbnd
      have he : -(4 * dimensionLog n)/2 = -2 * dimensionLog n := by ring
      have hsmall : 2*K*Real.exp (-u/2) ≤ 1/2 := by
        simpa only [u,he,subexponentialResidualSD,subexponentialTailFactor] using
          subexponentialResidualSD_le_half hn hK hb
      have hd (j : Fin p) : (1/2:ℝ) ≤ d j :=
        clipped_standardDeviation_ge_half h hu hn hunit hsmall j
      have hvar (j : Fin p) : covariance μ W j j = (d j)^2 := by
        have hn0 : 0 ≤ covariance μ W j j := by
          rw [←hAT,Matrix.mul_apply]
          exact Finset.sum_nonneg fun k _ => by
            simpa only [Matrix.transpose_apply,←pow_two] using sq_nonneg (AT j k)
        exact (Real.sq_sqrt hn0).symm
      have hwidth : gaussianMaximumMean AT ≤ g := gaussianMaximumMean_clipped_le h hu A AT hA hAT
      have hcompare (S : Rect p) : rectangleError μ W AT S ≤
          (32*intrinsicUniversalConstant)*R := by
        have hc := (rectangleError_le_rectangleDistance μ W AT S).trans
          (intrinsicEnvelopeCLT_after_standardization μ ξ hbnd hp d hd hvar AT hAT)
        have hD16 := Real.sqrt_le_sqrt (D_L_mul_le (by norm_num : (1:ℝ) ≤ 16) hbpos hL)
        have hrr : 4*(8*b*gaussianMaximumMean AT*L*Real.sqrt (D_L (2*(8*b)) L)) ≤ 32*R := by
          have hh := mul_le_mul hwidth hD16 (Real.sqrt_nonneg _) hg
          have hh' := mul_le_mul_of_nonneg_left hh (show 0 ≤ 32*b*L by positivity)
          convert hh' using 1 <;> dsimp only [R,subexponentialWidthRate,b,L,g] <;> ring
        have hc' := hc.trans (mul_le_mul_of_nonneg_left (min_le_right (1:ℝ) _) intrinsicUniversalConstant_pos.le)
        exact hc'.trans (by nlinarith [mul_le_mul_of_nonneg_left hrr intrinsicUniversalConstant_pos.le])
      apply rectangleDistance_le
      intro S
      have ht := subexponential_clipping_reduction_intrinsic h hp hn hunit A AT hA hAT hcompare S
      have ht' : rectangleError μ (normalizedObservationSum X) A S ≤
          (32*intrinsicUniversalConstant)*R +
          2*(printedResidualRadius n p K + subexponentialGaussianRadius n p K)*g+1/(n:ℝ) := by
        simpa only [residualCouplingRadius,gaussianCouplingRadius,subexponentialResidualRadius,
          subexponentialGaussianRadius,subexponentialResidualSD,subexponentialTailFactor,
          subexponentialUnionLog,he,g] using ht
      have hradii : printedResidualRadius n p K+subexponentialGaussianRadius n p K ≤ 58*b*L :=
        (add_le_add_right (printedResidualRadius_le_archive hn hp hK) _).trans
          (subexponential_radii_le hn hp hK)
      have hrad := mul_le_mul_of_nonneg_right hradii (show 0 ≤ 2*g by positivity)
      have hprob : 1/(n:ℝ) ≤ b := by
        exact (div_le_div_of_nonneg_right h.one_le_scale (Nat.cast_nonneg n)).trans
          (quotient_le_subexponentialScale hn hK)
      have hbR : b ≤ κ*R := by
        have hh := mul_le_mul_of_nonneg_left hκg hbpos.le
        have hh' := mul_le_mul_of_nonneg_left hbase (show 0 ≤ κ by positivity)
        nlinarith
      have hbr : b*g*L ≤ R := by
        change b*g*L ≤ b*g*L*Real.sqrt (D_L b L)
        exact le_mul_of_one_le_right (by positivity) hD
      have hrr : 2*(printedResidualRadius n p K+subexponentialGaussianRadius n p K)*g ≤ 116*R := by
        nlinarith only [hrad,mul_le_mul_of_nonneg_left hbr (by norm_num : (0:ℝ) ≤ 116)]
      change _ ≤ (32*intrinsicUniversalConstant+200*κ)*R
      nlinarith [mul_nonneg (sub_nonneg.mpr hκ) hR]
    · have hblo : (1/16:ℝ) ≤ b := le_of_not_gt hb
      have hh := mul_le_mul_of_nonneg_left hκg (show 0 ≤ 16*b by positivity)
      have hh' := mul_le_mul_of_nonneg_left hbase (show 0 ≤ 16*κ by positivity)
      have h16 : 1 ≤ 16*κ*R := by nlinarith
      have hc16 : 16*κ ≤ subexponentialWidthConstant := by
        dsimp [subexponentialWidthConstant,κ]
        have hcin := intrinsicUniversalConstant_pos
        nlinarith
      exact (rectangleDistance_le_one μ (normalizedObservationSum X) A).trans
        (h16.trans (mul_le_mul_of_nonneg_right hc16 hR))
  exact (le_min (rectangleDistance_le_one μ (normalizedObservationSum X) A) hraw).trans
    (min_one_le_mul_min_one hC le_rfl)


/-- Exact Corollary 2 under the infimum-based Orlicz norm and the printed
average marginal normalization. No exponential-moment or comparison premise
is supplied by the caller. -/
theorem subexponentialCLT_psi1_intrinsic
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K)
    (haverage : ∀ j, (1/(n:ℝ))*∑ i, ∫ ω, X i ω j ^ 2 ∂μ = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤ subexponentialWidthConstant *
      min 1 (subexponentialWidthRate n p K (gaussianMaximumMean A)) := by
  exact subexponentialCLT_intrinsic μ hp hn X (psi1_exponentialHypotheses_exact h)
    (normalizedObservationSum_unit_diagonal_of_average_secondMoments
      (psi1_exponentialHypotheses_exact h) haverage) A hA

/-- The centered Gaussian target in Corollary 2 exists for every actual
array satisfying its assumptions, including all singular covariances. -/
theorem gaussian_factor_exists_of_psi1
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A*A.transpose = covariance μ (normalizedObservationSum X) := by
  obtain ⟨A,hA⟩ := RectangleCLT.Companion.SplitV4.normalizedSummands_gaussian_factor_exists
    (psi1_exponentialHypotheses_exact h).coordinate_memLp_two h.centered
  exact ⟨A, by simpa only [RectangleCLT.Companion.SplitV4.sumVector_normalizedSummands] using hA⟩

/-- One fixed coefficient works before every dimension, probability model,
scale, observation array, and actual covariance factor. -/
def SubexponentialWidthBound (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
  ∀ (X : Fin n → Ω → Vector p) (K : ℝ),
    Psi1IndependentHypotheses μ X K →
    (∀ j, (1/(n:ℝ))*∑ i, ∫ ω, X i ω j ^ 2 ∂μ = 1) →
  ∀ (A : Matrix (Fin p) (Fin p) ℝ),
    A*A.transpose = covariance μ (normalizedObservationSum X) →
    rectangleDistance μ (normalizedObservationSum X) A ≤ C *
      min 1 (subexponentialWidthRate n p K (gaussianMaximumMean A))

/-- Corollary 2 of the frozen arXiv v1 manuscript. -/
theorem corollary_2_intrinsic : ∃ C : ℝ, 0 < C ∧ SubexponentialWidthBound.{u} C := by
  refine ⟨subexponentialWidthConstant, zero_lt_one.trans_le one_le_subexponentialWidthConstant, ?_⟩
  intro Ω _ μ _ p n hp hn X K h havg A hA
  exact subexponentialCLT_psi1_intrinsic μ hp hn X h havg A hA

end
end RectangleCLTArxivV1
