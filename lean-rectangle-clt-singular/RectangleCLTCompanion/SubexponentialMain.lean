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

def subexponentialGapThreshold (c₀ : ℝ) : ℝ := min (1 / 16) (c₀ / 8)

def subexponentialGapParameter (c₀ : ℝ) : ℝ := max 1 (2 / c₀)

def subexponentialGapComparisonConstant (c₀ : ℝ) : ℝ :=
  16 * companionUniversalConstant *
    (1 + Real.sqrt (subexponentialGapParameter c₀ *
      (1 + logPlus (Real.sqrt (subexponentialGapParameter c₀)))))

/-- The dependence on a fixed positive gap is chosen before all data. -/
def subexponentialGapConstant (c₀ : ℝ) : ℝ :=
  1 + (subexponentialGapThreshold c₀)⁻¹ +
    subexponentialGapComparisonConstant c₀ + 100 * subexponentialGaussianBoundaryConstant

theorem subexponentialGapThreshold_pos {c₀ : ℝ} (hc₀ : 0 < c₀) :
    0 < subexponentialGapThreshold c₀ := by
  exact lt_min (by norm_num) (div_pos hc₀ (by norm_num))

theorem subexponentialGapComparisonConstant_nonneg (c₀ : ℝ) :
    0 ≤ subexponentialGapComparisonConstant c₀ := by
  unfold subexponentialGapComparisonConstant
  have hC : 0 ≤ companionUniversalConstant := zero_le_one.trans one_le_companionUniversalConstant
  positivity

theorem one_le_subexponentialGapConstant {c₀ : ℝ} (hc₀ : 0 < c₀) :
    1 ≤ subexponentialGapConstant c₀ := by
  have ht := (inv_pos.mpr (subexponentialGapThreshold_pos hc₀)).le
  have hcomp := subexponentialGapComparisonConstant_nonneg c₀
  have hG := one_le_subexponentialGaussianBoundaryConstant
  unfold subexponentialGapConstant
  linarith

/-- Fixed-positive-correlation-gap refinement for sub-exponential rows. -/
theorem fixedGapSubexponentialCLT {c₀ : ℝ} (hc₀ : 0 < c₀) :
    FixedGapSubexponentialCLT.{u} c₀ (subexponentialGapConstant c₀) := by
  intro Ω _ μ _ p n hp hn X K A h hunit hA hgap R
  let b := subexponentialScale n K
  let L := dimensionLog p
  have hbpos : 0 < b := subexponentialScale_pos hn h.one_le_scale
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  have hC := one_le_subexponentialGapConstant hc₀
  apply rectangleError_saturate μ (normalizedObservationSum X) A R hC
  by_cases hb : b < subexponentialGapThreshold c₀
  · have hb16 : b < 1 / 16 := hb.trans_le (min_le_left _ _)
    have hbc : b < c₀ / 8 := hb.trans_le (min_le_right _ _)
    let u := 4 * dimensionLog n
    let ξ := normalizedClippedRows μ X (K * u)
    let W := sumVector ξ
    let d : Vector p := fun j => Real.sqrt (covariance μ W j j)
    let c := pairGap (covariance μ
      (fun ω => diagonalScale (fun j => (d j)⁻¹) (W ω)))
    let M := subexponentialGapParameter c₀
    have hu : 0 ≤ u := mul_nonneg (by norm_num)
      (zero_le_one.trans (log_exp_mul_nat_ge_one hn))
    have hδ : 2 * (K * u) / Real.sqrt (n : ℝ) = 8 * b := by
      dsimp [u, b, subexponentialScale]
      ring
    have hbounded : BoundedIndependentHypotheses μ ξ (8 * b) := by
      rw [← hδ]
      exact normalizedClippedRows_boundedHypotheses h.measurable h.independent
        (mul_nonneg hK hu)
    obtain ⟨AT, hAT⟩ := gaussian_factor_exists_of_boundedIndependent hbounded
    have he : -(4 * dimensionLog n) / 2 = -2 * dimensionLog n := by ring
    have hsmall : 2 * K * Real.exp (-u / 2) ≤ 1 / 2 := by
      simpa only [u, he, subexponentialResidualSD, subexponentialTailFactor] using
        subexponentialResidualSD_le_half hn hK hb16
    have hd (j : Fin p) : (1 / 2 : ℝ) ≤ d j :=
      clipped_standardDeviation_ge_half h hu hn hunit hsmall j
    have hvar (j : Fin p) : covariance μ W j j = d j ^ 2 := by
      have hnonneg : 0 ≤ covariance μ W j j := by
        rw [← hAT, Matrix.mul_apply]
        exact Finset.sum_nonneg (fun k _ => by
          simpa only [Matrix.transpose_apply, ← pow_two] using sq_nonneg (AT j k))
      exact (Real.sq_sqrt hnonneg).symm
    have hchange : 8 * K * Real.exp (-u / 2) < c₀ / 2 := by
      have hh := four_mul_subexponentialResidualSD_lt_half_gap hn hK hbc
      dsimp only [subexponentialResidualSD, subexponentialTailFactor] at hh
      dsimp only [u]
      rw [he]
      nlinarith
    have hc : c₀ / 2 ≤ c := by
      have hh := standardizedClipped_pairGap_lower h hu hn hunit hsmall
      change pairGap (covariance μ (normalizedObservationSum X)) -
        8 * K * Real.exp (-u / 2) ≤ c at hh
      linarith
    have hcp : 0 < c := (div_pos hc₀ (by norm_num : (0 : ℝ) < 2)).trans_le hc
    have hM : 1 ≤ M := le_max_left _ _
    have hκM : kappa L c ≤ M := by
      apply (kappa_le_inv hcp).trans
      have hinv := one_div_le_one_div_of_le (div_pos hc₀ (by norm_num : (0 : ℝ) < 2)) hc
      have heq : 1 / (c₀ / 2) = 2 / c₀ := by field_simp [hc₀.ne'] <;> ring
      simpa only [one_div] using (calc
        (1 / c) ≤ 1 / (c₀ / 2) := hinv
        _ = 2 / c₀ := heq
        _ ≤ M := le_max_right _ _)
    have hcompare (S : Rect p) : rectangleError μ W AT S ≤
        subexponentialGapComparisonConstant c₀ * fixedGapSubexponentialRate b L := by
      have hh := bounded_gapCLT_after_standardization hbounded hp hn d hd hvar AT hAT S
      rw [show 2 * (8 * b) = 16 * b by ring] at hh
      have hr := gapRate_le_fixedGapSubexponentialRate
        (by norm_num : (1 : ℝ) ≤ 16) hbpos hL hM hκM
      have hmin := (min_le_right (1 : ℝ) (gapRate (16 * b) L c)).trans hr
      have hscaled := mul_le_mul_of_nonneg_left hmin
        (zero_le_one.trans one_le_companionUniversalConstant)
      have hout := hh.trans hscaled
      convert hout using 1 <;>
        dsimp only [subexponentialGapComparisonConstant, M, L, c] <;> ring
    have ht := subexponential_clipping_reduction h hp hn hunit A AT hA hAT hcompare R
    have ht' : rectangleError μ (normalizedObservationSum X) A R ≤
        subexponentialGapComparisonConstant c₀ * fixedGapSubexponentialRate b L +
        subexponentialGaussianBoundaryConstant *
          (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
          Real.sqrt L + 1 / (n : ℝ) := by
      simpa only [residualCouplingRadius, gaussianCouplingRadius,
        subexponentialResidualRadius, subexponentialGaussianRadius,
        subexponentialResidualSD, subexponentialTailFactor, subexponentialUnionLog,
        subexponentialGaussianBoundaryConstant, he, L] using ht
    have htransfer := subexponential_transfer_error_weighted_le hn hp h.one_le_scale
      one_le_subexponentialGaussianBoundaryConstant
    change subexponentialGaussianBoundaryConstant *
        (subexponentialResidualRadius n p K + subexponentialGaussianRadius n p K) *
        Real.sqrt L + 1 / (n : ℝ) ≤
      (100 * subexponentialGaussianBoundaryConstant) * b * L ^ (3 / 2 : ℝ) at htransfer
    have hbase := fixedGap_base_le_rate hbpos.le hLp.le
    have hrawnonneg : 0 ≤ fixedGapSubexponentialRate b L :=
      (mul_nonneg hbpos.le (Real.rpow_nonneg hLp.le _)).trans hbase
    have hG : 0 ≤ subexponentialGaussianBoundaryConstant :=
      zero_le_one.trans one_le_subexponentialGaussianBoundaryConstant
    have hscaled := mul_le_mul_of_nonneg_left hbase
      (show 0 ≤ 100 * subexponentialGaussianBoundaryConstant by positivity)
    have htpos := (inv_pos.mpr (subexponentialGapThreshold_pos hc₀)).le
    have hpositiveProduct := mul_nonneg htpos hrawnonneg
    unfold subexponentialGapConstant
    nlinarith
  · have hblo : subexponentialGapThreshold c₀ ≤ b := le_of_not_gt hb
    have htpos := subexponentialGapThreshold_pos hc₀
    have hbase := base_le_fixedGapSubexponentialRate hbpos.le hL
    have hrawnonneg : 0 ≤ fixedGapSubexponentialRate b L := hbpos.le.trans hbase
    have hinv : (subexponentialGapThreshold c₀)⁻¹ ≤ subexponentialGapConstant c₀ := by
      unfold subexponentialGapConstant
      linarith [subexponentialGapComparisonConstant_nonneg c₀,
        one_le_subexponentialGaussianBoundaryConstant]
    have hprod := mul_le_mul_of_nonneg_left (hblo.trans hbase) (inv_pos.mpr htpos).le
    rw [inv_mul_cancel₀ htpos.ne'] at hprod
    exact (rectangleError_le_one μ (normalizedObservationSum X) A R).trans
      (hprod.trans (mul_le_mul_of_nonneg_right hinv hrawnonneg))

/-- A concrete Gaussian factor exists for every admissible normalized
sub-exponential array, including singular covariance. -/
theorem gaussian_factor_exists_of_subexponential
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (normalizedObservationSum X) := by
  let W := normalizedObservationSum X
  let V : Ω → Vector p := 0
  have hL2 (a : JointIndex p) : MemLp (fun ω => jointValue W V ω a) 2 μ := by
    cases a with
    | inl j => exact normalizedObservationSum_coordinate_memLp_two h j
    | inr j => exact memLp_zero
  have hmean (a : JointIndex p) : (∫ ω, jointValue W V ω a ∂μ) = 0 := by
    cases a with
    | inl j => exact normalizedObservationSum_coordinate_centered h j
    | inr j => simp [jointValue, V]
  have hrest : restoredCovariance (jointSecondMoment μ W V) = covariance μ W := by
    simpa only [V, add_zero] using jointSecondMoment_restoredCovariance W V hL2 hmean
  have hcov : (covariance μ W).PosSemidef := by
    rw [← hrest]
    exact restoredCovariance_posSemidef _ (jointSecondMoment_posSemidef hL2)
  refine ⟨hcov.sqrt, ?_⟩
  have hsymmetric : hcov.sqrt.transpose = hcov.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hcov.posSemidef_sqrt.isHermitian
  rw [hsymmetric]
  exact hcov.sqrt_mul_self

/-- The paper's Orlicz-norm version, with the average second moments
normalized as in the manuscript rather than a supplied covariance identity. -/
theorem subexponentialCLT_psi1
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ X K) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) (R : Rect p) :
    rectangleError μ (normalizedObservationSum X) A R ≤
      (2 * subexponentialUniversalConstant) *
        min 1 (unrestrictedRate (subexponentialScale n K) (dimensionLog p)) := by
  have he := h.exponentialHypotheses
  have hunit := normalizedObservationSum_unit_diagonal_of_average_secondMoments he haverage
  have hh := subexponentialCLT μ p n hp hn X (2 * K) A he hunit hA R
  rw [subexponentialScale_mul] at hh
  have hscale := min_one_unrestrictedRate_mul_le (by norm_num : (1 : ℝ) ≤ 2)
    (subexponentialScale_pos hn h.one_le_scale)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  have hC := zero_le_one.trans one_le_subexponentialUniversalConstant
  exact (hh.trans (mul_le_mul_of_nonneg_left hscale hC)).trans_eq (by ring)

/-- The fixed-gap Orlicz version of the paper's sub-exponential corollary. -/
theorem fixedGapSubexponentialCLT_psi1
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K c₀ : ℝ}
    (hc₀ : 0 < c₀) (h : Psi1IndependentHypotheses μ X K) (hp : 1 ≤ p) (hn : 1 ≤ n)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (hgap : c₀ ≤ pairGap (covariance μ (normalizedObservationSum X))) (R : Rect p) :
    rectangleError μ (normalizedObservationSum X) A R ≤
      (2 * subexponentialGapConstant c₀) *
        min 1 (fixedGapSubexponentialRate (subexponentialScale n K) (dimensionLog p)) := by
  have he := h.exponentialHypotheses
  have hunit := normalizedObservationSum_unit_diagonal_of_average_secondMoments he haverage
  have hh := fixedGapSubexponentialCLT hc₀ μ p n hp hn X (2 * K) A he hunit hA hgap R
  rw [subexponentialScale_mul] at hh
  have hscale := min_one_fixedGapSubexponentialRate_mul_le (by norm_num : (1 : ℝ) ≤ 2)
    (subexponentialScale_pos hn h.one_le_scale)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  have hC := zero_le_one.trans (one_le_subexponentialGapConstant hc₀)
  exact (hh.trans (mul_le_mul_of_nonneg_left hscale hC)).trans_eq (by ring)

theorem subexponentialCLTExists : ∃ C : ℝ, 1 ≤ C ∧ SubexponentialCLT.{u} C :=
  ⟨subexponentialUniversalConstant, one_le_subexponentialUniversalConstant, subexponentialCLT⟩

theorem fixedGapSubexponentialCLTExists {c₀ : ℝ} (hc₀ : 0 < c₀) :
    ∃ C : ℝ, 1 ≤ C ∧ FixedGapSubexponentialCLT.{u} c₀ C :=
  ⟨subexponentialGapConstant c₀, one_le_subexponentialGapConstant hc₀,
    fixedGapSubexponentialCLT hc₀⟩

end
end RectangleCLT.Companion
