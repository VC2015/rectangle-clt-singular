import RectangleCLTArxivV1.SupplementalGCapSeededComparison
import RectangleCLTArxivV1.SupplementalGCapIntegratedRemainder
import RectangleCLTArxivV1.IntrinsicMain

/- The dimension-logarithm cap for the actual independent bounded array.
Every boundary, envelope and seeded-remainder supplier is discharged below. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def dimensionCapComparisonConstant (C₀ : ℝ) : ℝ :=
  directInitializationConstant + capSeededTimeComparisonConstant C₀

theorem dimensionCapComparisonConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < dimensionCapComparisonConstant C₀ :=
  add_pos directInitializationConstant_pos (capSeededTimeComparisonConstant_pos hC₀)

theorem dimensionCap_time_gain_ge_one {ε L : ℝ} (hε : 0 < ε)
    (hεsmall : ε ≤ 1) (hL : 1 ≤ L) : 1 ≤ min (1 + Real.log (1 / ε)) L := by
  have hr : 1 ≤ 1 / ε := (le_div_iff₀ hε).2 (by linarith)
  exact le_min (by linarith [Real.log_nonneg hr]) hL

theorem dimensionCap_smooth_comparison
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ)
    (hband : relativeDerivativeBandwidth*δ ≤ s.bandwidth) (hband16 : 16*δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4)
    (henv : ∀ v : ℝ, 0 ≤ v → v ≤ 1 →
      (∫ z : Ω × Vector p, s.F (directSlepianPoint ξ v z) *
        (1-s.F (directSlepianPoint ξ v z)) ∂μ.prod (gaussianLaw A)) ≤
        derivativeEnvelopeSignedAverageConstant*s.bandwidth*κ)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    |(∫ ω, s.F (sumVector ξ ω) ∂μ)-(∫ g, s.F g ∂gaussianLaw A)| ≤
      dimensionCapComparisonConstant C₀*(κ*dimensionLog p)*
        (δ+δ^2/s.bandwidth*min (1+Real.log (1/(dimensionLog p*s.bandwidth^2))) (dimensionLog p)) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  let G := min (1+Real.log (1/ε)) L
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hε : 0 < ε := mul_pos (zero_lt_one.trans_le hL) (sq_pos_of_pos s.bandwidth_pos)
  have hG : 1 ≤ G := dimensionCap_time_gain_ge_one hε
    (by change dimensionLog p*s.bandwidth^2 ≤ 1; linarith) hL
  have hb := relative_derivative_bandwidth_conditions h.delta_nonneg hband
  have hi := direct_initialization_intrinsic_of_envelope μ ξ h (relativeMomentBounds_of_envelope h)
    hunit A hA s hfaces hb.1 (zero_le_one.trans hκ) henv
  have hs := cap_normalizedSeeded_time_comparison_bound μ ξ h (h.delta_pos hp hunit) hp hunit A hA s
    hb.2 hband16 hC₀ hκ hsmall hc
  have ht := smoother_gap_le_actual_two_stage_gaps s μ ξ h.measurable A hε.le
  have hh := ht.trans (add_le_add hi hs)
  change _ ≤ directInitializationConstant*δ*(L*κ)+
      directInitializationConstant*δ^2*(L*κ)/s.bandwidth+
      capSeededTimeComparisonConstant C₀*(κ*L)*(δ+δ^2/s.bandwidth*G) at hh
  apply hh.trans
  change _ ≤ dimensionCapComparisonConstant C₀*(κ*L)*(δ+δ^2/s.bandwidth*G)
  have hcst : 0 ≤ directInitializationConstant*(κ*L)*(δ^2/s.bandwidth) := by
    exact mul_nonneg (mul_nonneg directInitializationConstant_pos.le
      (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL)))
      (div_nonneg (sq_nonneg δ) s.bandwidth_pos.le)
  have hgain := mul_le_mul_of_nonneg_left hG hcst
  unfold dimensionCapComparisonConstant
  ring_nf at hgain ⊢
  nlinarith only [hgain]

def dimensionCapBandwidthConstant : ℝ := max 16 relativeDerivativeBandwidth

theorem dimensionCapBandwidthConstant_ge_one : 1 ≤ dimensionCapBandwidthConstant :=
  (by norm_num : (1 : ℝ) ≤ 16).trans (le_max_left _ _)

def dimensionCapBoundaryConstant : ℝ :=
  intrinsicOptimizationConstant dimensionCapBandwidthConstant
    (dimensionCapComparisonConstant intrinsicBoundaryConstant+9*intrinsicBoundaryConstant)

theorem dimensionCapBoundaryConstant_ge_one : 1 ≤ dimensionCapBoundaryConstant := by
  have hA := dimensionCapBandwidthConstant_ge_one
  have hC := dimensionCapComparisonConstant_pos intrinsicBoundaryConstant_pos
  have hB := intrinsicBoundaryConstant_pos
  unfold dimensionCapBoundaryConstant intrinsicOptimizationConstant
  nlinarith [mul_nonneg (show 0 ≤ dimensionCapComparisonConstant intrinsicBoundaryConstant+
    9*intrinsicBoundaryConstant by linarith) (show 0 ≤ dimensionCapBandwidthConstant+3 by linarith)]

/-- Actual comparison with the intrinsic boundary coefficient retained. -/
theorem dimensionCapBoundaryCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ dimensionCapBoundaryConstant *
      min 1 (dimensionCapRate (intrinsicBoundaryCoefficient μ ξ A) δ (dimensionLog p)) := by
  letI : NeZero p := ⟨by omega⟩
  let L := dimensionLog p
  let κ := intrinsicBoundaryCoefficient μ ξ A
  let b := dimensionCapBandwidth dimensionCapBandwidthConstant δ L
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hδ : 0 < δ := h.delta_pos hp hunit
  have hκ : 1 ≤ κ := one_le_intrinsicBoundaryCoefficient μ ξ A hp
  have hBW := dimensionCapBandwidthConstant_ge_one
  have hbpos : 0 < b := dimensionCapBandwidth_pos (zero_lt_one.trans_le hBW) hδ hL
  have hb : dimensionCapBandwidthConstant*δ ≤ b := dimensionCapBandwidth_admissible
    (zero_le_one.trans hBW) hδ.le hL
  have hband : relativeDerivativeBandwidth*δ ≤ b :=
    (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le).trans hb
  have hband16 : 16*δ ≤ b := (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le).trans hb
  have hδb : δ ≤ b := (le_mul_of_one_le_left hδ.le hBW).trans hb
  have hC : 0 ≤ dimensionCapComparisonConstant intrinsicBoundaryConstant+9*intrinsicBoundaryConstant := by
    linarith [dimensionCapComparisonConstant_pos intrinsicBoundaryConstant_pos,intrinsicBoundaryConstant_pos]
  apply dimensionCap_rate_of_small_bandwidth_estimate hBW hC hκ hδ hL
    (rectangleDistance_le_one μ (sumVector ξ) A)
  intro hsmall
  have hsmooth : smoothingDiscrepancy μ (sumVector ξ) A b hbpos ≤
      dimensionCapComparisonConstant intrinsicBoundaryConstant*(κ*L)*
        (δ+δ^2/b*min (1+Real.log (1/(L*b^2))) L) := by
    apply (smoothingDiscrepancy_le_iff μ (sumVector ξ) h.measurable_sum A b hbpos _).mpr
    intro lo hi
    let s := FaceSmoother.closedBox lo hi b hbpos
    have hband4 : 4*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right relativeDerivativeBandwidth_ge_four hδ.le).trans hband
    exact dimensionCap_smooth_comparison μ ξ h hp hunit A hA s rfl hband hband16
      intrinsicBoundaryConstant_pos hκ hsmall.le
      (fun v hv0 hv1 => integral_smallerEnvelope_directSlepian_intrinsic μ ξ h hunit A hA
        s rfl hband4 hv0 hv1)
      (fun t ht => intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0
        (by positivity) ht.1.le ht.2.le)
  have hrho := (rectangleDistance_le_smoothingDiscrepancy_intrinsic hp μ (sumVector ξ)
    h.measurable_sum A intrinsicBoundaryConstant_pos.le hδ.le (zero_le_one.trans hκ) hbpos hδb
    (intrinsicRectangleConcentration_bounded_endpoint h hp hunit A)
    (intrinsicRectangleConcentration_gaussian_endpoint μ ξ hp A (fun j => by rw [hA,hunit j]))).trans
      (add_le_add_right hsmooth _)
  let F := δ+δ^2/b*min (1+Real.log (1/(L*b^2))) L
  have hF : 0 ≤ F := by
    have hε : 0 < L*b^2 := by positivity
    have hG := dimensionCap_time_gain_ge_one hε (by linarith) hL
    dsimp [F]
    positivity
  have hx := mul_nonneg (mul_nonneg (dimensionCapComparisonConstant_pos intrinsicBoundaryConstant_pos).le
    (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL))) hbpos.le
  have hy := mul_nonneg (mul_nonneg (show 0 ≤ 9*intrinsicBoundaryConstant from
    mul_nonneg (by norm_num) intrinsicBoundaryConstant_pos.le)
    (mul_nonneg (zero_le_one.trans hκ) (zero_le_one.trans hL))) hF
  change rectangleDistance μ (sumVector ξ) A ≤
    (dimensionCapComparisonConstant intrinsicBoundaryConstant+9*intrinsicBoundaryConstant)*κ*L*
      (b+δ+δ^2/b*min (1+Real.log (1/(L*b^2))) L)
  apply hrho.trans
  change dimensionCapComparisonConstant intrinsicBoundaryConstant*(κ*L)*F+
    9*intrinsicBoundaryConstant*b*κ*L ≤ _
  dsimp only [F] at hy ⊢
  ring_nf at hx hy ⊢
  nlinarith only [hx,hy]

def dimensionCapCoreConstant : ℝ :=
  max (dimensionCapBoundaryConstant*max 1 intrinsicGaussianCoefficientConstant) (max 1 (Real.pi/2))

theorem dimensionCapCoreConstant_ge_one : 1 ≤ dimensionCapCoreConstant :=
  (le_max_left _ _).trans (le_max_right _ _)

/-- The expected-maximum theorem is invoked only after the actual capped
comparison has been proved. The complementary regime uses probability≤1. -/
theorem dimensionCapCLT
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) :
    rectangleDistance μ (sumVector ξ) A ≤ dimensionCapCoreConstant *
      min 1 (dimensionCapRate (gaussianMaximumMean A) δ (dimensionLog p)) := by
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hg := gaussianMaximumMean_nonneg A
  have hr : 0 ≤ dimensionCapRate (gaussianMaximumMean A) δ (dimensionLog p) := by
    unfold dimensionCapRate
    exact mul_nonneg (mul_nonneg (mul_nonneg h.delta_nonneg hg) (zero_le_one.trans hL))
      (Real.sqrt_nonneg _)
  have hone := rectangleDistance_le_one μ (sumVector ξ) A
  have hK : 0 ≤ dimensionCapBoundaryConstant := zero_le_one.trans dimensionCapBoundaryConstant_ge_one
  by_cases hsmall : δ*dimensionLog p ≤ gaussianMaximumMean A
  · have hcoef := intrinsicBoundaryCoefficient_le_gaussian h hp hunit A hA hsmall
    have hrate := dimensionCapRate_le_coefficient hcoef h.delta_nonneg (zero_le_one.trans hL)
    have hcap := (min_le_min_left 1 hrate).trans
      (intrinsic_min_one_mul_le intrinsicGaussianCoefficientConstant_pos.le hr)
    have hh := (dimensionCapBoundaryCLT μ ξ h hp hunit A hA).trans
      (mul_le_mul_of_nonneg_left hcap hK)
    apply hh.trans
    have hfin := mul_le_mul_of_nonneg_right
      (le_max_left (dimensionCapBoundaryConstant*max 1 intrinsicGaussianCoefficientConstant)
        (max 1 (Real.pi/2))) (le_min zero_le_one hr)
    convert hfin using 1
    ring
  · have hdiag (j : Fin p) : (A*A.transpose) j j=1 := by rw [hA,hunit j]
    have hlow := sqrt_two_div_pi_le_gaussianMaximumMean hp A hdiag
    have hraw := dimensionCap_trivial_large_envelope hone hlow h.delta_nonneg hL (lt_of_not_ge hsmall)
    have hcap := intrinsic_capped_of_le_one_and_mul hr hone hraw
    exact hcap.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (le_min zero_le_one hr))

def dimensionCapUniversalConstant : ℝ := max dimensionCapCoreConstant capBoundedIntegratedRemainderConstant

theorem dimensionCapUniversalConstant_pos : 0 < dimensionCapUniversalConstant :=
  (zero_lt_one.trans_le dimensionCapCoreConstant_ge_one).trans_le (le_max_left _ _)

universe u

/-- Proposition G.1, including the uniform integral of the literal fourth
remainder. One fixed constant precedes every model and threshold. -/
theorem proposition_G1_dimension_log_cap :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ)
      (ξ : Fin n → Ω → Vector p) (δ : ℝ),
      BoundedIndependentHypotheses μ ξ δ → 1 ≤ p →
      (∀ j, covariance μ (sumVector ξ) j j=1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ, A*A.transpose=covariance μ (sumVector ξ) →
      (rectangleDistance μ (sumVector ξ) A ≤ C*
        min 1 (δ*gaussianMaximumMean A*dimensionLog p*Real.sqrt (dimensionCapGain δ (dimensionLog p)))) ∧
      (∀ (s : FaceSmoother p) (x : Vector p), dimensionCapBandwidthConstant*δ ≤ s.bandwidth →
        dimensionLog p*s.bandwidth^2 ≤ 1/4 →
        (∫ t in (0 : ℝ)..1, |seededFourthRemainder s μ ξ A x (dimensionLog p*s.bandwidth^2) t|) ≤
          C*(δ^2*intrinsicBoundaryCoefficient μ ξ A*dimensionLog p/s.bandwidth)*
            min (1+Real.log (1/(dimensionLog p*s.bandwidth^2))) (dimensionLog p)) := by
  refine ⟨dimensionCapUniversalConstant,dimensionCapUniversalConstant_pos,?_⟩
  intro Ω _ μ _ p n ξ δ h hp hunit A hA
  have hδ : 0 < δ := h.delta_pos hp hunit
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hκ := one_le_intrinsicBoundaryCoefficient μ ξ A hp
  constructor
  · have hr : 0 ≤ dimensionCapRate (gaussianMaximumMean A) δ (dimensionLog p) := by
      unfold dimensionCapRate
      have hg := gaussianMaximumMean_nonneg A
      positivity
    exact (dimensionCapCLT μ ξ h hp hunit A hA).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one hr))
  · intro s x hband hsmall
    have hb : relativeDerivativeBandwidth*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le).trans hband
    have hb16 : 16*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le).trans hband
    have hraw := cap_seededFourthRemainder_bounded_integral_bound μ ξ h hδ hp hunit A hA s x
      (relative_derivative_bandwidth_conditions hδ.le hb).2 hb16 hsmall
    have hε : 0 < dimensionLog p*s.bandwidth^2 :=
      mul_pos (zero_lt_one.trans_le hL) (sq_pos_of_pos s.bandwidth_pos)
    have hG := dimensionCap_time_gain_ge_one hε (by linarith) hL
    have hfactor : 0 ≤ (δ^2*intrinsicBoundaryCoefficient μ ξ A*dimensionLog p/s.bandwidth)*
        min (1+Real.log (1/(dimensionLog p*s.bandwidth^2))) (dimensionLog p) :=
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg δ) (zero_le_one.trans hκ))
        (zero_le_one.trans hL)) s.bandwidth_pos.le) (zero_le_one.trans hG)
    apply hraw.trans
    have hfin := mul_le_mul_of_nonneg_right
      (le_max_right dimensionCapCoreConstant capBoundedIntegratedRemainderConstant) hfactor
    simpa only [mul_assoc,dimensionCapUniversalConstant] using hfin

end
end RectangleCLTArxivV1
