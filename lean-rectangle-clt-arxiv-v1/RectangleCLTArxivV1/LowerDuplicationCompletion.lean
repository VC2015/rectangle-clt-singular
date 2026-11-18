import RectangleCLTCompanion.SplitV4.CoordinateDuplication
import RectangleCLTArxivV1.GaussianCalibration
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! Completion of the optional coordinate duplication in Appendix F.4.
The actual bounded observations, Gaussian comparison, width, symmetry and
moments are preserved; the Gaussian factor is constructed internally. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open Filter
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem iIndepFun_duplicateCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {p q n : ℕ} {μ : Measure Ω} {ξ : Fin n → Ω → Vector p}
    (h : iIndepFun ξ μ) (r : Fin q → Fin p) :
    iIndepFun (fun i ω => duplicateCoordinates r (ξ i ω)) μ :=
  h.comp (fun _ => duplicateCoordinates r) (fun _ => measurable_duplicateCoordinates r)

theorem boundedIndependent_duplicateCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {p q n : ℕ} {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (r : Fin q → Fin p) (hr : Function.Surjective r) :
    BoundedIndependentHypotheses μ (fun i ω => duplicateCoordinates r (ξ i ω)) δ where
  measurable i := (measurable_duplicateCoordinates r).comp (h.measurable i)
  independent := iIndepFun_duplicateCoordinates h.independent r
  centered i j := h.centered i (r j)
  bounded i := by
    filter_upwards [h.bounded i] with ω hω
    rwa [norm_duplicateCoordinates r hr]
  delta_nonneg := h.delta_nonneg

theorem identDistrib_duplicateCoordinates {Ω Ξ : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Ξ] {p q : ℕ}
    {μ : Measure Ω} {ν : Measure Ξ} {X : Ω → Vector p} {Y : Ξ → Vector p}
    (h : IdentDistrib X Y μ ν) (r : Fin q → Fin p) :
    IdentDistrib (fun ω => duplicateCoordinates r (X ω))
      (fun ω => duplicateCoordinates r (Y ω)) μ ν :=
  h.comp (measurable_duplicateCoordinates r)

theorem centrallySymmetric_duplicateCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} {μ : Measure Ω} {X : Ω → Vector p}
    (h : IdentDistrib X (fun ω => -X ω) μ μ) (r : Fin q → Fin p) :
    IdentDistrib (fun ω => duplicateCoordinates r (X ω))
      (fun ω => -duplicateCoordinates r (X ω)) μ μ := by
  exact identDistrib_duplicateCoordinates h r

/-- Every coordinate functional, hence every coordinate moment, is exactly
reindexed, with no integrability or moment loss. -/
theorem integral_duplicateCoordinates_coordinate {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} (μ : Measure Ω) (X : Ω → Vector p) (r : Fin q → Fin p)
    (j : Fin q) (φ : ℝ → ℝ) :
    (∫ ω,φ (duplicateCoordinates r (X ω) j) ∂μ)=(∫ ω,φ (X ω (r j)) ∂μ) := rfl

theorem duplicateCoordinates_envelope_iff {p q : ℕ} (r : Fin q → Fin p)
    (hr : Function.Surjective r) (x : Vector p) (b : ℝ) :
    ‖duplicateCoordinates r x‖≤b ↔ ‖x‖≤b := by
  rw [norm_duplicateCoordinates r hr]

/-- All norm functionals, including polynomial and Orlicz envelopes,
remain exactly equal rather than merely bounded by the old envelope. -/
theorem integral_duplicateCoordinates_norm {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} (μ : Measure Ω) (X : Ω → Vector p) (r : Fin q → Fin p)
    (hr : Function.Surjective r) (φ : ℝ → ℝ) :
    (∫ ω,φ ‖duplicateCoordinates r (X ω)‖ ∂μ)=(∫ ω,φ ‖X ω‖ ∂μ) := by
  simp only [norm_duplicateCoordinates r hr]

theorem gaussianMaximumMean_duplicateCoordinates {p q : ℕ}
    (r : Fin q → Fin p) (hr : Function.Surjective r)
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin q) (Fin q) ℝ)
    (hcov : B*B.transpose=fun j k => (A*A.transpose) (r j) (r k)) :
    gaussianMaximumMean B=gaussianMaximumMean A := by
  unfold gaussianMaximumMean
  rw [gaussianLaw_duplicateCoordinates r A B hcov,
    integral_map (measurable_duplicateCoordinates r).aemeasurable measurable_norm.aestronglyMeasurable]
  simp only [norm_duplicateCoordinates r hr]

/-- Actual duplication constructs its Gaussian covariance factor from the
duplicated data. No new Gaussian representation is an input assumption. -/
theorem exists_duplicateCoordinates_comparison {Ω : Type*} [MeasurableSpace Ω]
    {p q n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (r : Fin q → Fin p) (hr : Function.Surjective r)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ)) :
    ∃ B : Matrix (Fin q) (Fin q) ℝ,
      B*B.transpose=covariance μ (sumVector (fun i ω => duplicateCoordinates r (ξ i ω))) ∧
      gaussianLaw B=(gaussianLaw A).map (duplicateCoordinates r) ∧
      rectangleDistance μ (sumVector (fun i ω => duplicateCoordinates r (ξ i ω))) B=
        rectangleDistance μ (sumVector ξ) A ∧
      gaussianMaximumMean B=gaussianMaximumMean A := by
  obtain ⟨B,hB⟩ := gaussian_factor_exists (boundedIndependent_duplicateCoordinates h r hr)
  have hsum : sumVector (fun i ω => duplicateCoordinates r (ξ i ω))=
      duplicateCoordinates r ∘ sumVector ξ := by
    funext ω
    exact sumVector_duplicateCoordinates ξ r ω
  have hcov : B*B.transpose=fun j k => (A*A.transpose) (r j) (r k) := by
    rw [hB,hsum,duplicateCoordinates_covariance,hA]
  refine ⟨B,hB,gaussianLaw_duplicateCoordinates r A B hcov,?_,
    gaussianMaximumMean_duplicateCoordinates r hr A B hcov⟩
  rw [hsum]
  exact rectangleDistance_duplicateCoordinates_of_covariance μ (sumVector ξ) r hr A B hcov

/-- Copying coordinate zero once gives exact zero gap, retains unit
marginals, and preserves the actual rectangle distance and Gaussian width. -/
theorem exists_coordinatePadding_zero_gap_comparison {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ} (hp : 1≤p)
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ)) :
    ∃ B : Matrix (Fin (p+1)) (Fin (p+1)) ℝ,
      B*B.transpose=covariance μ
        (sumVector (fun i ω => duplicateCoordinates (coordinatePaddingMap hp) (ξ i ω))) ∧
      (∀ j,(B*B.transpose) j j=1) ∧ pairGap (B*B.transpose)=0 ∧
      rectangleDistance μ
          (sumVector (fun i ω => duplicateCoordinates (coordinatePaddingMap hp) (ξ i ω))) B=
        rectangleDistance μ (sumVector ξ) A ∧
      gaussianMaximumMean B=gaussianMaximumMean A := by
  let r : Fin (p+1) → Fin p := coordinatePaddingMap hp
  have hr : Function.Surjective r := coordinatePaddingMap_surjective hp (by omega)
  obtain ⟨B,hB,hLaw,hDist,hWidth⟩ := exists_duplicateCoordinates_comparison h r hr A hA
  have hsum : sumVector (fun i ω => duplicateCoordinates r (ξ i ω))=
      duplicateCoordinates r ∘ sumVector ξ := by
    funext ω
    exact sumVector_duplicateCoordinates ξ r ω
  have hcov : B*B.transpose=fun j k => (A*A.transpose) (r j) (r k) := by
    rw [hB,hsum,duplicateCoordinates_covariance,hA]
  have hdiag : ∀ j,(A*A.transpose) j j=1 := by rw [hA];exact hunit
  refine ⟨B,hB,?_,?_,hDist,hWidth⟩
  · intro j
    rw [hcov]
    exact hdiag (r j)
  · rw [hcov]
    exact coordinatePadding_pairGap_zero_of_unit_gram hp (by omega) A hdiag

private theorem lowerDuplication_dimensionLog_eq_one_add_log_pos (p : ℕ) (hp : 1 ≤ p) :
    dimensionLog p = 1 + Real.log (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (show p ≠ 0 by omega)
  rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hp0, Real.log_exp]

theorem lowerDuplication_dimensionLog_ratio_tendsto_one :
    Tendsto (fun p : ℕ => dimensionLog (p + 1) / dimensionLog p) atTop (𝓝 1) := by
  have hlog : Tendsto (fun p : ℕ => Real.log (p : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hden : Tendsto (fun p : ℕ => 1 + Real.log (p : ℝ)) atTop atTop :=
    tendsto_atTop_add_const_left atTop 1 hlog
  have hnum : Tendsto (fun p : ℕ => Real.log ((p : ℝ) + 1) - Real.log (p : ℝ)) atTop (𝓝 0) :=
    Real.tendsto_log_nat_add_one_sub_log
  have hratio := (hnum.div_atTop hden).add_const (1 : ℝ)
  simp only [zero_add] at hratio
  apply hratio.congr'
  filter_upwards [eventually_ge_atTop 1] with p hp
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn : 1 + Real.log (p : ℝ) ≠ 0 := by
    have hl := Real.log_nonneg hpR
    linarith
  rw [lowerDuplication_dimensionLog_eq_one_add_log_pos (p + 1) (by omega),
    lowerDuplication_dimensionLog_eq_one_add_log_pos p hp, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

theorem lowerDuplication_dimensionLog_sequence_ratio_tendsto_one (p : ℕ → ℕ)
    (hp : Tendsto p atTop atTop) :
    Tendsto (fun n => dimensionLog (p n + 1) / dimensionLog (p n)) atTop (𝓝 1) :=
  lowerDuplication_dimensionLog_ratio_tendsto_one.comp hp


end
end RectangleCLTArxivV1
