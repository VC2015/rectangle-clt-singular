import RectangleCLTArxivV1.BoundedRectangleIntrinsic
import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import RectangleCLTArxivV1.ThinnedMaximum
import RectangleCLTArxivV1.GaussianWidthOrder
import RectangleCLTArxivV1.IntrinsicInputs
import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SplitV4.SeededPathBase

/-! Actual intrinsic concentration suppliers for the endpoints and seeded
base. The retained mask is averaged under its genuine unconditional law. -/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section

def intrinsicBoundaryConstant : ℝ := max seededBaseConcentrationConstant 1073742336

theorem intrinsicBoundaryConstant_pos : 0 < intrinsicBoundaryConstant :=
  lt_of_lt_of_le (by norm_num) (le_max_right _ _)

theorem intrinsicBoundaryConstant_ge_512 : (512 : ℝ) ≤ intrinsicBoundaryConstant :=
  (by norm_num : (512 : ℝ) ≤ 1073742336).trans (le_max_right _ _)

theorem intrinsicBoundaryConstant_ge_1024 : (1024 : ℝ) ≤ intrinsicBoundaryConstant :=
  (by norm_num : (1024 : ℝ) ≤ 1073742336).trans (le_max_right _ _)

theorem combine_intrinsicBoundary {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    {P c : ℝ}
    (hlog : P ≤ c * Real.sqrt (dimensionLog p))
    (hmax : P ≤ c * (1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A))) :
    P ≤ c * intrinsicBoundaryCoefficient μ ξ A := by
  unfold intrinsicBoundaryCoefficient
  by_cases hh : Real.sqrt (dimensionLog p) ≤
      1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)
  · rwa [min_eq_left hh]
  · rwa [min_eq_right (le_of_not_ge hh)]

theorem intrinsicRectangleConcentration_bounded_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    IntrinsicRectangleConcentration (μ.map (sumVector ξ)) intrinsicBoundaryConstant δ
      (intrinsicBoundaryCoefficient μ ξ A) := by
  intro s z d hd
  have hsδ : 0 ≤ d+δ := add_nonneg hd.le h.delta_nonneg
  have hC64 : (64 : ℝ) ≤ intrinsicBoundaryConstant := (by norm_num : (64:ℝ)≤512).trans intrinsicBoundaryConstant_ge_512
  have hClog : (256 : ℝ) ≤ intrinsicBoundaryConstant :=
    (by norm_num : (256 : ℝ) ≤ 512).trans intrinsicBoundaryConstant_ge_512
  have hlog := boundedRectangleBoundary_map_logarithmic hp μ ξ h (by norm_num) hunit s z hd
  have hmax := boundedRectangleBoundary_map_intrinsic μ ξ h (by norm_num) hunit s z hd
  rw [div_one] at hmax hlog
  rw [← mul_assoc] at hlog
  have hE : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hEmax : (∫ ω, ‖sumVector ξ ω‖ ∂μ) ≤
      1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A) := by
    linarith [le_max_left (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
  have hfin := combine_intrinsicBoundary μ ξ A
    (hlog.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hClog hsδ) (Real.sqrt_nonneg _)))
    (hmax.trans (by
      calc
        _ = (64 * (d+δ)) * (∫ ω, ‖sumVector ξ ω‖ ∂μ) := by ring
        _ ≤ (intrinsicBoundaryConstant * (d+δ)) *
            (1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)) :=
          mul_le_mul (mul_le_mul_of_nonneg_right hC64 hsδ) hEmax hE
            (mul_nonneg intrinsicBoundaryConstant_pos.le hsδ)))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using hfin

theorem intrinsicRectangleConcentration_gaussian_endpoint
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1) :
    IntrinsicRectangleConcentration (gaussianLaw A) intrinsicBoundaryConstant 0
      (intrinsicBoundaryCoefficient μ ξ A) := by
  intro s z d hd
  have hClog : (4 : ℝ) ≤ intrinsicBoundaryConstant :=
    (by norm_num : (4 : ℝ) ≤ 512).trans intrinsicBoundaryConstant_ge_512
  have hC2 : (2 : ℝ) ≤ intrinsicBoundaryConstant :=
    (by norm_num : (2 : ℝ) ≤ 512).trans intrinsicBoundaryConstant_ge_512
  have hlog := gaussianRectangleBoundary_fixed_shift_logarithmic hp s A z (by norm_num) hd hdiag
  rw [div_one] at hlog
  have hmax := gaussianRectangleBoundary_intrinsic_fixed_shift s A z (by norm_num) hd hdiag
  rw [div_one] at hmax
  have hgmax : gaussianMaximumMean A ≤
      1 + max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A) := by
    linarith [le_max_right (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
  have hfin := combine_intrinsicBoundary μ ξ A
    (hlog.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hClog hd.le) (Real.sqrt_nonneg _)))
    (hmax.trans (mul_le_mul (mul_le_mul_of_nonneg_right hC2 hd.le) hgmax
      (gaussianMaximumMean_nonneg A) (mul_nonneg intrinsicBoundaryConstant_pos.le hd.le)))
  simpa only [add_zero, mul_assoc, mul_left_comm, mul_comm] using hfin

/-- When the bounded retained component has variance at least one third,
its unconditional intrinsic expected maximum is controlled by that of W. -/
theorem seededRectangleBoundary_intrinsic_bounded_dominant
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {ε t : ℝ}
    (ht : 0 ≤ t) (hhalf : t ≤ 2/3) (s : FaceSmoother p) (z : Vector p)
    {d : ℝ} (hd : 0 < d) :
    (seededSplitBaseDistribution μ ξ A x ε t).real {q | q+z ∈ s.boundaryLayer d} ≤
      1024 * (d+δ) * ∫ ω, ‖sumVector ξ ω‖ ∂μ := by
  have ht1 : t ≤ 1 := by linarith
  let B := bernoulliArrayLaw μ ξ t
  let G := seededSplitGaussianScale ε t • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hv : 0 < 1-t := by linarith
  have hb := boundedRectangleBoundary_map_product_intrinsic B
    (fun i (b : Fin n → Vector p) => b i) (h.thinned t ht ht1) hv
    (h.thinned_sum_unit_diagonal hunit t ht ht1) (standardGaussian p)
    (fun g => x+G.mulVec g) (measurable_const.add (measurable_mulVec G)) s z hd
  rw [seededSplitBaseDistribution_eq_bounded_shift]
  change _ ≤ _ at hb
  apply hb.trans
  have hE : 0 ≤ ∫ ω, ‖sumVector ξ ω‖ ∂μ := integral_nonneg (fun _ => norm_nonneg _)
  have hret := integral_norm_bernoulliArraySum_le h ht ht1
  have hc : (d+2*δ)/(1-t) ≤ 8*(d+δ) := by
    apply (div_le_iff₀ hv).mpr
    have hsδ : 0 ≤ d+δ := add_nonneg hd.le h.delta_nonneg
    nlinarith
  have hnonneg : 0 ≤ (d+2*δ)/(1-t) := div_nonneg (by linarith [h.delta_nonneg]) hv.le
  have hh := mul_le_mul hc hret (integral_nonneg (fun b => norm_nonneg (arraySum b)))
    (by nlinarith [h.delta_nonneg] : 0 ≤ 8*(d+δ))
  change ((d+2*δ)/(1-t)) * (∫ b, ‖arraySum b‖ ∂B) ≤ _ at hh
  have hh' := mul_le_mul_of_nonneg_left hh (show (0 : ℝ) ≤ 64 by norm_num)
  convert hh' using 1
  ring

/-- In the other part of the path the Gaussian scale is at least one half;
the regularization ε is allowed to be arbitrarily large. -/
theorem seededRectangleBoundary_intrinsic_gaussian_dominant
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hhalf : 2/3 < t) (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    (seededSplitBaseDistribution μ ξ A x ε t).real {q | q+z ∈ s.boundaryLayer d} ≤
      4 * d * gaussianMaximumMean A := by
  let B := bernoulliArrayLaw μ ξ t
  let a := seededSplitGaussianScale ε t
  let G := a • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have ha : 0 < a := seededSplitGaussianScale_pos (by linarith)
  have ha2 : a^2 = (t+ε)/2 := seededSplitGaussianScale_sq hε ht
  have haHalf : 1/2 ≤ a := by nlinarith
  have hdiag (j : Fin p) : (G*G.transpose) j j = a^2 := by
    rw [show G*G.transpose = a^2 • (A*A.transpose) by
      dsimp [G]; rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring]
    simp only [Matrix.smul_apply, smul_eq_mul, hA, hunit, mul_one]
  have hg := gaussianRectangleBoundary_intrinsic_product s G B
    (fun b => x+arraySum b) (measurable_const.add (measurable_arraySum p n)) z
    (sq_pos_of_pos ha) hd hdiag
  rw [seededSplitBaseDistribution_eq_gaussian_shift μ ξ h.measurable A x ε ht ht1]
  have hV : Measurable (fun q : Vector p × (Fin n → Vector p) => q.1+(x+arraySum q.2)) :=
    measurable_fst.add (measurable_const.add ((measurable_arraySum p n).comp measurable_snd))
  have hSet : MeasurableSet {q : Vector p | q+z ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
  rw [Measure.real, Measure.map_apply hV hSet]
  change ((gaussianLaw G).prod B).real {q | (q.1+(x+arraySum q.2))+z ∈ s.boundaryLayer d} ≤ _
  apply hg.trans
  rw [show gaussianMaximumMean G = a*gaussianMaximumMean A by
    dsimp [G]; rw [gaussianMaximumMean_smul, abs_of_pos ha]]
  have heq : (2*d/a^2)*(a*gaussianMaximumMean A) = (2*d/a)*gaussianMaximumMean A := by
    field_simp; ring
  rw [heq]
  apply mul_le_mul_of_nonneg_right _ (gaussianMaximumMean_nonneg A)
  apply (div_le_iff₀ ha).mpr
  nlinarith


theorem sqrt_dimensionLog_div_le_two {p : ℕ} (hp : 1 ≤ p) {v : ℝ}
    (hv : (1/4 : ℝ) ≤ v) :
    Real.sqrt (dimensionLog p/v) ≤ 2*Real.sqrt (dimensionLog p) := by
  have hv0 : 0 < v := by linarith
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hquot : dimensionLog p/v ≤ 4*dimensionLog p := by
    apply (div_le_iff₀ hv0).mpr
    have hh := mul_nonneg (by linarith : 0 ≤ 4*v-1) hL
    nlinarith
  apply Real.sqrt_le_iff.mpr
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hL]

/-- Both logarithmic alternatives are consequences of the printed intrinsic
and MGF estimates, with the same t=2/3 split as the manuscript. -/
theorem seededRectangleBoundary_logarithmic
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    (seededSplitBaseDistribution μ ξ A x ε t).real {q | q+z ∈ s.boundaryLayer d} ≤
      1024*(d+δ)*Real.sqrt (dimensionLog p) := by
  let B := bernoulliArrayLaw μ ξ t
  let a := seededSplitGaussianScale ε t
  let G := a • A
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  have hroot := Real.sqrt_nonneg (dimensionLog p)
  by_cases hhalf : t ≤ 2/3
  · have hv : 0 < 1-t := by linarith
    have hb := boundedRectangleBoundary_map_product_logarithmic hp B
      (fun i (b : Fin n → Vector p) => b i) (h.thinned t ht ht1) hv
      (h.thinned_sum_unit_diagonal hunit t ht ht1) (standardGaussian p)
      (fun g => x+G.mulVec g) (measurable_const.add (measurable_mulVec G)) s z hd
    rw [seededSplitBaseDistribution_eq_bounded_shift]
    apply hb.trans
    have hq := sqrt_dimensionLog_div_le_two hp (show (1/4 : ℝ) ≤ 1-t by linarith)
    calc
      _ ≤ 256*((d+2*δ)*(2*Real.sqrt (dimensionLog p))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hq (by linarith [h.delta_nonneg])) (by norm_num)
      _ = (512*(d+2*δ))*Real.sqrt (dimensionLog p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [h.delta_nonneg]) hroot
  · have ha : 0 < a := seededSplitGaussianScale_pos (by linarith)
    have ha2 : a^2 = (t+ε)/2 := seededSplitGaussianScale_sq hε ht
    have hdiag (j : Fin p) : (G*G.transpose) j j = a^2 := by
      rw [show G*G.transpose = a^2 • (A*A.transpose) by
        dsimp [G]; rw [Matrix.transpose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul]; congr 1; ring]
      simp only [Matrix.smul_apply, smul_eq_mul, hA, hunit, mul_one]
    have hg := gaussianRectangleBoundary_product_logarithmic hp s G B
      (fun b => x+arraySum b) (measurable_const.add (measurable_arraySum p n)) z
      (sq_pos_of_pos ha) hd hdiag
    rw [seededSplitBaseDistribution_eq_gaussian_shift μ ξ h.measurable A x ε ht ht1]
    have hV : Measurable (fun q : Vector p × (Fin n → Vector p) => q.1+(x+arraySum q.2)) :=
      measurable_fst.add (measurable_const.add ((measurable_arraySum p n).comp measurable_snd))
    have hSet : MeasurableSet {q : Vector p | q+z ∈ s.boundaryLayer d} :=
      (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
    rw [Measure.real, Measure.map_apply hV hSet]
    change ((gaussianLaw G).prod B).real {q | (q.1+(x+arraySum q.2))+z ∈ s.boundaryLayer d} ≤ _
    apply hg.trans
    have hq := sqrt_dimensionLog_div_le_two hp (show (1/4 : ℝ) ≤ a^2 by linarith)
    calc
      _ ≤ (4*d)*(2*Real.sqrt (dimensionLog p)) := mul_le_mul_of_nonneg_left hq (by positivity)
      _ = (8*d)*Real.sqrt (dimensionLog p) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (by linarith [h.delta_nonneg]) hroot

theorem intrinsicRectangleConcentration_seededSplitBase
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    IntrinsicRectangleConcentration (seededSplitBaseDistribution μ ξ A x ε t)
      intrinsicBoundaryConstant δ (intrinsicBoundaryCoefficient μ ξ A) := by
  intro s z d hd
  have hsδ : 0 ≤ d+δ := add_nonneg hd.le h.delta_nonneg
  have hlog := seededRectangleBoundary_logarithmic h hp hunit A hA x hε ht ht1 s z hd
  have hlog' := hlog.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right intrinsicBoundaryConstant_ge_1024 hsδ)
    (Real.sqrt_nonneg _))
  have hmax : (seededSplitBaseDistribution μ ξ A x ε t).real {q | q+z ∈ s.boundaryLayer d} ≤
      (intrinsicBoundaryConstant*(d+δ)) *
        (1+max (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)) := by
    by_cases hhalf : t ≤ 2/3
    · have hh := seededRectangleBoundary_intrinsic_bounded_dominant h hunit A x (ε := ε) ht hhalf s z hd
      apply hh.trans
      apply mul_le_mul (mul_le_mul_of_nonneg_right intrinsicBoundaryConstant_ge_1024 hsδ)
      · linarith [le_max_left (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
      · exact integral_nonneg (fun _ => norm_nonneg _)
      · exact mul_nonneg intrinsicBoundaryConstant_pos.le hsδ
    · have hh := seededRectangleBoundary_intrinsic_gaussian_dominant h hunit A hA x hε ht ht1
        (lt_of_not_ge hhalf) s z hd
      apply hh.trans
      apply mul_le_mul
      · exact mul_le_mul ((by norm_num : (4 : ℝ) ≤ 512).trans intrinsicBoundaryConstant_ge_512)
          (by linarith [h.delta_nonneg]) hd.le intrinsicBoundaryConstant_pos.le
      · linarith [le_max_right (∫ ω, ‖sumVector ξ ω‖ ∂μ) (gaussianMaximumMean A)]
      · exact gaussianMaximumMean_nonneg A
      · exact mul_nonneg intrinsicBoundaryConstant_pos.le hsδ
  have hh := combine_intrinsicBoundary μ ξ A hlog' hmax
  simpa only [intrinsicBoundaryConstant, mul_assoc, mul_left_comm, mul_comm] using hh

end
end RectangleCLTArxivV1
