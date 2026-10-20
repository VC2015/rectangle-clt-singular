import RectangleCLT.SmootherConvolution
import RectangleCLT.Statement

/-! Scaling the actual Gaussian convolutions of rectangle smoothers.
The Gaussian factor may be singular: only the scalar dilation is positive. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

/-- Divide the rectangle offsets and smoothing bandwidth by a positive scalar. -/
def scaleDown (a : ℝ) (ha : 0 < a) : FaceSmoother p where
  faces := s.faces
  offsets f := s.offsets f / a
  bandwidth := s.bandwidth / a
  bandwidth_pos := div_pos s.bandwidth_pos ha

@[simp] theorem scaleDown_faces (a : ℝ) (ha : 0 < a) : (s.scaleDown a ha).faces = s.faces := rfl
@[simp] theorem scaleDown_offsets (a : ℝ) (ha : 0 < a) (f : Face p) :
    (s.scaleDown a ha).offsets f = s.offsets f / a := rfl
@[simp] theorem scaleDown_bandwidth (a : ℝ) (ha : 0 < a) :
    (s.scaleDown a ha).bandwidth = s.bandwidth / a := rfl

private theorem scaleDown_normalDot (a : ℝ) (f : Face p) (x : Vector p) :
    normalDot f (a⁻¹ • x) = normalDot f x / a := by
  cases hb : f.2 <;> simp only [normalDot, hb, Bool.false_eq_true, ↓reduceIte,
    Pi.smul_apply, smul_eq_mul, div_eq_mul_inv] <;> ring

private theorem weights_ext {u v : FaceWeights p} (h : ∀ f, u.weight f = v.weight f) : u = v := by
  cases u with | mk uw hu => cases v with | mk vw hv =>
    have he : uw = vw := funext h
    cases he
    rfl

/-- The normalized exponential face weights are unchanged by simultaneous
scaling of the point, offsets, and bandwidth. -/
theorem weights_scaleDown (a : ℝ) (ha : 0 < a) (x : Vector p) :
    (s.scaleDown a ha).weights (a⁻¹ • x) = s.weights x := by
  apply weights_ext
  intro f
  simp only [weights, scaleDown_faces]
  split_ifs with hf
  · congr 1
    simp only [faceScore, scaleDown_offsets, scaleDown_bandwidth, scaleDown_normalDot]
    field_simp
  · rfl

@[simp] theorem F_scaleDown (a : ℝ) (ha : 0 < a) (x : Vector p) :
    (s.scaleDown a ha).F (a⁻¹ • x) = s.F x := by
  simp only [F, weights_scaleDown]

/-- Actual third coordinate derivatives acquire the scalar factor `a⁻³`. -/
theorem mixedThirdDerivativeF_scaleDown (a : ℝ) (ha : 0 < a) (x : Vector p)
    (j k l : Fin p) :
    s.mixedThirdDerivativeF x j k l =
      (s.scaleDown a ha).mixedThirdDerivativeF (a⁻¹ • x) j k l / a ^ 3 := by
  rw [s.mixedThirdDerivativeF_eq, (s.scaleDown a ha).mixedThirdDerivativeF_eq,
    F_scaleDown, weights_scaleDown, scaleDown_bandwidth]
  field_simp [ne_of_gt ha, ne_of_gt s.bandwidth_pos]
  ring

/-- Actual fourth coordinate derivatives acquire the scalar factor `a⁻⁴`. -/
theorem mixedFourthDerivativeF_scaleDown (a : ℝ) (ha : 0 < a) (x : Vector p)
    (j k l m : Fin p) :
    s.mixedFourthDerivativeF x j k l m =
      (s.scaleDown a ha).mixedFourthDerivativeF (a⁻¹ • x) j k l m / a ^ 4 := by
  rw [s.mixedFourthDerivativeF_eq, (s.scaleDown a ha).mixedFourthDerivativeF_eq,
    F_scaleDown, weights_scaleDown, scaleDown_bandwidth]
  field_simp [ne_of_gt ha, ne_of_gt s.bandwidth_pos]
  ring

private theorem scaled_argument (a : ℝ) (ha : 0 < a)
    (A : Matrix (Fin p) (Fin p) ℝ) (x z : Vector p) :
    a⁻¹ • (x + (a • A).mulVec z) = a⁻¹ • x + A.mulVec z := by
  rw [Matrix.smul_mulVec_assoc, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt ha), one_smul]

private theorem integral_gaussianLaw_of_continuous
    (A : Matrix (Fin p) (Fin p) ℝ) (G : Vector p → ℝ) (hG : Continuous G) :
    (∫ z, G z ∂gaussianLaw A) = ∫ z, G (A.mulVec z) ∂standardGaussian p :=
  integral_map (measurable_mulVec A).aemeasurable hG.aestronglyMeasurable

/-- Exact scaling of an actual third derivative of a Gaussian convolution.
No inverse or positive definiteness of the Gaussian matrix is required. -/
theorem convolutionThirdDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw (a • A)) x j k l =
      (s.scaleDown a ha).convolutionThirdDerivative (gaussianLaw A) (a⁻¹ • x) j k l / a ^ 3 := by
  rw [s.convolutionThirdDerivative_eq_integral,
    (s.scaleDown a ha).convolutionThirdDerivative_eq_integral]
  rw [integral_gaussianLaw_of_continuous (a • A)
    (fun z => s.mixedThirdDerivativeF (x + z) j k l)
    ((s.continuous_thirdDerivative j k l).comp (continuous_const.add continuous_id))]
  rw [integral_gaussianLaw_of_continuous A
    (fun z => (s.scaleDown a ha).mixedThirdDerivativeF (a⁻¹ • x + z) j k l)
    (((s.scaleDown a ha).continuous_thirdDerivative j k l).comp
      (continuous_const.add continuous_id))]
  rw [← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [s.mixedThirdDerivativeF_scaleDown a ha, scaled_argument a ha])

/-- Exact fourth-derivative Gaussian scaling, valid also for singular factors. -/
theorem convolutionFourthDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw (a • A)) x j k l m =
      (s.scaleDown a ha).convolutionFourthDerivative (gaussianLaw A) (a⁻¹ • x) j k l m / a ^ 4 := by
  rw [s.convolutionFourthDerivative_eq_integral,
    (s.scaleDown a ha).convolutionFourthDerivative_eq_integral]
  rw [integral_gaussianLaw_of_continuous (a • A)
    (fun z => s.mixedFourthDerivativeF (x + z) j k l m)
    ((s.continuous_fourthDerivative j k l m).comp (continuous_const.add continuous_id))]
  rw [integral_gaussianLaw_of_continuous A
    (fun z => (s.scaleDown a ha).mixedFourthDerivativeF (a⁻¹ • x + z) j k l m)
    (((s.scaleDown a ha).continuous_fourthDerivative j k l m).comp
      (continuous_const.add continuous_id))]
  rw [← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun z => by
    dsimp only
    rw [s.mixedFourthDerivativeF_scaleDown a ha, scaled_argument a ha])

/-- Exact scaling of the summed absolute third derivative tensor. -/
theorem sum_abs_convolutionThirdDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative (gaussianLaw (a • A)) x j k l|) =
      (∑ j, ∑ k, ∑ l,
        |(s.scaleDown a ha).convolutionThirdDerivative (gaussianLaw A) (a⁻¹ • x) j k l|) /
          a ^ 3 := by
  simp_rw [s.convolutionThirdDerivative_gaussian_scaleDown a ha, abs_div,
    abs_of_pos (pow_pos ha 3), Finset.sum_div]

/-- Exact scaling of the summed absolute fourth derivative tensor. -/
theorem sum_abs_convolutionFourthDerivative_gaussian_scaleDown
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, |s.convolutionFourthDerivative (gaussianLaw (a • A)) x j k l m|) =
      (∑ j, ∑ k, ∑ l, ∑ m,
        |(s.scaleDown a ha).convolutionFourthDerivative (gaussianLaw A) (a⁻¹ • x) j k l m|) /
          a ^ 4 := by
  simp_rw [s.convolutionFourthDerivative_gaussian_scaleDown a ha, abs_div,
    abs_of_pos (pow_pos ha 4), Finset.sum_div]

/-- A local envelope for the normalized convolution gives a local envelope
for the scaled Gaussian convolution at the original spatial radius. -/
theorem abs_convolutionFourthDerivative_gaussian_scaled_shift_le
    (a : ℝ) (ha : 0 < a) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    (H : Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ z : Vector p, ‖z‖ ≤ s.bandwidth / a → ∀ j k l m,
      |(s.scaleDown a ha).convolutionFourthDerivative (gaussianLaw A)
        (a⁻¹ • x + z) j k l m| ≤ H j k l m)
    {z : Vector p} (hz : ‖z‖ ≤ s.bandwidth) (j k l m : Fin p) :
    |s.convolutionFourthDerivative (gaussianLaw (a • A)) (x + z) j k l m| ≤
      H j k l m / a ^ 4 := by
  have hscale : ‖a⁻¹ • z‖ ≤ s.bandwidth / a := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
    calc
      _ ≤ a⁻¹ * s.bandwidth := mul_le_mul_of_nonneg_left hz (inv_nonneg.mpr ha.le)
      _ = _ := by ring
  rw [s.convolutionFourthDerivative_gaussian_scaleDown a ha, abs_div,
    abs_of_pos (pow_pos ha 4), smul_add]
  exact div_le_div_of_nonneg_right (hH _ hscale j k l m) (pow_nonneg ha.le 4)

private theorem sqrt_cube_eq_rpow {v : ℝ} (hv : 0 < v) :
    (Real.sqrt v) ^ 3 = v ^ (3 / 2 : ℝ) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul_natCast hv.le (1 / 2 : ℝ) 3]
  norm_num

/-- Variance-time form of the exact third-derivative scaling identity. -/
theorem convolutionThirdDerivative_gaussian_sqrt_scaleDown
    (v : ℝ) (hv : 0 < v) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l : Fin p) :
    s.convolutionThirdDerivative (gaussianLaw (Real.sqrt v • A)) x j k l =
      (s.scaleDown (Real.sqrt v) (Real.sqrt_pos.mpr hv)).convolutionThirdDerivative
        (gaussianLaw A) ((Real.sqrt v)⁻¹ • x) j k l / v ^ (3 / 2 : ℝ) := by
  rw [s.convolutionThirdDerivative_gaussian_scaleDown, sqrt_cube_eq_rpow hv]

/-- Variance-time form of the exact fourth-derivative scaling identity. -/
theorem convolutionFourthDerivative_gaussian_sqrt_scaleDown
    (v : ℝ) (hv : 0 < v) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthDerivative (gaussianLaw (Real.sqrt v • A)) x j k l m =
      (s.scaleDown (Real.sqrt v) (Real.sqrt_pos.mpr hv)).convolutionFourthDerivative
        (gaussianLaw A) ((Real.sqrt v)⁻¹ • x) j k l m / v ^ 2 := by
  rw [s.convolutionFourthDerivative_gaussian_scaleDown]
  congr 1
  nlinarith [Real.sq_sqrt hv.le]

end

end RectangleCLT.FaceSmoother
