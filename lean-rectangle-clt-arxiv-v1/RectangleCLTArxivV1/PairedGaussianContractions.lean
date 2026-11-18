import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import RectangleCLTArxivV1.EnvelopeThresholdIntegration
import RectangleCLTCompanion.SplitV4.GaussianDerivativeContractions

/-!
# Intrinsic Gaussian envelopes and weighted derivative contractions

The Gaussian expected maximum is that of the actual covariance factor.
Arbitrary dependent random centers and coefficients remain allowed; only
independence of the Gaussian factor is used. No comparison inequality is an
input. These estimates replace the logarithmic coefficient in the paired
interpolation proof of Appendix E.
-/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- The printed threshold-window proof applied to actual Gaussian layers. -/
theorem gaussian_smallerEnvelope_intrinsic {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p) :
    (∫ g, s.F (g+r)*(1-s.F (g+r)) ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * s.bandwidth * (gaussianMaximumMean A / v) := by
  let W : Vector p → Vector p := fun x => x+r
  have hW : Measurable W := measurable_id.add_const r
  let ν := (gaussianLaw A).map W
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hW.aemeasurable
  have hbound (t : FaceSmoother p) :
      ν.real {x | (∀ f ∈ t.faces, t.faceScore f x ≤ s.bandwidth) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -s.bandwidth)} ≤
      (2*s.bandwidth/v)*gaussianMaximumMean A := by
    have hset : {x | (∀ f ∈ t.faces, t.faceScore f x ≤ s.bandwidth) ∧
        ¬(∀ f ∈ t.faces, t.faceScore f x ≤ -s.bandwidth)} = t.boundaryLayer s.bandwidth := by
      ext x
      exact (t.mem_boundaryLayer_iff_score s.bandwidth x).symm
    rw [hset]
    change ((gaussianLaw A).map W).real (t.boundaryLayer s.bandwidth) ≤ _
    rw [Measure.real, Measure.map_apply hW (t.measurableSet_boundaryLayer s.bandwidth)]
    exact gaussianRectangleBoundary_intrinsic_fixed_shift t A r hv s.bandwidth_pos hdiag
  have hb := integral_smallerEnvelope_le_of_matching_boundary_printed s ν (fun t _ => hbound t)
  rw [integral_map hW.aemeasurable
    (s.continuous_F.mul (continuous_const.sub s.continuous_F)).aestronglyMeasurable] at hb
  have he : Real.exp 1 ≤ Real.exp (3 / 2 : ℝ) := Real.exp_le_exp.mpr (by norm_num)
  have hh := mul_le_mul_of_nonneg_right he
    (mul_nonneg s.bandwidth_pos.le (div_nonneg (gaussianMaximumMean_nonneg A) hv.le))
  apply hb.trans
  convert hh using 1 <;> field_simp [hv.ne'] <;> ring

/-- The expected maximum of the scaled Gaussian has exactly the scale
needed by the endpoint singularity in the Slepian path. -/
theorem gaussianMaximumMean_slepian_scale_div {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : t < 1) :
    gaussianMaximumMean (Real.sqrt (1-t) • A) / (1-t) =
      gaussianMaximumMean A / Real.sqrt (1-t) := by
  have hv : 0 < 1-t := sub_pos.mpr ht
  have ha : 0 < Real.sqrt (1-t) := Real.sqrt_pos.mpr hv
  rw [gaussianMaximumMean_smul, abs_of_nonneg ha.le]
  calc
    _ = (Real.sqrt (1-t) * gaussianMaximumMean A) / Real.sqrt (1-t) ^ 2 := by
      rw [Real.sq_sqrt hv.le]
    _ = _ := by
      field_simp [ha.ne']
      calc
        _ = gaussianMaximumMean A * Real.sqrt (1-t) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hv.le]

theorem intrinsic_gaussian_gradient_contraction {p : ℕ} (_hp : 1 ≤ p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r b : Vector p) :
    (∫ g, |(smootherC4Test s).gradient (g + r) b| ∂gaussianLaw A) ≤
      Real.exp (3 / 2 : ℝ) * (gaussianMaximumMean A / v) * ‖b‖ := by
  have hi := (smootherC4Test s).integrable_gradient_eval (gaussianLaw A)
    (fun g => g + r) (fun _ => b) (measurable_id.add_const r) measurable_const ‖b‖ (fun _ => le_rfl)
  have hΨ := s.integrable_smallerEnvelope (fun g : Vector p => g + r) (measurable_id.add_const r)
    (μ := gaussianLaw A)
  calc
    _ ≤ ∫ g, (‖b‖ / s.bandwidth) * (s.F (g + r) * (1 - s.F (g + r))) ∂gaussianLaw A :=
      integral_mono_ae hi.abs (hΨ.const_mul _) (ae_of_all _ (fun g => abs_smoother_gradient_le_envelope s _ b))
    _ = (‖b‖ / s.bandwidth) * ∫ g, s.F (g + r) * (1 - s.F (g + r)) ∂gaussianLaw A :=
      integral_const_mul _ _
    _ ≤ (‖b‖ / s.bandwidth) *
        (Real.exp (3 / 2 : ℝ) * s.bandwidth * (gaussianMaximumMean A / v)) :=
      mul_le_mul_of_nonneg_left (gaussian_smallerEnvelope_intrinsic s A hv hdiag r)
        (div_nonneg (norm_nonneg b) s.bandwidth_pos.le)
    _ = _ := by field_simp [ne_of_gt s.bandwidth_pos]; ring

theorem intrinsic_gaussian_hessian_contraction {p : ℕ} (_hp : 1 ≤ p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (r : Vector p)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    (∫ g, |(smootherC4Test s).hessianTrace M (g + r)| ∂gaussianLaw A) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth) * (gaussianMaximumMean A / v) * matrixMaxEntryNorm M := by
  have hi := (smootherC4Test s).integrable_hessianTrace (gaussianLaw A)
    (fun g => g + r) (measurable_id.add_const r) M
  have hΨ := s.integrable_smallerEnvelope (fun g : Vector p => g + r) (measurable_id.add_const r)
    (μ := gaussianLaw A)
  calc
    _ ≤ ∫ g, (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        (s.F (g + r) * (1 - s.F (g + r))) ∂gaussianLaw A :=
      integral_mono_ae hi.abs (hΨ.const_mul _) (ae_of_all _ (fun g => abs_smoother_hessianTrace_le_envelope s _ M))
    _ = (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        ∫ g, s.F (g + r) * (1 - s.F (g + r)) ∂gaussianLaw A := integral_const_mul _ _
    _ ≤ (3 * matrixMaxEntryNorm M / s.bandwidth ^ 2) *
        (Real.exp (3 / 2 : ℝ) * s.bandwidth * (gaussianMaximumMean A / v)) :=
      mul_le_mul_of_nonneg_left (gaussian_smallerEnvelope_intrinsic s A hv hdiag r)
        (by unfold matrixMaxEntryNorm; positivity)
    _ = _ := by field_simp [ne_of_gt s.bandwidth_pos]; ring


theorem intrinsic_weighted_gaussian_gradient_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (R b : Ω → Vector p)
    (hR : Measurable R) (hb : Measurable b) (hbi : Integrable (fun ω => ‖b ω‖) μ) :
    (∫ z : Ω × Vector p, |(smootherC4Test s).gradient (z.2 + R z.1) (b z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (Real.exp (3 / 2 : ℝ) * (gaussianMaximumMean A / v)) * ∫ ω, ‖b ω‖ ∂μ := by
  have hi := integrable_weighted_gaussian_gradient s μ A R b hR hb hbi
  calc
    _ = ∫ ω, ∫ g, |(smootherC4Test s).gradient (g + R ω) (b ω)| ∂gaussianLaw A ∂μ :=
      integral_prod _ hi.abs
    _ ≤ ∫ ω, (Real.exp (3 / 2 : ℝ) * (gaussianMaximumMean A / v)) * ‖b ω‖ ∂μ :=
      integral_mono_ae hi.abs.integral_prod_left (hbi.const_mul _)
        (ae_of_all _ (fun ω => intrinsic_gaussian_gradient_contraction hp s A hv hdiag (R ω) (b ω)))
    _ = _ := integral_const_mul _ _


theorem intrinsic_weighted_gaussian_hessian_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) (R : Ω → Vector p)
    (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hR : Measurable R)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) :
    (∫ z : Ω × Vector p, |(smootherC4Test s).hessianTrace (M z.1) (z.2 + R z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * (gaussianMaximumMean A / v)) *
        ∫ ω, matrixMaxEntryNorm (M ω) ∂μ := by
  have hi := integrable_weighted_gaussian_hessian s μ A R M hR hM hMi
  calc
    _ = ∫ ω, ∫ g, |(smootherC4Test s).hessianTrace (M ω) (g + R ω)| ∂gaussianLaw A ∂μ :=
      integral_prod _ hi.abs
    _ ≤ ∫ ω, (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * (gaussianMaximumMean A / v)) *
        matrixMaxEntryNorm (M ω) ∂μ :=
      integral_mono_ae hi.abs.integral_prod_left (hMi.const_mul _)
        (ae_of_all _ (fun ω => intrinsic_gaussian_hessian_contraction hp s A hv hdiag (R ω) (M ω)))
    _ = _ := integral_const_mul _ _


theorem intrinsic_slepian_weighted_gradient_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (W b : Ω → Vector p) (hW : Measurable W) (hb : Measurable b)
    (hbi : Integrable (fun ω => ‖b ω‖) μ) {t : ℝ} (ht : t < 1) :
    (∫ z, |(smootherC4Test s).gradient (C4Test.slepianPoint W t z) (b z.1)|
      ∂μ.prod (gaussianLaw A)) ≤
      (Real.exp (3 / 2 : ℝ) * (gaussianMaximumMean A / Real.sqrt (1-t))) * ∫ ω, ‖b ω‖ ∂μ := by
  have hi := integrable_weighted_gaussian_gradient s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) b (measurable_const.smul hW) hb hbi
  have he := integral_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi.abs
  have hbnd := intrinsic_weighted_gaussian_gradient_contraction hp s μ (Real.sqrt (1 - t) • A)
    (sub_pos.mpr ht) (slepian_scaled_factor_diagonal A hdiag ht.le)
    (fun ω => Real.sqrt t • W ω) b (measurable_const.smul hW) hb hbi
  rw [gaussianMaximumMean_slepian_scale_div A ht] at hbnd
  simpa only [C4Test.slepianPoint, add_comm] using he.trans_le hbnd


theorem intrinsic_slepian_weighted_hessian_contraction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (W : Ω → Vector p) (M : Ω → Matrix (Fin p) (Fin p) ℝ) (hW : Measurable W)
    (hM : ∀ j k, Measurable (fun ω => M ω j k))
    (hMi : Integrable (fun ω => matrixMaxEntryNorm (M ω)) μ) {t : ℝ} (ht : t < 1) :
    (∫ z, |(smootherC4Test s).hessianTrace (M z.1) (C4Test.slepianPoint W t z)|
      ∂μ.prod (gaussianLaw A)) ≤
      (3 * Real.exp (3 / 2 : ℝ) / s.bandwidth * (gaussianMaximumMean A / Real.sqrt (1-t))) *
        ∫ ω, matrixMaxEntryNorm (M ω) ∂μ := by
  have hi := integrable_weighted_gaussian_hessian s μ (Real.sqrt (1 - t) • A)
    (fun ω => Real.sqrt t • W ω) M (measurable_const.smul hW) hM hMi
  have he := integral_scaled_gaussian_product μ A (Real.sqrt (1 - t)) _ hi.abs
  have hbnd := intrinsic_weighted_gaussian_hessian_contraction hp s μ (Real.sqrt (1 - t) • A)
    (sub_pos.mpr ht) (slepian_scaled_factor_diagonal A hdiag ht.le)
    (fun ω => Real.sqrt t • W ω) M (measurable_const.smul hW) hM hMi
  rw [gaussianMaximumMean_slepian_scale_div A ht] at hbnd
  simpa only [C4Test.slepianPoint, add_comm] using he.trans_le hbnd

end
end RectangleCLTArxivV1
