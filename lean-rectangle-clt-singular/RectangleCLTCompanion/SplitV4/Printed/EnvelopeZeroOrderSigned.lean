import RectangleCLTCompanion.SplitV4.Printed.EnvelopeZeroOrder
import Mathlib.MeasureTheory.Integral.Bochner.Set
import RectangleCLT.RectangleSmoothing

/-! A.1 order-zero counterexample with the complete signed face family
in dimension one, both thresholds finite and equal to one. Thus the
scope finding does not rely on deleting faces or infinite thresholds. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Unit signed normals +1,-1, offsets 1,1, and bandwidth h. -/
def signedTwoFaceSmoother (h x : ℝ) : ℝ :=
  1/(1+Real.exp ((x-1)/h)+Real.exp ((-x-1)/h))

theorem signedTwoFaceSmoother_eq_closedBox {h : ℝ} (hh : 0 < h) (x : ℝ) :
    signedTwoFaceSmoother h x =
      (RectangleCLT.FaceSmoother.closedBox (fun _ : Fin 1 => (-1 : ℝ)) (fun _ => (1 : ℝ)) h hh).F (fun _ => x) := by
  classical
  simp [signedTwoFaceSmoother, RectangleCLT.FaceSmoother.F, RectangleCLT.FaceSmoother.weights,
    RectangleCLT.FaceSmoother.closedBox, RectangleCLT.FaceSmoother.faceScore,
    RectangleCLT.FaceSmoother.normalDot, RectangleCLT.FaceWeights.F, RectangleCLT.FaceWeights.T,
    Fintype.sum_prod_type, Fin.sum_univ_succ, add_assoc, add_comm, add_left_comm]

theorem signedTwoFaceSmoother_pos (h x : ℝ) : 0 < signedTwoFaceSmoother h x := by
  unfold signedTwoFaceSmoother
  positivity

theorem signedTwoFaceSmoother_le_one (h x : ℝ) : signedTwoFaceSmoother h x ≤ 1 := by
  unfold signedTwoFaceSmoother
  exact (div_le_one (by positivity)).mpr (by linarith [Real.exp_pos ((x-1)/h), Real.exp_pos ((-x-1)/h)])

theorem integrable_signedTwoFaceSmoother (μ : Measure ℝ) [IsFiniteMeasure μ] (h : ℝ) :
    Integrable (signedTwoFaceSmoother h) μ := by
  have hm : Measurable (signedTwoFaceSmoother h) := by unfold signedTwoFaceSmoother; fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (signedTwoFaceSmoother_pos _ _)]
    exact signedTwoFaceSmoother_le_one _ _

theorem signedTwoFaceSmoother_lower_on_interval {h : ℝ} (hh : 0 < h) {x : ℝ}
    (hx : x ∈ Icc (-1 : ℝ) 1) : (1/3 : ℝ) ≤ signedTwoFaceSmoother h x := by
  have he1 : Real.exp ((x-1)/h) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [hx.2]) hh.le)
  have he2 : Real.exp ((-x-1)/h) ≤ 1 := Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg (by linarith [hx.1]) hh.le)
  unfold signedTwoFaceSmoother
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

theorem gaussian_unit_interval_mass_pos : 0 < (gaussianReal 0 1).real (Icc (-1 : ℝ) 1) := by
  have hp : 0 < ∫ x in Icc (-1 : ℝ) 1, gaussianPDFReal 0 1 x := by
    apply (setIntegral_pos_iff_support_of_nonneg_ae
      (ae_of_all _ (gaussianPDFReal_nonneg 0 1)) (integrable_gaussianPDFReal 0 1).integrableOn).mpr
    have hs : Function.support (gaussianPDFReal 0 1) = univ := by
      ext x
      simp only [Function.mem_support, mem_univ, iff_true]
      exact (gaussianPDFReal_pos 0 1 x (by norm_num)).ne'
    rw [hs,univ_inter]
    norm_num
  unfold Measure.real
  rw [gaussianReal_apply_eq_integral 0 (by norm_num : (1 : NNReal) ≠ 0), ENNReal.toReal_ofReal hp.le]
  exact hp

theorem integral_signedTwoFaceSmoother_lower {h : ℝ} (hh : 0 < h) :
    (gaussianReal 0 1).real (Icc (-1 : ℝ) 1)/3 ≤
      ∫ x, signedTwoFaceSmoother h x ∂gaussianReal 0 1 := by
  have hi := integrable_signedTwoFaceSmoother (gaussianReal 0 1) h
  have hbound : ∀ x : ℝ, (Icc (-1 : ℝ) 1).indicator (fun _ => (1/3 : ℝ)) x ≤ signedTwoFaceSmoother h x := by
    intro x
    by_cases hx : x ∈ Icc (-1 : ℝ) 1
    · simpa only [indicator_of_mem hx] using signedTwoFaceSmoother_lower_on_interval hh hx
    · simp only [indicator_of_not_mem hx]
      exact (signedTwoFaceSmoother_pos _ _).le
  have hle := integral_mono ((integrable_const (1/3 : ℝ)).indicator measurableSet_Icc) hi hbound
  simpa only [integral_indicator measurableSet_Icc, integral_const, measureReal_restrict_apply_univ,
    smul_eq_mul, div_eq_mul_inv, one_mul] using hle

/-- A literal full signed-face q=0 averaged bound is impossible even
with fixed finite thresholds and a centered unit-variance Gaussian. -/
theorem no_uniform_signed_zero_order_averaged_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      (∫ x, signedTwoFaceSmoother h x ∂gaussianReal 0 1) ≤ C*h := by
  rintro ⟨C,hC,hbound⟩
  let b := (gaussianReal 0 1).real (Icc (-1 : ℝ) 1)/3
  have hb : 0 < b := div_pos gaussian_unit_interval_mass_pos (by norm_num)
  let h := b/(2*(C+1))
  have hh : 0 < h := by dsimp [h]; positivity
  have hupper := hbound h hh
  have hlower := integral_signedTwoFaceSmoother_lower hh
  change b ≤ ∫ x, signedTwoFaceSmoother h x ∂gaussianReal 0 1 at hlower
  have hsmall : C*h < b := by
    dsimp only [h]
    rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2*(C+1))]
    nlinarith
  linarith

theorem no_uniform_closedBox_zero_order_averaged_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ (h : ℝ) (hh : 0 < h),
      (∫ x, (RectangleCLT.FaceSmoother.closedBox (fun _ : Fin 1 => (-1 : ℝ))
        (fun _ => (1 : ℝ)) h hh).F (fun _ => x) ∂gaussianReal 0 1) ≤ C*h := by
  rintro ⟨C,hC,hbound⟩
  apply no_uniform_signed_zero_order_averaged_bound
  refine ⟨C,hC,?_⟩
  intro h hh
  simpa only [signedTwoFaceSmoother_eq_closedBox hh] using hbound h hh

end
end RectangleCLT.Companion.SplitV4.Printed
