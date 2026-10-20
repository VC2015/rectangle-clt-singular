import RectangleCLT.SharpMasterAssembly
import RectangleCLT.GaussianDerivativeScaling

/-! Variance normalization of the literal separate fourth-derivative suprema.
Only scalar dilation is used, so the Gaussian factor may be singular. -/

open Set

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem localConvolutionFourthSup_gaussian_sqrt_le
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m ≤
      (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup
        A (r / Real.sqrt t) ((Real.sqrt t)⁻¹ • x) 1 j k l m / t ^ 2 := by
  apply csSup_le
  · exact ⟨_, 0, by simpa only [Metric.mem_closedBall, dist_self] using hr, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    change |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + v) j k l m| ≤ _
    have hvnorm : ‖v‖ ≤ r := by
      simpa only [Metric.mem_closedBall, dist_zero_right] using hv
    have hnorm : ‖(Real.sqrt t)⁻¹ • v‖ ≤ r / Real.sqrt t := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr (Real.sqrt_pos.mpr ht))]
      calc
        _ ≤ (Real.sqrt t)⁻¹ * r :=
          mul_le_mul_of_nonneg_left hvnorm (inv_nonneg.mpr (Real.sqrt_nonneg t))
        _ = _ := by ring
    rw [s.convolutionFourthDerivative_gaussian_sqrt_scaleDown t ht, abs_div,
      abs_of_pos (pow_pos ht 2), smul_add]
    apply div_le_div_of_nonneg_right _ (pow_nonneg ht.le 2)
    simpa only [Real.sqrt_one, one_smul] using
      (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).abs_convolutionFourthDerivative_le_localSup
        A ((Real.sqrt t)⁻¹ • x) 1 hnorm j k l m

theorem sum_localConvolutionFourthSup_gaussian_sqrt_le
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (x : Vector p) {t : ℝ} (ht : 0 < t) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.localConvolutionFourthSup A r x t j k l m) ≤
      (∑ j, ∑ k, ∑ l, ∑ m,
        (s.scaleDown (Real.sqrt t) (Real.sqrt_pos.mpr ht)).localConvolutionFourthSup
          A (r / Real.sqrt t) ((Real.sqrt t)⁻¹ • x) 1 j k l m) / t ^ 2 := by
  simp only [Finset.sum_div]
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
    Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
      s.localConvolutionFourthSup_gaussian_sqrt_le A hr x ht j k l m

end RectangleCLT.FaceSmoother
