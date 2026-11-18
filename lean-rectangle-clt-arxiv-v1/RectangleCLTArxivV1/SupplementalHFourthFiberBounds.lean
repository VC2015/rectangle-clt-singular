import RectangleCLTArxivV1.SupplementalHFourthTubes
import RectangleCLTArxivV1.SupplementalHSurfaceGeometry

/-! Actual weighted Green coefficients are paid for by actual adaptive
fourth-radius normal fibers, uniformly at angular degeneracies. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT.Companion.SignedSurface
open scoped InnerProductSpace
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def supplementalHWeightedRidgeCoefficient (u v z : E) : ℝ :=
  |⟪u,z⟫_ℝ| *⟪supplementalHRidgeConormal u v,z⟫_ℝ+
    |⟪v,z⟫_ℝ| *⟪supplementalHRidgeConormal v u,z⟫_ℝ

/-- Exact coefficient comparison for the weighted paired ridge term.
The only radius input is the ordinary norm of its normal-space point. -/
theorem adaptive_weighted_ridge_pair_fourth_bound
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u v z : E) (hu : ‖u‖=1) (hv : ‖v‖=1) (hp : u+v≠0) (hm : u-v≠0)
    (hz : ‖z‖≤R x) :
    |supplementalHWeightedRidgeCoefficient u v z| *gaussianKernel z≤
      (8192*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle u v (1/(4*R x)),
        R (x+ridgeDisplacement u v st)^4*gaussianKernel (z+ridgeDisplacement u v st)
          ∂((volume : Measure ℝ).prod volume)) := by
  have hb : |⟪z,bisector u v⟫_ℝ|≤R x := by
    exact (abs_real_inner_le_norm _ _).trans (by rw [norm_bisector u v hp,mul_one]; exact hz)
  have hc : |⟪z,differenceDirection u v⟫_ℝ|≤R x := by
    exact (abs_real_inner_le_norm _ _).trans (by rw [norm_differenceDirection u v hm,mul_one]; exact hz)
  have hf := adaptive_ridge_gaussian_integral_lower_fourth R hRm hR hRadd x u v z hu hv hp hm hb hc
  have hcoef : |supplementalHWeightedRidgeCoefficient u v z|≤2*‖u-v‖*R x^2 :=
    (supplementalH_weighted_ridge_pair_le u v z hu hv hp hm).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hz 2)
        (mul_nonneg (by norm_num) (norm_nonneg _)))
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by
    rw [←Real.exp_add]
    norm_num
  calc
    _ ≤ (2*‖u-v‖*R x^2)*gaussianKernel z :=
      mul_le_mul_of_nonneg_right hcoef (Real.exp_nonneg _)
    _ = (8192*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^2*‖u-v‖/4096)) := by
      calc
        _ = 2*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*‖u-v‖*R x^2*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

/-- The scalar cubic coefficient on a facet is controlled by the cubic
radius left by the genuine fourth-weight normal fiber. -/
theorem abs_weighted_facet_coefficient_le {R b : ℝ} (hR : 1≤R) (hb : |b|≤R) :
    abs (|b| *(b^2-1))≤2*R^3 := by
  have hR0 : 0≤R := zero_le_one.trans hR
  have hsq : b^2≤R^2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg b) hb 2
  have habs : |b^2-1|≤b^2+1 := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (sq_nonneg _),abs_one])
  calc
    _ = |b| *|b^2-1| := by rw [abs_mul,abs_abs]
    _ ≤ R*(b^2+1) := mul_le_mul hb habs (abs_nonneg _) hR0
    _ ≤ R*(R^2+1) := mul_le_mul_of_nonneg_left (add_le_add_right hsq 1) hR0
    _ ≤ 2*R^3 := by
      have h : 0≤R*(R^2-1) := mul_nonneg hR0 (by nlinarith)
      nlinarith [h]

/-- Actual weighted facet coefficient-to-fiber bound. -/
theorem adaptive_weighted_facet_fourth_bound
    (R : E → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (x u z : E) (hu : ‖u‖=1) (hz : |⟪z,u⟫_ℝ|≤R x) :
    abs (|⟪z,u⟫_ℝ| *(⟪z,u⟫_ℝ^2-1))*gaussianKernel z≤
      (128*Real.exp ((3:ℝ)/2))*(∫ t in Set.Icc (0:ℝ) (1/(4*R x)),
        R (x+t • u)^4*gaussianKernel (z+t • u)) := by
  have hf := adaptive_facet_gaussian_integral_lower_fourth R hRm hR hRadd x u z hu hz
  have hexp : Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2)=1 := by
    rw [←Real.exp_add]
    norm_num
  calc
    _ ≤ (2*R x^3)*gaussianKernel z :=
      mul_le_mul_of_nonneg_right (abs_weighted_facet_coefficient_le (hR x) hz) (Real.exp_nonneg _)
    _ = (128*Real.exp ((3:ℝ)/2))*(Real.exp (-(3:ℝ)/2)*gaussianKernel z*(R x^3/64)) := by
      calc
        _ = 2*(Real.exp ((3:ℝ)/2)*Real.exp (-(3:ℝ)/2))*R x^3*gaussianKernel z := by rw [hexp]; ring
        _ = _ := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hf (by positivity)

end
end RectangleCLTArxivV1
