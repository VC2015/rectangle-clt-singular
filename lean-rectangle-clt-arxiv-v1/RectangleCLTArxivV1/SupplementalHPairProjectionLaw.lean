import RectangleCLTArxivV1.SupplementalHPairReference
import RectangleCLTCompanion.SplitV4.Printed.GaussianOrthogonalIndependence

/-! Actual two-coordinate Gaussian transport for the pair reference.
The complementary unit coordinate is constructed from the original normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def hReferencePairComplement {r : ℕ} (u v : Vector r) : Vector r :=
  (Real.sqrt (1-(faceDot u v)^2))⁻¹ • gaussianNormalProjection u v

theorem hReferencePairComplement_orthogonal {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u=1) : faceDot u (hReferencePairComplement u v)=0 := by
  rw [hReferencePairComplement,threshold_faceDot_smul_right,
    gaussianNormalProjection_orthogonal u v hu,mul_zero]

theorem hReferencePairComplement_unit {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    vectorNormSq (hReferencePairComplement u v)=1 := by
  have hν : 0 < Real.sqrt (1-(faceDot u v)^2) := Real.sqrt_pos.mpr (by linarith)
  have hres : vectorNormSq (gaussianNormalProjection u v)=1-(faceDot u v)^2 := by
    have he : gaussianNormalProjection u v=SignedSurface.gaussianSectionPoint u 0 v := by
      simp [gaussianNormalProjection,SignedSurface.gaussianSectionPoint,
        SignedSurface.gaussianSectionResidual,faceDot_comm u v]
    rw [he,SignedSurface.vectorNormSq_gaussianSectionPoint u 0 hu v,hv]
    ring
  have hscale : vectorNormSq (hReferencePairComplement u v)=
      ((Real.sqrt (1-(faceDot u v)^2))⁻¹)^2*vectorNormSq (gaussianNormalProjection u v) := by
    unfold hReferencePairComplement vectorNormSq
    simp only [Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
  rw [hscale,hres,←Real.sq_sqrt (show 0≤1-(faceDot u v)^2 by linarith)]
  field_simp

theorem hReferencePairComplement_reconstruct {r : ℕ} (u v : Vector r)
    (hρ : (faceDot u v)^2<1) :
    v=faceDot u v • u+Real.sqrt (1-(faceDot u v)^2) • hReferencePairComplement u v := by
  have hν : 0 < Real.sqrt (1-(faceDot u v)^2) := Real.sqrt_pos.mpr (by linarith)
  rw [hReferencePairComplement,smul_smul,mul_inv_cancel₀ hν.ne',one_smul,
    gaussianNormalProjection,faceDot_comm v u]
  abel

/-- The two remaining Gaussian coordinates have the actual independent
standard normal product law. -/
theorem hReferencePair_unit_coordinates_map {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1) :
    (standardGaussian r).map (fun g => (faceDot u g,faceDot (hReferencePairComplement u v) g)) =
      (gaussianReal 0 1).prod (gaussianReal 0 1) := by
  have horth : faceDot (hReferencePairComplement u v) u=0 := by
    rw [faceDot_comm]
    exact hReferencePairComplement_orthogonal u v hu
  have hh := Printed.standardGaussian_map_orthogonal_pair u (hReferencePairComplement u v) hu horth
  rw [Printed.standardGaussian_map_unit_faceDot _ (hReferencePairComplement_unit u v hu hv hρ)] at hh
  exact hh

/-- Exact expectation transport for any measurable test of the original
correlated Gaussian coordinates. No independent-coordinate conclusion is
assumed about the original normals. -/
theorem hReferencePair_projected_integral {r : ℕ} (u v : Vector r)
    (hu : vectorNormSq u=1) (hv : vectorNormSq v=1) (hρ : (faceDot u v)^2<1)
    (F : ℝ × ℝ → ℝ) (hF : Measurable F) :
    (∫ g, F (faceDot u g,faceDot v g) ∂standardGaussian r) =
      ∫ z, F (z.1,faceDot u v*z.1+Real.sqrt (1-(faceDot u v)^2)*z.2)
        ∂(gaussianReal 0 1).prod (gaussianReal 0 1) := by
  let e := hReferencePairComplement u v
  let T := fun g => (faceDot u g,faceDot e g)
  let H := fun z : ℝ × ℝ => F (z.1,faceDot u v*z.1+Real.sqrt (1-(faceDot u v)^2)*z.2)
  have hT : Measurable T := by unfold T faceDot; fun_prop
  have hH : Measurable H := hF.comp (by fun_prop)
  have hlin (g : Vector r) : faceDot v g=faceDot u v*faceDot u g+
      Real.sqrt (1-(faceDot u v)^2)*faceDot e g := by
    have he := congrArg (fun w => faceDot w g) (hReferencePairComplement_reconstruct u v hρ)
    simpa only [gaussianPair_faceDot_add_left,threshold_faceDot_smul_left] using he
  calc
    _ = ∫ g, H (T g) ∂standardGaussian r := integral_congr_ae (ae_of_all _ (fun g => by
      change F (faceDot u g,faceDot v g)=F (faceDot u g,_)
      rw [hlin]) )
    _ = ∫ z, H z ∂(standardGaussian r).map T :=
      (integral_map hT.aemeasurable hH.aestronglyMeasurable).symm
    _ = _ := by rw [hReferencePair_unit_coordinates_map u v hu hv hρ]

end
end RectangleCLTArxivV1
