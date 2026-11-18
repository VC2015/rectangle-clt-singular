import RectangleCLTArxivV1.SupplementalGRectangularHessian
import RectangleCLTArxivV1.SupplementalGRectangularStein

/-! Exact intrinsic-dimensional single/pair decomposition of the actual
Gaussian fourth directional derivative. Rectangular factors are allowed. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem capRectangularSingleDerivative_eq_softFaceDirectional {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (f : Face p) :
    capRectangularSingleDerivative s A x f =
      s.softFaceDirectional {f} (A.mulVec (capRectangularFactorNormal A f)) x := by
  unfold capRectangularSingleDerivative
  have he : (fun t : ℝ => selectorTupleWeight s ![f]
      (line x (A.mulVec (capRectangularFactorNormal A f)) t)) =
      (fun t => s.softFaceWeight {f} (line x (A.mulVec (capRectangularFactorNormal A f)) t)) := by
    funext t
    simp [selectorTupleWeight,FaceSmoother.softFaceWeight,FaceSmoother.pi]
  rw [he]
  simpa only [line_zero] using
    (s.hasDerivAt_softFaceDirectional {f} (A.mulVec (capRectangularFactorNormal A f)) x 0).deriv

/-- The actual derivative of `Fπ_f` has a signed third-Hermite Gaussian
representation with precisely one additional inverse Gaussian scale. -/
theorem cap_rectangular_singleFace_score_transfer {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (Z : Vector r) (f : Face p)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, repeatedDirectionScore g Z * capRectangularSingleDerivative s A
      ((σ • A).mulVec g+x) f ∂standardGaussian r) =
      (∫ g, capThirdHermiteScore (capRectangularFactorNormal A f) Z g *
        selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian r) / σ := by
  have ht := capThirdHermiteScore_integral_softFace_rectangular s (σ • A) {f} x (capRectangularFactorNormal A f) Z
  simp_rw [Matrix.smul_mulVec_assoc,cap_softFaceDirectional_smul] at ht
  have he : (∫ g, repeatedDirectionScore g Z *
      (σ*s.softFaceDirectional {f} (A.mulVec (capRectangularFactorNormal A f)) ((σ • A).mulVec g+x))
      ∂standardGaussian r) =
      σ*(∫ g, repeatedDirectionScore g Z *
        s.softFaceDirectional {f} (A.mulVec (capRectangularFactorNormal A f)) ((σ • A).mulVec g+x)
        ∂standardGaussian r) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by ring
  -- Only the coefficient matrix is scaled here; the evaluation point is
  -- the same genuine Gaussian point throughout the identity.
  have hsoft (g : Vector r) : s.softFaceWeight {f} ((σ • A).mulVec g+x) =
      selectorTupleWeight s ![f] ((σ • A).mulVec g+x) := by
    simp [selectorTupleWeight,FaceSmoother.softFaceWeight,FaceSmoother.pi]
  simp_rw [capRectangularSingleDerivative_eq_softFaceDirectional]
  apply (eq_div_iff hσ).mpr
  have ht' : (∫ g, capThirdHermiteScore (capRectangularFactorNormal A f) Z g *
      selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian r) =
      σ*(∫ g, repeatedDirectionScore g Z *
        s.softFaceDirectional {f} (A.mulVec (capRectangularFactorNormal A f)) ((σ • A).mulVec g+x)
        ∂standardGaussian r) := by
    simpa only [← Matrix.smul_mulVec_assoc,hsoft,he] using ht
  rw [ht']
  ring

theorem cap_rectangular_integrable_score_selector {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (Z : Vector r) (α : Fin k → Face p) :
    Integrable (fun g => repeatedDirectionScore g Z*selectorTupleWeight s α (A.mulVec g+x))
      (standardGaussian r) := by
  have hs : Integrable (fun g => repeatedDirectionScore g Z) (standardGaussian r) := by
    simpa only [mul_one] using
      integrable_repeatedDirectionScore_weight (standardGaussian r) id (fun _ => (1 : ℝ))
        (integrable_const 1) (fun j k => by simpa only [mul_one] using
          standardGaussian_integrable_coordinate_product r j k) Z
  have hm := measurable_selectorTupleWeight_comp s α (fun g => A.mulVec g+x)
    ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)
  simpa only [mul_comm] using hs.bdd_mul hm.aestronglyMeasurable
    ⟨1,fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
      exact selectorTupleWeight_le_one s α _⟩

theorem cap_rectangular_integrable_score_singleDerivative {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (Z : Vector r) (f : Face p) (σ : ℝ) :
    Integrable (fun g => repeatedDirectionScore g Z*capRectangularSingleDerivative s A
      ((σ • A).mulVec g+x) f) (standardGaussian r) := by
  rw [show (fun g => repeatedDirectionScore g Z*capRectangularSingleDerivative s A
      ((σ • A).mulVec g+x) f) =
      (fun g => repeatedDirectionScore g Z*s.softFaceDirectional {f}
        (A.mulVec (capRectangularFactorNormal A f)) ((σ • A).mulVec g+x)) by
      funext g; rw [capRectangularSingleDerivative_eq_softFaceDirectional]]
  apply cap_integrable_gaussian_bounded_product _ _ (integrable_fixed_gaussian_repeated_score Z)
  · exact (s.continuous_softFaceDirectional {f} _).measurable.comp
      ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)
  · exact ⟨_,fun g => s.abs_softFaceDirectional_le {f} _ _⟩

/-- The actual fourth Gaussian convolution tensor has the printed signed
single-face H3 and pair H2 decomposition, with its precise Gaussian powers. -/
theorem cap_rectangular_fourth_derivative_single_pair {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x : Vector p) (Z : Vector r) (Y W : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, restorationFourthDerivative s ((σ • A).mulVec g+x) (A.mulVec Z) Y W ∂standardGaussian r) =
      -(1/(s.bandwidth*σ^3))*(∑ f, (normalDot f Y*normalDot f W)*
        (∫ g, capThirdHermiteScore (capRectangularFactorNormal A f) Z g*
          selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian r)) +
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ g, capRectangularPairCoefficient A f g Y W*
        (∫ z, repeatedDirectionScore z Z*selectorTupleWeight s ![f,g]
          ((σ • A).mulVec z+x) ∂standardGaussian r)) := by
  let d (f : Face p) (g : Vector r) := capRectangularSingleDerivative s A ((σ • A).mulVec g+x) f
  let w (f g : Face p) (z : Vector r) := selectorTupleWeight s ![f,g] ((σ • A).mulVec z+x)
  let C (f : Face p) := normalDot f Y*normalDot f W
  let B (f g : Face p) := capRectangularPairCoefficient A f g Y W
  have hP : Integrable (fun g => ∑ f, C f*(repeatedDirectionScore g Z*d f g))
      (standardGaussian r) :=
    integrable_finset_sum _ (fun f _ => (cap_rectangular_integrable_score_singleDerivative s A x Z f σ).const_mul (C f))
  have hQ : Integrable (fun z => ∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z))
      (standardGaussian r) :=
    integrable_finset_sum _ (fun f _ => integrable_finset_sum _
      (fun g _ => (cap_rectangular_integrable_score_selector s (σ • A) x Z ![f,g]).const_mul (B f g)))
  have he (z : Vector r) : repeatedDirectionScore z Z*
      restorationHessian s ((σ • A).mulVec z+x) Y W =
        -(1/s.bandwidth)*(∑ f, C f*(repeatedDirectionScore z Z*d f z)) +
        (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z)) := by
    rw [cap_rectangular_hessian_single_pair s A hdiag]
    dsimp only [C,B,d,w]
    rw [mul_add]
    congr 1
    · simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      ring
    · simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro g _
      ring
  have hsplit : (∫ g, repeatedDirectionScore g Z*
      restorationHessian s ((σ • A).mulVec g+x) Y W ∂standardGaussian r) =
      -(1/s.bandwidth)*(∑ f, C f*(∫ g, repeatedDirectionScore g Z*d f g ∂standardGaussian r)) +
      (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*
        (∫ z, repeatedDirectionScore z Z*w f g z ∂standardGaussian r)) := by
    simp_rw [he]
    rw [integral_add (f := fun g => -(1/s.bandwidth)*(∑ f, C f*(repeatedDirectionScore g Z*d f g)))
      (g := fun z => (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z)))
      (hP.const_mul _) (hQ.const_mul _),integral_const_mul,integral_const_mul]
    rw [integral_finset_sum _ (fun f _ => (cap_rectangular_integrable_score_singleDerivative s A x Z f σ).const_mul (C f))]
    rw [integral_finset_sum _ (fun f _ => integrable_finset_sum _
      (fun g _ => (cap_rectangular_integrable_score_selector s (σ • A) x Z ![f,g]).const_mul (B f g)))]
    simp_rw [integral_finset_sum _ (fun g _ =>
      (cap_rectangular_integrable_score_selector s (σ • A) x Z ![_,g]).const_mul (B _ g)),integral_const_mul]
    rfl
  rw [gaussian_restorationFourthDerivative_stein s A x Y W Z hσ]
  simp_rw [restorationHessian_swap s _ W Y]
  rw [hsplit]
  dsimp only [d,C,B,w]
  have ht (f : Face p) := cap_rectangular_singleFace_score_transfer s A x Z f hσ
  simp_rw [ht]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp [hσ,s.bandwidth_pos.ne']
  ring


end
end RectangleCLTArxivV1
