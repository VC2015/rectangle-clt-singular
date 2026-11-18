import RectangleCLTArxivV1.SupplementalGOriginalHessian
import RectangleCLTArxivV1.SupplementalGHermite
import RectangleCLTCompanion.RestorationTensorIBP

/-! Exact Gaussian single/pair decomposition of the actual fourth
convolution tensor. All signs are retained before copy expectations. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section

theorem capOriginalSingleDerivative_eq_softFaceDirectional {p : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (f : Face p) :
    capOriginalSingleDerivative s A x f =
      s.softFaceDirectional {f} (A.mulVec (capFactorNormal A f)) x := by
  unfold capOriginalSingleDerivative
  have he : (fun t : ℝ => selectorTupleWeight s ![f]
      (line x (A.mulVec (capFactorNormal A f)) t)) =
      (fun t => s.softFaceWeight {f} (line x (A.mulVec (capFactorNormal A f)) t)) := by
    funext t
    simp [selectorTupleWeight,FaceSmoother.softFaceWeight,FaceSmoother.pi]
  rw [he]
  simpa only [line_zero] using
    (s.hasDerivAt_softFaceDirectional {f} (A.mulVec (capFactorNormal A f)) x 0).deriv

theorem cap_softFaceDirectional_smul {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (c : ℝ) (d x : Vector p) :
    s.softFaceDirectional S (c • d) x = c*s.softFaceDirectional S d x := by
  have hn (f : Face p) : normalDot f (c • d) = c*normalDot f d := by
    unfold normalDot
    split <;> simp [smul_eq_mul]
  have hm : (s.weights x).directionalMean (c • d) = c*(s.weights x).directionalMean d := by
    rw [FaceWeights.directionalMean_eq,FaceWeights.directionalMean_eq,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [Pi.smul_apply,smul_eq_mul]
    ring
  unfold FaceSmoother.softFaceDirectional
  simp_rw [hn]
  rw [hm,← Finset.mul_sum]
  ring

/-- The actual derivative of `Fπ_f` has a signed third-Hermite Gaussian
representation with precisely one additional inverse Gaussian scale. -/
theorem cap_singleFace_score_transfer {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x Z : Vector p) (f : Face p)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, repeatedDirectionScore g Z * capOriginalSingleDerivative s A
      ((σ • A).mulVec g+x) f ∂standardGaussian p) =
      (∫ g, capThirdHermiteScore (capFactorNormal A f) Z g *
        selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian p) / σ := by
  have ht := capThirdHermiteScore_integral_softFace s (σ • A) {f} x (capFactorNormal A f) Z
  simp_rw [Matrix.smul_mulVec_assoc,cap_softFaceDirectional_smul] at ht
  have he : (∫ g, repeatedDirectionScore g Z *
      (σ*s.softFaceDirectional {f} (A.mulVec (capFactorNormal A f)) ((σ • A).mulVec g+x))
      ∂standardGaussian p) =
      σ*(∫ g, repeatedDirectionScore g Z *
        s.softFaceDirectional {f} (A.mulVec (capFactorNormal A f)) ((σ • A).mulVec g+x)
        ∂standardGaussian p) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun g => by ring
  -- Only the coefficient matrix is scaled here; the evaluation point is
  -- the same genuine Gaussian point throughout the identity.
  have hsoft (g : Vector p) : s.softFaceWeight {f} ((σ • A).mulVec g+x) =
      selectorTupleWeight s ![f] ((σ • A).mulVec g+x) := by
    simp [selectorTupleWeight,FaceSmoother.softFaceWeight,FaceSmoother.pi]
  simp_rw [capOriginalSingleDerivative_eq_softFaceDirectional]
  apply (eq_div_iff hσ).mpr
  have ht' : (∫ g, capThirdHermiteScore (capFactorNormal A f) Z g *
      selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian p) =
      σ*(∫ g, repeatedDirectionScore g Z *
        s.softFaceDirectional {f} (A.mulVec (capFactorNormal A f)) ((σ • A).mulVec g+x)
        ∂standardGaussian p) := by
    simpa only [← Matrix.smul_mulVec_assoc,hsoft,he] using ht
  rw [ht']
  ring

theorem cap_integrable_score_selector {p k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x Z : Vector p) (α : Fin k → Face p) :
    Integrable (fun g => repeatedDirectionScore g Z*selectorTupleWeight s α (A.mulVec g+x))
      (standardGaussian p) := by
  have hs : Integrable (fun g => repeatedDirectionScore g Z) (standardGaussian p) := by
    simpa only [mul_one] using
      integrable_repeatedDirectionScore_weight (standardGaussian p) id (fun _ => (1 : ℝ))
        (integrable_const 1) (fun j k => by simpa only [mul_one] using
          standardGaussian_integrable_coordinate_product p j k) Z
  have hm := measurable_selectorTupleWeight_comp s α (fun g => A.mulVec g+x)
    ((measurable_mulVec A).add measurable_const)
  simpa only [mul_comm] using hs.bdd_mul hm.aestronglyMeasurable
    ⟨1,fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
      exact selectorTupleWeight_le_one s α _⟩

theorem cap_integrable_score_singleDerivative {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x Z : Vector p) (f : Face p) (σ : ℝ) :
    Integrable (fun g => repeatedDirectionScore g Z*capOriginalSingleDerivative s A
      ((σ • A).mulVec g+x) f) (standardGaussian p) := by
  let d := A.mulVec (capFactorNormal A f)
  have hi₂ := s.integrable_bilinear_softFaceDirectional_gaussian (σ • A) {f} x d Z Z
  have hi := s.integrable_softFaceDirectional_gaussian (σ • A) {f} x d
  simp_rw [capOriginalSingleDerivative_eq_softFaceDirectional]
  convert hi₂.sub (hi.const_mul (vectorNormSq Z)) using 1
  funext g
  dsimp only [Pi.sub_apply,repeatedDirectionScore,d]
  ring

/-- The actual fourth Gaussian convolution tensor has the printed signed
single-face H3 and pair H2 decomposition, with its precise Gaussian powers. -/
theorem cap_convolutionFourthTensor_single_pair {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (x Z Y W : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    s.convolutionFourthTensor (gaussianLaw (σ • A)) x (A.mulVec Z) (A.mulVec Z) Y W =
      -(1/(s.bandwidth*σ^3))*(∑ f, (normalDot f Y*normalDot f W)*
        (∫ g, capThirdHermiteScore (capFactorNormal A f) Z g*
          selectorTupleWeight s ![f] ((σ • A).mulVec g+x) ∂standardGaussian p)) +
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ g, capOriginalPairCoefficient A f g Y W*
        (∫ z, repeatedDirectionScore z Z*selectorTupleWeight s ![f,g]
          ((σ • A).mulVec z+x) ∂standardGaussian p)) := by
  let d (f : Face p) (g : Vector p) := capOriginalSingleDerivative s A ((σ • A).mulVec g+x) f
  let w (f g : Face p) (z : Vector p) := selectorTupleWeight s ![f,g] ((σ • A).mulVec z+x)
  let C (f : Face p) := normalDot f Y*normalDot f W
  let B (f g : Face p) := capOriginalPairCoefficient A f g Y W
  have hP : Integrable (fun g => ∑ f, C f*(repeatedDirectionScore g Z*d f g))
      (standardGaussian p) :=
    integrable_finset_sum _ (fun f _ => (cap_integrable_score_singleDerivative s A x Z f σ).const_mul (C f))
  have hQ : Integrable (fun z => ∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z))
      (standardGaussian p) :=
    integrable_finset_sum _ (fun f _ => integrable_finset_sum _
      (fun g _ => (cap_integrable_score_selector s (σ • A) x Z ![f,g]).const_mul (B f g)))
  have he (z : Vector p) : repeatedDirectionScore z Z*
      restorationHessian s ((σ • A).mulVec z+x) Y W =
        -(1/s.bandwidth)*(∑ f, C f*(repeatedDirectionScore z Z*d f z)) +
        (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z)) := by
    rw [cap_original_hessian_single_pair s A hdiag]
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
      restorationHessian s ((σ • A).mulVec g+x) Y W ∂standardGaussian p) =
      -(1/s.bandwidth)*(∑ f, C f*(∫ g, repeatedDirectionScore g Z*d f g ∂standardGaussian p)) +
      (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*
        (∫ z, repeatedDirectionScore z Z*w f g z ∂standardGaussian p)) := by
    simp_rw [he]
    rw [integral_add (f := fun g => -(1/s.bandwidth)*(∑ f, C f*(repeatedDirectionScore g Z*d f g)))
      (g := fun z => (1/s.bandwidth^2)*(∑ f, ∑ g, B f g*(repeatedDirectionScore z Z*w f g z)))
      (hP.const_mul _) (hQ.const_mul _),integral_const_mul,integral_const_mul]
    rw [integral_finset_sum _ (fun f _ => (cap_integrable_score_singleDerivative s A x Z f σ).const_mul (C f))]
    rw [integral_finset_sum _ (fun f _ => integrable_finset_sum _
      (fun g _ => (cap_integrable_score_selector s (σ • A) x Z ![f,g]).const_mul (B f g)))]
    simp_rw [integral_finset_sum _ (fun g _ =>
      (cap_integrable_score_selector s (σ • A) x Z ![_,g]).const_mul (B _ g)),integral_const_mul]
    rfl
  rw [convolutionFourthTensor_repeated_score_scaled s A x Z Y W hσ,hsplit]
  dsimp only [d,C,B,w]
  have ht (f : Face p) := cap_singleFace_score_transfer s A x Z f hσ
  simp_rw [ht]
  simp_rw [← mul_div_assoc]
  rw [← Finset.sum_div]
  field_simp [hσ,s.bandwidth_pos.ne']
  ring

end
end RectangleCLTArxivV1
