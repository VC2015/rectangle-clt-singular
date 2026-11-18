import RectangleCLTArxivV1.SupplementalGDecomposition
import RectangleCLTCompanion.SplitV4.RestorationConditionalStein

/-! The additional third-Hermite transfer for rectangular factors. This
uses genuine scalar Gaussian Stein with polynomial integrability, so the
Gaussian dimension may equal the covariance rank. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_integrable_gaussian_bounded_product {r : ℕ}
    (P F : Vector r → ℝ) (hPi : Integrable P (standardGaussian r))
    (hFm : Measurable F) (hFb : ∃ C : ℝ, ∀ g, |F g| ≤ C) :
    Integrable (fun g => P g*F g) (standardGaussian r) := by
  obtain ⟨C,hC⟩ := hFb
  simpa only [mul_comm] using hPi.bdd_mul hFm.aestronglyMeasurable
    ⟨C,fun g => by simpa only [Real.norm_eq_abs] using hC g⟩

theorem cap_integrable_coordinate_score {r : ℕ} (Z : Vector r) (j : Fin r) :
    Integrable (fun g => g j*repeatedDirectionScore g Z) (standardGaussian r) := by
  have htrip := standardGaussian_integrable_faceDot_triple (localBasisVector j) Z Z
  have he : faceDot (localBasisVector j) = (fun g : Vector r => g j) := by
    funext g
    simp [faceDot,localBasisVector]
  rw [he] at htrip
  convert htrip.sub ((standardGaussian_integrable_coordinate r j).const_mul (vectorNormSq Z)) using 1
  funext g
  dsimp only [repeatedDirectionScore,Pi.sub_apply]
  ring

/-- An actual third-Hermite integration by parts for any bounded smooth
Gaussian test. Ordinary derivatives and bounded envelopes supply all
integrability; the Gaussian identity is proved. -/
theorem capThirdHermiteScore_integral_bounded
    {r : ℕ} (u Z : Vector r) (F : Vector r → ℝ) (D : Fin r → Vector r → ℝ)
    (hFm : Measurable F) (hDm : ∀ j, Measurable (D j))
    (hFb : ∃ C : ℝ, ∀ g, |F g| ≤ C) (hDb : ∀ j, ∃ C : ℝ, ∀ g, |D j g| ≤ C)
    (hderiv : ∀ j g, HasDerivAt (fun t => F (Function.update g j t)) (D j g) (g j)) :
    (∫ g, capThirdHermiteScore u Z g*F g ∂standardGaussian r) =
      ∫ g, repeatedDirectionScore g Z*(∑ j, u j*D j g) ∂standardGaussian r := by
  have hscore := integrable_fixed_gaussian_repeated_score Z
  have hsf := cap_integrable_gaussian_bounded_product _ F hscore hFm hFb
  have hlin := cap_integrable_gaussian_bounded_product (faceDot Z) F
    (standardGaussian_integrable_faceDot Z) hFm hFb
  have hsd (j : Fin r) := cap_integrable_gaussian_bounded_product _ (D j) hscore (hDm j) (hDb j)
  have hxi (j : Fin r) : Integrable (fun g => g j*(repeatedDirectionScore g Z*F g))
      (standardGaussian r) := by
    simpa only [mul_assoc] using cap_integrable_gaussian_bounded_product _ F
      (cap_integrable_coordinate_score Z j) hFm hFb
  have hgrad (j : Fin r) : Integrable (fun g =>
      2*Z j*faceDot Z g*F g+repeatedDirectionScore g Z*D j g) (standardGaussian r) := by
    simpa only [mul_assoc] using (hlin.const_mul (2*Z j)).add (hsd j)
  have hs := standardGaussian_directional_stein_of_integrable u
    (g := fun g => repeatedDirectionScore g Z*F g)
    (g' := fun j g => 2*Z j*faceDot Z g*F g+repeatedDirectionScore g Z*D j g)
    (fun j g => by
      convert (((hasDerivAt_faceDot_update Z g j).pow 2).sub_const (vectorNormSq Z)).mul (hderiv j g) using 1
      simp only [Function.update_eq_self,repeatedDirectionScore,pow_one,Nat.reduceSub]
      ring) hsf hgrad hxi
  have hpoint (g : Vector r) :
      (∑ j, u j*(2*Z j*faceDot Z g*F g+repeatedDirectionScore g Z*D j g)) =
      (2*faceDot u Z)*(faceDot Z g*F g)+repeatedDirectionScore g Z*(∑ j, u j*D j g) := by
    simp only [mul_add,Finset.sum_add_distrib]
    congr 1
    · change (∑ j, u j*(2*Z j*faceDot Z g*F g)) =
        (2*(∑ j, u j*Z j))*(faceDot Z g*F g)
      simp only [Finset.mul_sum,Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
  simp_rw [hpoint] at hs
  have hri : Integrable (fun g => repeatedDirectionScore g Z*(∑ j, u j*D j g))
      (standardGaussian r) := by
    have hi := integrable_finset_sum Finset.univ (fun j _ => (hsd j).const_mul (u j))
    convert hi using 1
    funext g
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hli : Integrable (fun g => faceDot u g*(repeatedDirectionScore g Z*F g))
      (standardGaussian r) := by
    simpa only [faceDot,Finset.sum_mul,mul_assoc] using
      integrable_finset_sum Finset.univ (fun j _ => (hxi j).const_mul (u j))
  have he (g : Vector r) : capThirdHermiteScore u Z g*F g =
      faceDot u g*(repeatedDirectionScore g Z*F g)-(2*faceDot u Z)*(faceDot Z g*F g) := by
    unfold capThirdHermiteScore
    ring
  simp_rw [he]
  rw [integral_sub hli (hlin.const_mul _),hs,integral_add (hlin.const_mul _) hri]
  ring

theorem cap_softFaceDirectional_mulVec {p r : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (S : Finset (Face p)) (u : Vector r) (x : Vector p) :
    s.softFaceDirectional S (A.mulVec u) x =
      ∑ j, u j * s.softFaceDirectional S (fun k => A k j) x := by
  have hnormal (f : Face p) : normalDot f (A.mulVec u) =
      ∑ j, u j * normalDot f (fun k => A k j) := by
    cases hf : f.2 <;>
      simp only [normalDot, hf, Bool.false_eq_true, ↓reduceIte,
        Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hmean : (s.weights x).directionalMean (A.mulVec u) =
      ∑ j, u j * (s.weights x).directionalMean (fun k => A k j) := by
    simp only [FaceWeights.directionalMean_eq, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold softFaceDirectional
  rw [hmean]
  simp_rw [hnormal]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro f _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

theorem cap_softFaceWeight_rectangular_slice {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (S : Finset (Face p)) (x : Vector p)
    (g : Vector r) (j : Fin r) :
    HasDerivAt (fun t => s.softFaceWeight S (A.mulVec (Function.update g j t)+x))
      (s.softFaceDirectional S (fun k => A k j) (A.mulVec g+x)) (g j) := by
  have hd0 : HasDerivAt
      (fun a => s.softFaceWeight S (line (A.mulVec g+x) (fun k => A k j) a))
      (s.softFaceDirectional S (fun k => A k j) (A.mulVec g+x)) (g j-g j) := by
    simpa only [sub_self,line_zero] using
      s.hasDerivAt_softFaceDirectional S (fun k => A k j) (A.mulVec g+x) 0
  have hd := hd0.comp (h := fun t : ℝ => t-g j) (g j)
    ((hasDerivAt_id (g j)).sub_const (g j))
  simpa only [Function.comp_apply,sub_self,line_zero,mul_one,restorationAffine_update] using hd

/-- The extra signed H3 transfer is valid for a rectangular covariance
factor, with Gaussian dimension r independently of the ambient dimension p. -/
theorem capThirdHermiteScore_integral_softFace_rectangular {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (S : Finset (Face p)) (x : Vector p) (u Z : Vector r) :
    (∫ g, capThirdHermiteScore u Z g*s.softFaceWeight S (A.mulVec g+x) ∂standardGaussian r) =
      ∫ g, repeatedDirectionScore g Z*s.softFaceDirectional S (A.mulVec u) (A.mulVec g+x)
        ∂standardGaussian r := by
  let F : Vector r → ℝ := fun g => s.softFaceWeight S (A.mulVec g+x)
  let D : Fin r → Vector r → ℝ := fun j g =>
    s.softFaceDirectional S (fun k => A k j) (A.mulVec g+x)
  have hx : Measurable (fun g : Vector r => A.mulVec g+x) :=
    (continuous_const.matrix_mulVec continuous_id).measurable.add_const x
  have hFm : Measurable F := (s.continuous_softFaceWeight S).measurable.comp hx
  have hDm (j : Fin r) : Measurable (D j) :=
    (s.continuous_softFaceDirectional S _).measurable.comp hx
  have hFb : ∃ C : ℝ, ∀ g, |F g| ≤ C := ⟨1,fun g => by
    rw [abs_of_nonneg (s.softFaceWeight_nonneg S _)]
    exact s.softFaceWeight_le_one S _⟩
  have hDb (j : Fin r) : ∃ C : ℝ, ∀ g, |D j g| ≤ C :=
    ⟨_,fun g => s.abs_softFaceDirectional_le S (fun k => A k j) (A.mulVec g+x)⟩
  have hs := capThirdHermiteScore_integral_bounded u Z F D hFm hDm hFb hDb
    (fun j g => cap_softFaceWeight_rectangular_slice s A S x g j)
  simpa only [F,D,← cap_softFaceDirectional_mulVec] using hs

end
end RectangleCLTArxivV1
