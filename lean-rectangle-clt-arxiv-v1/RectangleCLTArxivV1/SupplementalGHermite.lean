import RectangleCLTArxivV1.SupplementalGHessian
import RectangleCLT.GaussianFourthRecursion

/-! The additional signed third Hermite transfer used for Supplemental G's
single-face remainder. Gaussian polynomial integrability and Stein are
proved inputs from the archive, with no assumed remainder estimate. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def capThirdHermiteScore {r : ℕ} (u Z g : Vector r) : ℝ :=
  faceDot u g * repeatedDirectionScore g Z - 2*faceDot u Z*faceDot Z g

def capThirdHermiteMatrix {r : ℕ} (u g : Vector r) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => faceDot u g * (g j*g k-if j=k then 1 else 0) - u j*g k-g j*u k

private theorem cap_outer_quadratic {r : ℕ} (u v Z : Vector r) :
    matrixQuadratic (Matrix.vecMulVec u v) Z = faceDot u Z*faceDot v Z := by
  simp only [matrixQuadratic,Matrix.vecMulVec_apply,faceDot,Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The score is the actual quadratic contraction of the symmetric
third-Hermite matrix printed in the supplement. -/
theorem capThirdHermiteScore_eq_matrixQuadratic {r : ℕ} (u Z g : Vector r) :
    capThirdHermiteScore u Z g = matrixQuadratic (capThirdHermiteMatrix u g) Z := by
  have hbase := repeatedDirectionScore_eq_quadratic g Z
  have hsplit : capThirdHermiteMatrix u g =
      faceDot u g • (rankOne g-1) - Matrix.vecMulVec u g - Matrix.vecMulVec g u := by
    ext j k
    simp [capThirdHermiteMatrix,rankOne,Matrix.one_apply,Matrix.vecMulVec,smul_eq_mul]
  rw [hsplit]
  have hsub (B C : Matrix (Fin r) (Fin r) ℝ) :
      matrixQuadratic (B-C) Z = matrixQuadratic B Z-matrixQuadratic C Z := by
    simp [matrixQuadratic,sub_mul,mul_sub,Finset.sum_sub_distrib]
  rw [hsub,hsub,cap_outer_quadratic,cap_outer_quadratic]
  have hsmul (c : ℝ) (B : Matrix (Fin r) (Fin r) ℝ) :
      matrixQuadratic (c • B) Z = c*matrixQuadratic B Z := by
    simp only [matrixQuadratic,Matrix.smul_apply,smul_eq_mul,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  rw [hsmul,← hbase]
  unfold capThirdHermiteScore
  rw [faceDot_comm g Z]
  ring

theorem capThirdHermiteMatrix_symmetric {r : ℕ} (u g : Vector r) :
    (capThirdHermiteMatrix u g).transpose = capThirdHermiteMatrix u g := by
  ext j k
  simp only [Matrix.transpose_apply,capThirdHermiteMatrix,eq_comm]
  ring

/-- The extra Gaussian integration by parts transfers the derivative in a
single normal onto the repeated-direction score. The two derivative
corrections are retained with their signs and exact coefficient two. -/
theorem capThirdHermiteScore_integral_softFace {p : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u Z : Vector p) :
    (∫ g, capThirdHermiteScore u Z g * s.softFaceWeight S (A.mulVec g+x)
      ∂standardGaussian p) =
    ∫ g, repeatedDirectionScore g Z *
      s.softFaceDirectional S (A.mulVec u) (A.mulVec g+x) ∂standardGaussian p := by
  let W : Vector p → ℝ := fun g => s.softFaceWeight S (A.mulVec g+x)
  let D : Vector p → ℝ := fun g => s.softFaceDirectional S (A.mulVec u) (A.mulVec g+x)
  have hi₃ := s.integrable_trilinear_softFaceWeight_gaussian A S x u Z Z
  have hiu := s.integrable_linear_softFaceWeight_gaussian A S x u
  have hiz := s.integrable_linear_softFaceWeight_gaussian A S x Z
  have hiD := s.integrable_softFaceDirectional_gaussian A S x (A.mulVec u)
  have hi₂D := s.integrable_bilinear_softFaceDirectional_gaussian A S x (A.mulVec u) Z Z
  have htrip : Integrable (fun g => faceDot u g*(faceDot Z g*(faceDot Z g*W g)))
      (standardGaussian p) := by simpa only [W,mul_assoc] using hi₃
  have hlinearU : Integrable (fun g => faceDot u g*W g) (standardGaussian p) := hiu
  have hlinearZ : Integrable (fun g => faceDot Z g*W g) (standardGaussian p) := hiz
  have hquadraticD : Integrable (fun g => faceDot Z g*(faceDot Z g*D g))
      (standardGaussian p) := by simpa only [D,mul_assoc] using hi₂D
  have hleft : (∫ g, capThirdHermiteScore u Z g*W g ∂standardGaussian p) =
      (∫ g, faceDot u g*(faceDot Z g*(faceDot Z g*W g)) ∂standardGaussian p) -
      vectorNormSq Z*(∫ g, faceDot u g*W g ∂standardGaussian p) -
      (2*faceDot u Z)*(∫ g, faceDot Z g*W g ∂standardGaussian p) := by
    have he (g : Vector p) : capThirdHermiteScore u Z g*W g =
        (faceDot u g*(faceDot Z g*(faceDot Z g*W g)) -
          vectorNormSq Z*(faceDot u g*W g)) - (2*faceDot u Z)*(faceDot Z g*W g) := by
      unfold capThirdHermiteScore repeatedDirectionScore
      ring
    simp_rw [he]
    have hs₁ := integral_sub (htrip.sub (hlinearU.const_mul (vectorNormSq Z)))
      (hlinearZ.const_mul (2*faceDot u Z))
    have hs₂ := integral_sub htrip (hlinearU.const_mul (vectorNormSq Z))
    simp only [Pi.sub_apply] at hs₁ hs₂
    rw [hs₁,hs₂,integral_const_mul,integral_const_mul]
  have hright : (∫ g, repeatedDirectionScore g Z*D g ∂standardGaussian p) =
      (∫ g, faceDot Z g*(faceDot Z g*D g) ∂standardGaussian p) -
      vectorNormSq Z*(∫ g, D g ∂standardGaussian p) := by
    have he (g : Vector p) : repeatedDirectionScore g Z*D g =
        faceDot Z g*(faceDot Z g*D g)-vectorNormSq Z*D g := by
      unfold repeatedDirectionScore
      ring
    simp_rw [he]
    rw [integral_sub hquadraticD (hiD.const_mul _),integral_const_mul]
  change (∫ g, capThirdHermiteScore u Z g*W g ∂standardGaussian p) =
    ∫ g, repeatedDirectionScore g Z*D g ∂standardGaussian p
  rw [hleft,hright]
  have hquad := s.softFaceWeight_gaussian_quadratic_weighted_stein A S x u Z Z
  have hfirst := s.softFaceWeight_gaussian_directional_stein A S x u
  change (∫ g, faceDot u g*(faceDot Z g*(faceDot Z g*W g)) ∂standardGaussian p) =
    faceDot u Z*(∫ g, faceDot Z g*W g ∂standardGaussian p) +
    faceDot u Z*(∫ g, faceDot Z g*W g ∂standardGaussian p) +
    (∫ g, faceDot Z g*(faceDot Z g*D g) ∂standardGaussian p) at hquad
  rw [hquad,hfirst]
  dsimp only [D]
  ring

end
end RectangleCLTArxivV1
