import RectangleCLTArxivV1.GaussianAdditionWidth
import RectangleCLTArxivV1.ThinnedMaximum

/-! Covariance order controls the actual Gaussian maximum by the printed
independent Gaussian addition and conditional Jensen argument. The positive
semidefinite complement is constructed, including in singular directions. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- An independent centered Gaussian addition increases the actual
expected maximum norm. -/
theorem gaussianMaximumMean_le_of_covariance_addition {p : ℕ}
    (B D A : Matrix (Fin p) (Fin p) ℝ)
    (hcov : A * A.transpose = B * B.transpose + D * D.transpose) :
    gaussianMaximumMean B ≤ gaussianMaximumMean A := by
  let τ := (gaussianLaw B).prod (gaussianLaw D)
  have hiB : Integrable (id : Vector p → Vector p) (gaussianLaw B) :=
    (integrable_norm_iff measurable_id.aestronglyMeasurable).mp (gaussianLaw_integrable_norm B)
  have hiD : Integrable (id : Vector p → Vector p) (gaussianLaw D) :=
    (integrable_norm_iff measurable_id.aestronglyMeasurable).mp (gaussianLaw_integrable_norm D)
  have hzero : (∫ x : Vector p, x ∂gaussianLaw D) = 0 := by
    ext j
    have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hiD
    change (∫ x : Vector p, x j ∂gaussianLaw D) = (∫ x : Vector p, x ∂gaussianLaw D) j at he
    simpa only [Pi.zero_apply] using he.symm.trans (gaussianLaw_integral_coordinate D j)
  have hm : (∫ z : Vector p × Vector p, z.2 ∂τ) = 0 := by
    simpa only [id_eq, measureReal_univ_eq_one, one_smul, hzero] using
      integral_fun_snd (μ := gaussianLaw B) (ν := gaussianLaw D) id
  have hind : IndepFun (Prod.fst : Vector p × Vector p → Vector p) Prod.snd τ := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    have he : (fun z : Vector p × Vector p => (z.1, z.2)) = id := rfl
    simp [τ, he]
  have hj := integral_norm_le_independent_add τ Prod.fst Prod.snd measurable_fst measurable_snd
    (integrable_fst_probability (gaussianLaw B) (gaussianLaw D) id hiB)
    (integrable_snd_probability (gaussianLaw B) (gaussianLaw D) id hiD) hm hind
  have hfun : gaussianScaledSum (p := p) 1 1 = (fun z => z.1 + z.2) := by
    funext z
    simp only [gaussianScaledSum, one_smul]
  have hlaw : τ.map (fun z => z.1 + z.2) = gaussianLaw A := by
    have hh := gaussianLaw_scaled_sum B D A 1 1 (by simpa only [one_pow, one_smul] using hcov)
    rw [hfun] at hh
    exact hh
  have he : (∫ z : Vector p × Vector p, ‖z.1 + z.2‖ ∂τ) = gaussianMaximumMean A := by
    unfold gaussianMaximumMean
    rw [← hlaw, integral_map (measurable_fst.add measurable_snd).aemeasurable measurable_norm.aestronglyMeasurable]
  rw [he, integral_fun_fst (μ := gaussianLaw B) (ν := gaussianLaw D) (fun x => ‖x‖)] at hj
  simpa only [measureReal_univ_eq_one, one_smul] using hj

/-- Quadratic covariance order constructs an independent Gaussian
complement and applies the actual Jensen estimate. -/
theorem gaussianMaximumMean_mono_jensen {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ)
    (hquad : ∀ v : Vector p, matrixQuadratic (B * B.transpose) v ≤
      matrixQuadratic (A * A.transpose) v) :
    gaussianMaximumMean B ≤ gaussianMaximumMean A := by
  let M := A * A.transpose - B * B.transpose
  have hPSD : M.PosSemidef := by
    constructor
    · simp only [M, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial,
        Matrix.transpose_sub, Matrix.transpose_mul, Matrix.transpose_transpose]
    · intro v
      have hh : 0 ≤ matrixQuadratic M v := by
        have he : matrixQuadratic M v = matrixQuadratic (A * A.transpose) v -
            matrixQuadratic (B * B.transpose) v := by
          simp only [M, matrixQuadratic, Matrix.sub_apply, mul_sub, sub_mul, Finset.sum_sub_distrib]
        rw [he]
        exact sub_nonneg.mpr (hquad v)
      simpa [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using hh
  let D := hPSD.sqrt
  have hD : D * D.transpose = M := by
    have hs : D.transpose = D := by
      simpa only [D, Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
        hPSD.posSemidef_sqrt.isHermitian
    rw [hs]
    exact hPSD.sqrt_mul_self
  apply gaussianMaximumMean_le_of_covariance_addition B D A
  rw [hD]
  dsimp [M]
  abel

/-- The precise printed conditional-width conclusion from an actual
quadratic bound by `CΣ`, using the Gaussian addition/Jensen route. -/
theorem gaussianMaximumMean_le_sqrt_mul_jensen {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hquad : ∀ v : Vector p, matrixQuadratic (B * B.transpose) v ≤
      C * matrixQuadratic (A * A.transpose) v) :
    gaussianMaximumMean B ≤ Real.sqrt C * gaussianMaximumMean A := by
  have hh := gaussianMaximumMean_mono_jensen (Real.sqrt C • A) B (by
    intro v
    rw [sqrt_smul_factor_gram C hC A, matrixQuadratic_smul_real]
    exact hquad v)
  simpa only [gaussianMaximumMean_smul, abs_of_nonneg (Real.sqrt_nonneg C)] using hh

end RectangleCLTArxivV1
