import RectangleCLT.GaussianComparisonLaw

/-! Genuine finite-dimensional Gaussian linear images with rectangular factors. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def finiteStandardGaussian (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ => gaussianReal 0 1)

instance finiteStandardGaussian_probability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (finiteStandardGaussian ι) := by unfold finiteStandardGaussian; infer_instance

theorem measurable_rectangularMulVec {p : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin p) ι ℝ) : Measurable B.mulVec :=
  measurable_pi_lambda _ (fun r => Finset.measurable_sum _ (fun i _ => measurable_const.mul (measurable_pi_apply i)))

def rectangularGaussianLaw {p : ℕ} {ι : Type*} [Fintype ι] (B : Matrix (Fin p) ι ℝ) : Measure (Vector p) :=
  (finiteStandardGaussian ι).map B.mulVec

instance rectangularGaussianLaw_probability {p : ℕ} {ι : Type*} [Fintype ι] (B : Matrix (Fin p) ι ℝ) :
    IsProbabilityMeasure (rectangularGaussianLaw B) := isProbabilityMeasure_map (measurable_rectangularMulVec B).aemeasurable

theorem finiteStandardGaussian_fourier {ι : Type*} [Fintype ι] (a : ι → ℝ) :
    (∫ z : ι → ℝ, Complex.exp (((dotProduct z a : ℝ) : ℂ) * Complex.I) ∂finiteStandardGaussian ι) =
      Complex.exp (-((∑ i, a i ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  letI : SigmaFinite (volume : Measure ℝ) := inferInstanceAs (SigmaFinite (gaussianReal 0 1))
  have hpoint (z : ι → ℝ) : Complex.exp (((dotProduct z a : ℝ) : ℂ) * Complex.I) =
      ∏ i, Complex.exp (((a i * z i : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [dotProduct, Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  simp_rw [hpoint]
  change (∫ z : ι → ℝ, ∏ i, Complex.exp (((a i * z i : ℝ) : ℂ) * Complex.I)) = _
  rw [integral_fintype_prod_eq_prod ι (E := fun _ => ℝ)
    (fun i (z : ℝ) => Complex.exp (((a i * z : ℝ) : ℂ) * Complex.I))]
  change (∏ i, ∫ z : ℝ, Complex.exp (((a i * z : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1) = _
  have hscalar (i : ι) : (∫ z : ℝ, Complex.exp (((a i * z : ℝ) : ℂ) * Complex.I) ∂gaussianReal 0 1) =
      Complex.exp (-((a i : ℂ) ^ 2) / 2) := by
    simpa [charFun_apply_real, neg_div] using (charFun_gaussianReal (μ := 0) (v := 1) (a i))
  simp_rw [hscalar]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow]
  rw [← Finset.sum_div, Finset.sum_neg_distrib]

theorem vectorFourier_rectangularGaussianLaw {p : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin p) ι ℝ) (t : Vector p) :
    vectorFourier (rectangularGaussianLaw B) t =
      Complex.exp (-((dotProduct t ((B * B.transpose).mulVec t) : ℝ) : ℂ) / 2) := by
  have hlinear (z : ι → ℝ) : vectorFourierKernel t (B.mulVec z) =
      Complex.exp (((dotProduct z (B.transpose.mulVec t) : ℝ) : ℂ) * Complex.I) := by
    have hdot : dotProduct (B.mulVec z) t = dotProduct z (B.transpose.mulVec t) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose, dotProduct_comm]
    unfold vectorFourierKernel
    rw [hdot]
  unfold vectorFourier rectangularGaussianLaw
  rw [integral_map (measurable_rectangularMulVec B).aemeasurable (measurable_vectorFourierKernel t).aestronglyMeasurable]
  simp_rw [hlinear]
  rw [finiteStandardGaussian_fourier]
  have hquadratic : (∑ i, (B.transpose.mulVec t i) ^ 2) = dotProduct t ((B * B.transpose).mulVec t) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [dotProduct, pow_two]
  rw [hquadratic]

theorem rectangularGaussianLaw_eq_gaussianLaw {p : ℕ} {ι : Type*} [Fintype ι]
    (B : Matrix (Fin p) ι ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hcov : B * B.transpose = A * A.transpose) : rectangularGaussianLaw B = gaussianLaw A := by
  apply measure_eq_of_vectorFourier_eq
  intro t
  rw [vectorFourier_rectangularGaussianLaw, vectorFourier_gaussianLaw, hcov]

end
end RectangleCLT.Companion.SplitV4
