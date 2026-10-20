import RectangleCLT.Statement
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Uniqueness and addition of the concrete Gaussian laws

The native `Vector p` norm is the maximum norm. Character uniqueness is
therefore applied directly to the separating dot-product bilinear form,
without imposing an incompatible inner-product norm on that type.
All covariance matrices may be singular.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def vectorDotPairing (p : ℕ) : Vector p →ₗ[ℝ] Vector p →ₗ[ℝ] ℝ :=
  LinearMap.mk₂ ℝ dotProduct
    (fun _ _ _ => add_dotProduct _ _ _)
    (fun _ _ _ => smul_dotProduct _ _ _)
    (fun _ _ _ => dotProduct_add _ _ _)
    (fun _ _ _ => dotProduct_smul _ _ _)

theorem vectorDotPairing_continuous (p : ℕ) :
    Continuous (fun z : Vector p × Vector p => vectorDotPairing p z.1 z.2) := by
  change Continuous (fun z : Vector p × Vector p => ∑ j, z.1 j * z.2 j)
  fun_prop

def vectorFourierKernel {p : ℕ} (t x : Vector p) : ℂ :=
  Complex.exp ((dotProduct x t : ℝ) * Complex.I)

theorem measurable_vectorFourierKernel {p : ℕ} (t : Vector p) :
    Measurable (vectorFourierKernel t) := by
  unfold vectorFourierKernel dotProduct
  fun_prop

def vectorFourier {p : ℕ} (μ : Measure (Vector p)) (t : Vector p) : ℂ :=
  ∫ x, vectorFourierKernel t x ∂μ

theorem measure_eq_of_vectorFourier_eq {p : ℕ} {μ ν : Measure (Vector p)}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (h : ∀ t, vectorFourier μ t = vectorFourier ν t) : μ = ν := by
  apply ext_of_integral_char_eq Real.continuous_probChar Real.probChar_ne_one
    (L := vectorDotPairing p) ?_ (vectorDotPairing_continuous p)
  · intro v hv hzero
    have hself := LinearMap.congr_fun hzero v
    change dotProduct v v = 0 at hself
    exact hv (dotProduct_self_eq_zero.mp hself)
  · intro t
    simpa only [BoundedContinuousFunction.char_apply, Real.probChar_apply,
      vectorDotPairing, LinearMap.mk₂_apply, vectorFourier, vectorFourierKernel] using h t

theorem vectorFourier_standardGaussian {p : ℕ} (t : Vector p) :
    vectorFourier (standardGaussian p) t =
      Complex.exp (-((∑ j, t j ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  have hprod (x : Vector p) : vectorFourierKernel t x =
      ∏ j, Complex.exp (((t j * x j : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    unfold vectorFourierKernel dotProduct
    congr 1
    simp only [Complex.ofReal_sum, Complex.ofReal_mul, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hscalar (j : Fin p) :
      (∫ x : ℝ, Complex.exp (((t j * x : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 1) = Complex.exp (-((t j : ℂ) ^ 2) / 2) := by
    simpa [charFun_apply_real] using
      (charFun_gaussianReal (μ := 0) (v := 1) (t j))
  unfold vectorFourier
  simp_rw [hprod]
  change (∫ x : Fin p → ℝ, ∏ j,
    Complex.exp (((t j * x j : ℝ) : ℂ) * Complex.I)) = _
  rw [integral_fintype_prod_eq_prod]
  change (∏ j, ∫ x : ℝ, Complex.exp (((t j * x : ℝ) : ℂ) * Complex.I)
    ∂gaussianReal 0 1) = _
  simp_rw [hscalar]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Complex.ofReal_pow, Finset.sum_neg_distrib,
    Finset.sum_div]

theorem vectorFourier_gaussianLaw {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (t : Vector p) :
    vectorFourier (gaussianLaw A) t =
      Complex.exp (-((dotProduct t ((A * A.transpose).mulVec t) : ℝ) : ℂ) / 2) := by
  have hlinear (x : Vector p) :
      vectorFourierKernel t (A.mulVec x) =
        vectorFourierKernel (A.transpose.mulVec t) x := by
    have hdot : dotProduct (A.mulVec x) t = dotProduct x (A.transpose.mulVec t) := by
      rw [dotProduct_comm, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose,
        dotProduct_comm]
    unfold vectorFourierKernel
    rw [hdot]
  unfold vectorFourier gaussianLaw
  rw [integral_map (measurable_mulVec A).aemeasurable
    (measurable_vectorFourierKernel t).aestronglyMeasurable]
  simp_rw [hlinear]
  change vectorFourier (standardGaussian p) (A.transpose.mulVec t) = _
  rw [vectorFourier_standardGaussian]
  have hquadratic : (∑ j, (A.transpose.mulVec t j) ^ 2) =
      dotProduct t ((A * A.transpose).mulVec t) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [dotProduct, pow_two]
  rw [hquadratic]

/-- The explicit Gaussian law depends on the covariance, including for
singular square factors. -/
theorem gaussianLaw_eq_of_factor_covariance {p : ℕ}
    {A B : Matrix (Fin p) (Fin p) ℝ}
    (hcov : A * A.transpose = B * B.transpose) : gaussianLaw A = gaussianLaw B := by
  apply measure_eq_of_vectorFourier_eq
  intro t
  rw [vectorFourier_gaussianLaw, vectorFourier_gaussianLaw, hcov]

/-- Every coordinate marginal of the concrete Gaussian law is the centered
real Gaussian with the corresponding covariance diagonal entry. -/
theorem gaussianLaw_map_eval_eq_gaussianReal {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) (v : ℝ≥0)
    (hdiag : (A * A.transpose) j j = (v : ℝ)) :
    (gaussianLaw A).map (fun x => x j) = gaussianReal 0 v := by
  classical
  apply Measure.ext_of_charFun
  funext t
  have hdot (x : Vector p) : dotProduct x (t • Pi.single j (1 : ℝ)) = t * x j := by
    simp [dotProduct, Pi.single_apply, mul_ite, ite_mul, mul_comm]
  have hquadratic : dotProduct (t • Pi.single j (1 : ℝ))
      ((A * A.transpose).mulVec (t • Pi.single j (1 : ℝ))) = t ^ 2 * (v : ℝ) := by
    simp [dotProduct, Matrix.mulVec, Pi.single_apply, mul_ite, ite_mul,
      Finset.mul_sum, Finset.sum_mul, hdiag]
    ring
  calc
    charFun ((gaussianLaw A).map (fun x => x j)) t =
        vectorFourier (gaussianLaw A) (t • Pi.single j (1 : ℝ)) := by
      rw [charFun_apply_real,
        integral_map (measurable_pi_apply j).aemeasurable (by fun_prop)]
      unfold vectorFourier vectorFourierKernel
      simp_rw [hdot]
      rfl
    _ = Complex.exp (-((t ^ 2 * (v : ℝ) : ℝ) : ℂ) / 2) := by
      rw [vectorFourier_gaussianLaw, hquadratic]
    _ = charFun (gaussianReal 0 v) t := by
      rw [charFun_gaussianReal]
      push_cast
      congr 1
      ring

theorem gaussianLaw_map_eval_eq_standard {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p)
    (hdiag : (A * A.transpose) j j = 1) :
    (gaussianLaw A).map (fun x => x j) = gaussianReal 0 1 :=
  gaussianLaw_map_eval_eq_gaussianReal A j 1 (by simpa using hdiag)

def gaussianScaledSum {p : ℕ} (a b : ℝ) (z : Vector p × Vector p) : Vector p :=
  a • z.1 + b • z.2

theorem measurable_gaussianScaledSum {p : ℕ} (a b : ℝ) :
    Measurable (gaussianScaledSum (p := p) a b) := by
  unfold gaussianScaledSum
  fun_prop

theorem vectorFourier_gaussianScaledSum {p : ℕ}
    (A B : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ) (t : Vector p) :
    vectorFourier (((gaussianLaw A).prod (gaussianLaw B)).map (gaussianScaledSum a b)) t =
      Complex.exp (-((dotProduct t
        ((a ^ 2 • (A * A.transpose) + b ^ 2 • (B * B.transpose)).mulVec t) : ℝ) : ℂ) / 2) := by
  have hkernel (z : Vector p × Vector p) :
      vectorFourierKernel t (gaussianScaledSum a b z) =
        vectorFourierKernel (a • t) z.1 * vectorFourierKernel (b • t) z.2 := by
    unfold vectorFourierKernel gaussianScaledSum
    rw [← Complex.exp_add]
    congr 1
    simp only [add_dotProduct, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      Complex.ofReal_add, Complex.ofReal_mul]
    ring
  unfold vectorFourier
  rw [integral_map (measurable_gaussianScaledSum a b).aemeasurable
    (measurable_vectorFourierKernel t).aestronglyMeasurable]
  simp_rw [hkernel]
  rw [integral_prod_mul]
  change vectorFourier (gaussianLaw A) (a • t) * vectorFourier (gaussianLaw B) (b • t) = _
  rw [vectorFourier_gaussianLaw, vectorFourier_gaussianLaw, ← Complex.exp_add]
  congr 1
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.mulVec_smul,
    dotProduct_add, dotProduct_smul, smul_dotProduct, smul_eq_mul,
    Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_pow]
  ring

/-- A sum of independent centered Gaussian laws has the sum of their scaled
covariances. No factor, covariance, or interpolating covariance is required
to be invertible. -/
theorem gaussianLaw_scaled_sum {p : ℕ}
    (A B C : Matrix (Fin p) (Fin p) ℝ) (a b : ℝ)
    (hcov : C * C.transpose = a ^ 2 • (A * A.transpose) + b ^ 2 • (B * B.transpose)) :
    ((gaussianLaw A).prod (gaussianLaw B)).map (gaussianScaledSum a b) = gaussianLaw C := by
  apply measure_eq_of_vectorFourier_eq
  intro t
  rw [vectorFourier_gaussianScaledSum, vectorFourier_gaussianLaw, hcov]

end

end RectangleCLT
