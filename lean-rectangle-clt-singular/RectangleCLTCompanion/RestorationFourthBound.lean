import RectangleCLTCompanion.RestorationHessian

/-! Quantitative restoration of the actual score-weighted Hessian, obtained
from the two finite partitions.  The selector matrix estimate remains the
single explicit analytic estimate premise. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

def restorationSelectorCap (s : FaceSmoother p) (b K R C T : ℝ) (k : ℕ) : ℝ :=
  (b * K * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
    (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1)

def restorationHessianCoefficientsOne
    (Y W : Ω → Fin n → Ξ → Vector p) : Fin n → (Fin 1 → Face p) → Ω → Ξ → ℝ :=
  fun i α ω => restorationHessianCoefficientOne (Y ω) (W ω) i α

def restorationHessianCoefficientsTwo
    (Y W : Ω → Fin n → Ξ → Vector p) : Fin n → (Fin 2 → Face p) → Ω → Ξ → ℝ :=
  fun i α ω => restorationHessianCoefficientTwo (Y ω) (W ω) i α

/-- A real averaged restoration estimate, rather than a hypothesis named
after the desired error term.  All arrays can be dependent within and
between summands; their independence from the Gaussian is the product law. -/
theorem restorationHessianExpectation_integrable_and_bound
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (Z : Ω → Fin n → Ξ → Vector r) (Y W : Ω → Fin n → Ξ → Vector p)
    (v : Fin n → Ω → Ξ → Vector p) {δ K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν A V C T)
    (hV : Measurable V) (hZm : ∀ ω i, Measurable (Z ω i))
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hY : ∀ ω i, Measurable (Y ω i)) (hW : ∀ ω i, Measurable (W ω i))
    (hv : ∀ i ω, Measurable (v i ω))
    (hYb : ∀ ω i a, ‖Y ω i a‖ ≤ δ) (hWb : ∀ ω i a, ‖W ω i a‖ ≤ δ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤ K * vectorNormSq u)
    (hBm1 : ∀ (ℓ : ℕ) (α : Fin 1 → Face p) (β : Fin ℓ → Face p) (j l : Fin r),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z
        (restorationHessianCoefficientsOne Y W) v α β ω j l))
    (hBm2 : ∀ (ℓ : ℕ) (α : Fin 2 → Face p) (β : Fin ℓ → Face p) (j l : Fin r),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z
        (restorationHessianCoefficientsTwo Y W) v α β ω j l))
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Integrable (fun ω => fixedRestorationHessianExpectation s μ A (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω)) ν ∧
    |∫ ω, fixedRestorationHessianExpectation s μ A (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω) ∂ν| ≤
        (2 * restorationSelectorCap s (δ ^ 2) K R C T 2 +
          restorationSelectorCap s (δ ^ 2) K R C T 1) / s.bandwidth ^ 2 := by
  have hc1 (i : Fin n) (α : Fin 1 → Face p) (ω : Ω) :
      Measurable (fun a => restorationHessianCoefficientsOne Y W i α ω a) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY ω i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW ω i))
  have hc2 (i : Fin n) (α : Fin 2 → Face p) (ω : Ω) :
      Measurable (fun a => restorationHessianCoefficientsTwo Y W i α ω a) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY ω i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hW ω i))
  have hb1 (i : Fin n) (α : Fin 1 → Face p) (ω : Ω) (a : Ξ) :
      |restorationHessianCoefficientsOne Y W i α ω a| ≤ δ ^ 2 :=
    restorationHessianCoefficient_abs_le (hYb ω) (hWb ω) i (α 0) (α 0) a
  have hb2 (i : Fin n) (α : Fin 2 → Face p) (ω : Ω) (a : Ξ) :
      |restorationHessianCoefficientsTwo Y W i α ω a| ≤ δ ^ 2 :=
    restorationHessianCoefficient_abs_le (hYb ω) (hWb ω) i (α 0) (α 1) a
  have h1 := restorationTranslatedExpectation_integrable_and_bound s ν μ A V Z
    (restorationHessianCoefficientsOne Y W) v hmatrix (by decide) hV hZm hZ hc1 hv
      hb1 (sq_nonneg δ) hK hR hvb hbudget hBm1 hC hT hsmall
  have h2 := restorationTranslatedExpectation_integrable_and_bound s ν μ A V Z
    (restorationHessianCoefficientsTwo Y W) v hmatrix (by decide) hV hZm hZ hc2 hv
      hb2 (sq_nonneg δ) hK hR hvb hbudget hBm2 hC hT hsmall
  let J1 : Ω → ℝ := fun ω => fixedRestorationTranslatedExpectation s μ A (V ω) (Z ω)
    (restorationHessianCoefficientOne (Y ω) (W ω)) (fun i => v i ω)
  let J2 : Ω → ℝ := fun ω => fixedRestorationTranslatedExpectation s μ A (V ω) (Z ω)
    (restorationHessianCoefficientTwo (Y ω) (W ω)) (fun i => v i ω)
  have hpoint (ω : Ω) : fixedRestorationHessianExpectation s μ A (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω) = (2 * J2 ω - J1 ω) / s.bandwidth ^ 2 :=
    fixedRestorationHessianExpectation_eq_partitions s μ A (V ω) (Z ω) (Y ω) (W ω)
      (fun i => v i ω) (hZ ω) (hY ω) (hW ω) (fun i => hv i ω) (hYb ω) (hWb ω)
  have hJ1 : Integrable J1 ν := h1.1
  have hJ2 : Integrable J2 ν := h2.1
  have hJ1b : |∫ ω, J1 ω ∂ν| ≤ restorationSelectorCap s (δ ^ 2) K R C T 1 := h1.2
  have hJ2b : |∫ ω, J2 ω ∂ν| ≤ restorationSelectorCap s (δ ^ 2) K R C T 2 := h2.2
  constructor
  · convert ((hJ2.const_mul 2).sub hJ1).div_const (s.bandwidth ^ 2) using 1
    funext ω
    exact hpoint ω
  · have heq : (∫ ω, fixedRestorationHessianExpectation s μ A (V ω) (Z ω)
        (Y ω) (W ω) (fun i => v i ω) ∂ν) =
        (2 * (∫ ω, J2 ω ∂ν) - ∫ ω, J1 ω ∂ν) / s.bandwidth ^ 2 := by
      simp_rw [hpoint]
      rw [integral_div, integral_sub (hJ2.const_mul 2) hJ1, integral_const_mul]
    rw [heq, abs_div, abs_of_pos (pow_pos s.bandwidth_pos 2)]
    apply div_le_div_of_nonneg_right _ (sq_nonneg _)
    calc
      _ ≤ |2 * ∫ ω, J2 ω ∂ν| + |∫ ω, J1 ω ∂ν| := abs_sub _ _
      _ = 2 * |∫ ω, J2 ω ∂ν| + |∫ ω, J1 ω ∂ν| := by rw [abs_mul]; norm_num
      _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hJ2b (by norm_num)) hJ1b

end
end RectangleCLT.Companion
