import RectangleCLTArxivV1.TransfersConditionalKernel

/-! Averaging the actual exceptional-data kernel. All first moments and
square-root Jensen bounds use the actual product of original marginal laws. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

/-- The width-dependent raw cutoff estimate, before optimization of the
cutoff or absorption of the small variance term. -/
theorem conditionalPolynomial_intrinsic_raw {p n : ℕ}
    (μ : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (μ i)]
    {B T q : ℝ} (h : ∀ i, ConditionalTruncationMomentHypotheses (μ i) B T q)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hB : 1 ≤ B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = originalAverageCovariance μ)
    (hunit : ∀ j, (A * A.transpose) j j = 1)
    (hv : truncationVarianceBudget B T q ≤ 1 / 4) :
    rectangleDistance (Measure.pi μ)
      (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A ≤
      conditionalIntrinsicBoundedCost n p T (gaussianMaximumMean A) +
        8 * gaussianMaximumMean A *
          (∫ x, ‖conditionalNormalizedShift μ T
            (observedTruncationMask T x, observedExceptionalArray T x)‖ ∂Measure.pi μ) +
        16 * gaussianMaximumMean A * Real.sqrt (dimensionLog p) *
          Real.sqrt (10 * truncationVarianceBudget B T q) +
        20 * gaussianMaximumMean A * Real.sqrt (2 * truncationVarianceBudget B T q * dimensionLog p) +
        12 * truncationVarianceBudget B T q := by
  let i : Fin n := ⟨0, by omega⟩
  let v := truncationVarianceBudget B T q
  let g := gaussianMaximumMean A
  let L := dimensionLog p
  let b := conditionalIntrinsicBoundedCost n p T g
  let s := 20 * g * Real.sqrt (2 * v * L)
  let d : (Fin n → Vector p) → ℝ := fun x => matrixMaxEntryNorm
    (conditionalCovarianceForMask μ T (observedTruncationMask T x) - A * A.transpose)
  let r : (Fin n → Vector p) → ℝ := fun x => ‖conditionalNormalizedShift μ T
    (observedTruncationMask T x, observedExceptionalArray T x)‖
  let f : (Fin n → Vector p) → ℝ := fun x => matrixMaxDiagonal
    (conditionalAllCovariance μ T - conditionalCovarianceForMask μ T (observedTruncationMask T x))
  let S : (Fin n → Vector p) → ℝ := fun x => Real.sqrt (f x)
  let F : (Fin n → Vector p) → ℝ := fun x => b + 8 * g * r x +
    (16 * g * Real.sqrt L) * S x + s + 2 * d x
  have hv0 : 0 ≤ v := (h i).varianceBudget_nonneg
  have hg : 0 ≤ g := gaussianMaximumMean_nonneg A
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hd0 (x : Fin n → Vector p) : 0 ≤ d x := norm_nonneg _
  have hf0 (x : Fin n → Vector p) : 0 ≤ f x := matrixMaxDiagonal_nonneg _
  have hiD : Integrable d (Measure.pi μ) := integrable_observedConditionalCovarianceDeviation μ T (A * A.transpose)
  have hiR : Integrable r (Measure.pi μ) := by
    simpa only [conditionalNormalizedShift] using observed_exceptional_shift_norm_integrable μ h
  have hiF0 : Integrable f (Measure.pi μ) := integrable_observedOmittedDiagonalMaximum μ T
  have hiS : Integrable S (Measure.pi μ) := integrable_sqrt_of_integrable_nonneg (Measure.pi μ) f hiF0 hf0
  have hi₁ := (integrable_const b).add (hiR.const_mul (8 * g))
  have hi₂ := hi₁.add (hiS.const_mul (16 * g * Real.sqrt L))
  have hi₃ := hi₂.add (integrable_const s)
  have hiF : Integrable F (Measure.pi μ) := hi₃.add (hiD.const_mul 2)
  have hEd : (∫ x, d x ∂Measure.pi μ) ≤ 6 * v := by
    dsimp only [d, v]
    rw [hA]
    exact Printed.expected_conditional_covariance_deviation_le μ h hn
  have hES : (∫ x, S x ∂Measure.pi μ) ≤ Real.sqrt (10 * v) := by
    apply (integral_sqrt_le_sqrt_integral (Measure.pi μ) f hiF0 hf0).trans
    apply Real.sqrt_le_sqrt
    have hh := expected_observedOmittedDiagonalMaximum_le μ h hn
    change (∫ x, f x ∂Measure.pi μ) ≤ 2 * v at hh
    exact hh.trans (by linarith)
  have hEF : (∫ x, F x ∂Measure.pi μ) = b + 8 * g * (∫ x, r x ∂Measure.pi μ) +
      (16 * g * Real.sqrt L) * (∫ x, S x ∂Measure.pi μ) + s + 2 * (∫ x, d x ∂Measure.pi μ) := by
    change (∫ x, ((b + 8 * g * r x) + (16 * g * Real.sqrt L) * S x + s) + 2 * d x ∂Measure.pi μ) = _
    have he₄ := integral_add hi₃ (hiD.const_mul 2)
    have he₃ := integral_add hi₂ (integrable_const s)
    have he₂ := integral_add hi₁ (hiS.const_mul (16 * g * Real.sqrt L))
    have he₁ := integral_add (integrable_const b) (hiR.const_mul (8 * g))
    simp only [Pi.add_apply] at he₄ he₃ he₂ he₁
    rw [he₄, he₃, he₂, he₁]
    simp only [integral_const_mul, integral_const, measureReal_univ_eq_one, one_smul]
  obtain ⟨C₀, hC₀⟩ := conditionalRetained_gaussian_factor_exists μ (h i).threshold_pos.le (fun _ => false)
  apply rectangleDistance_le
  intro R
  have hpoint (x : Fin n → Vector p) :
      rectangleError (conditionalTruncationKernel μ T
        (observedTruncationMask T x, observedExceptionalArray T x))
        (normalizedObservationSum (fun i (x : Fin n → Vector p) => x i)) A R ≤ F x := by
    have hh := conditionalKernel_rectangle_error_intrinsic_diagonal μ h hp hn hB
      (observedTruncationMask T x, observedExceptionalArray T x) A C₀ hA hunit hC₀ hv R
    convert hh using 1
    dsimp [conditionalIntrinsicKernelDiagonalCost, F, f, S, b, g, r, d, s, L]
    rw [Real.sqrt_mul (hf0 x)]
    ring
  have havg := (rectangleError_le_integral_conditionalKernel_rectangleError μ T A R).trans
    (integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) hiF (ae_of_all _ hpoint))
  rw [hEF] at havg
  have hES' := mul_le_mul_of_nonneg_left hES
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16) hg) (Real.sqrt_nonneg L))
  have hEd' := mul_le_mul_of_nonneg_left hEd (by norm_num : (0 : ℝ) ≤ 2)
  change _ ≤ b + 8 * g * (∫ x, r x ∂Measure.pi μ) +
    16 * g * Real.sqrt L * Real.sqrt (10 * v) + s + 12 * v
  linarith only [havg, hES', hEd']

end RectangleCLTArxivV1
