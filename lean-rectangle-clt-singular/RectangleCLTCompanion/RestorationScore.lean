import RectangleCLTCompanion.RestorationCoefficients

/-! Actual repeated-direction Gaussian score and its finite coefficient trace
identity.  Gaussian integration by parts is deliberately a separate result:
the statements here are exact moment algebra with all moments integrable. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {r n : ℕ} {Ω : Type*} [MeasurableSpace Ω]

/-- The second standard-Gaussian score in a repeated direction. -/
def repeatedDirectionScore (g z : Vector r) : ℝ :=
  (faceDot z g) ^ 2 - vectorNormSq z

theorem repeatedDirectionScore_eq_quadratic (g z : Vector r) :
    repeatedDirectionScore g z = matrixQuadratic (rankOne g - 1) z := by
  classical
  simp only [repeatedDirectionScore, matrixQuadratic, Matrix.sub_apply,
    mul_sub, sub_mul, Finset.sum_sub_distrib, rankOne, Matrix.one_apply]
  rw [← matrixQuadratic_rankOne_eq_square g z]
  congr 1
  simp [vectorNormSq, matrixQuadratic, pow_two]

theorem integrable_repeatedDirectionScore_weight (ν : Measure Ω)
    (g : Ω → Vector r) (w : Ω → ℝ)
    (hw : Integrable w ν)
    (hgg : ∀ j k, Integrable (fun a => g a j * g a k * w a) ν)
    (z : Vector r) :
    Integrable (fun a => repeatedDirectionScore (g a) z * w a) ν := by
  classical
  have h (j k : Fin r) : Integrable
      (fun a => z j * ((g a j * g a k - if j = k then 1 else 0) * w a) * z k) ν := by
    convert (((hgg j k).sub (hw.const_mul (if j = k then 1 else 0))).const_mul
      (z j)).mul_const (z k) using 1
    funext a
    dsimp only [Pi.sub_apply]
    ring
  have hs := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => h j k))
  convert hs using 1
  funext a
  rw [repeatedDirectionScore_eq_quadratic]
  simp only [matrixQuadratic, Matrix.sub_apply, rankOne, Matrix.one_apply,
    Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- The repeated-direction score is the quadratic form of the actual
weighted Gaussian score matrix, rather than a named abstract covariance. -/
theorem integral_repeatedDirectionScore_eq_quadratic (ν : Measure Ω)
    (g : Ω → Vector r) (w : Ω → ℝ)
    (hw : Integrable w ν)
    (hgg : ∀ j k, Integrable (fun a => g a j * g a k * w a) ν)
    (z : Vector r) :
    (∫ a, repeatedDirectionScore (g a) z * w a ∂ν) =
      matrixQuadratic (weightedScore ν g w) z := by
  have hi (j k : Fin r) : Integrable
      (fun a => (g a j * g a k - if j = k then 1 else 0) * w a) ν := by
    convert (hgg j k).sub (hw.const_mul (if j = k then 1 else 0)) using 1
    funext a
    dsimp only [Pi.sub_apply]
    ring
  unfold weightedScore
  rw [matrixQuadratic_integral ν _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => by
    dsimp only
    rw [repeatedDirectionScore_eq_quadratic]
    simp only [matrixQuadratic, Matrix.sub_apply, rankOne, Matrix.one_apply,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring)

theorem trace_mul_integral (ν : Measure Ω)
    (B : Matrix (Fin r) (Fin r) ℝ) (D : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hD : ∀ j k, Integrable (fun a => D a j k) ν) :
    Matrix.trace (B * Matrix.of (fun j k => ∫ a, D a j k ∂ν)) =
      ∫ a, Matrix.trace (B * D a) ∂ν := by
  change (∑ j, ∑ k, B j k * (∫ a, D a k j ∂ν)) =
    ∫ a, ∑ j, ∑ k, B j k * D a k j ∂ν
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (hD k j).const_mul (B j k)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => (hD k j).const_mul (B j k))]
  simp only [integral_const_mul]

/-- Fresh directions may be dependent on their bounded coefficient.  This
trace identity is the exact repeated-direction summation used in restoration. -/
theorem trace_restorationCoefficient_mul (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b)
    (W : Matrix (Fin r) (Fin r) ℝ) :
    Matrix.trace (restorationCoefficient μ Z c * W) =
      ∑ i, ∫ a, c i a * matrixQuadratic W (Z i a) ∂μ := by
  rw [Matrix.trace_mul_comm]
  have heq : restorationCoefficient μ Z c =
      ∑ i, (fun j k => ∫ a, c i a * (Z i a j * Z i a k) ∂μ) := by
    ext j k
    simp [restorationCoefficient, Finset.sum_apply]
  rw [heq, Matrix.mul_sum, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  change Matrix.trace (W * Matrix.of (fun j k => ∫ a, c i a * (Z i a j * Z i a k) ∂μ)) = _
  rw [trace_mul_integral μ W _
    (fun j k => integrable_restorationCoefficient_entry μ Z c hZ hc hb i j k)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => by
    dsimp only
    have heq' : (fun j k => c i a * (Z i a j * Z i a k)) =
        c i a • rankOne (Z i a) := by ext j k; rfl
    rw [heq', Matrix.mul_smul, Matrix.trace_smul, trace_mul_rankOne, smul_eq_mul])

/-- Concrete product-Gaussian version of the coefficient trace identity.
The fresh-array law appears outside the Gaussian expectation; no
conditioning or independence oracle is assumed. -/
theorem sum_integral_repeatedDirectionScore_eq_trace (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b)
    (w : Vector r → ℝ) (hw : Measurable w) (hwb : ∀ g, |w g| ≤ 1) :
    (∑ i, ∫ a, c i a * (∫ g, repeatedDirectionScore g (Z i a) * w g
        ∂standardGaussian r) ∂μ) =
      Matrix.trace (restorationCoefficient μ Z c *
        weightedScore (standardGaussian r) id w) := by
  calc
    _ = ∑ i, ∫ a, c i a *
        matrixQuadratic (weightedScore (standardGaussian r) id w) (Z i a) ∂μ := by
      apply Finset.sum_congr rfl
      intro i _
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => congrArg (fun t => c i a * t)
        (integral_repeatedDirectionScore_eq_quadratic (standardGaussian r) id w
          (standardGaussian_integrable_bounded_weight w hw hwb)
          (standardGaussian_integrable_weighted_product w hw hwb) (Z i a)))
    _ = _ := (trace_restorationCoefficient_mul μ Z c hZ hc hb _).symm

/-- The full fresh-array/Gaussian integrand is integrable.  Thus the trace
identity is also a genuine product-law/Fubini identity, not merely algebra
between possibly undefined iterated integrals. -/
theorem integrable_restorationScore_product (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b)
    (w : Vector r → ℝ) (hw : Measurable w) (hwb : ∀ g, |w g| ≤ 1)
    (i : Fin n) :
    Integrable (fun ag : Ω × Vector r =>
      c i ag.1 * (repeatedDirectionScore ag.2 (Z i ag.1) * w ag.2))
      (μ.prod (standardGaussian r)) := by
  classical
  have hg (j k : Fin r) : Integrable
      (fun g : Vector r => (g j * g k - if j = k then 1 else 0) * w g)
      (standardGaussian r) := by
    convert (standardGaussian_integrable_weighted_product w hw hwb j k).sub
      ((standardGaussian_integrable_bounded_weight w hw hwb).const_mul
        (if j = k then 1 else 0)) using 1
    funext g
    dsimp only [Pi.sub_apply]
    ring
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (integrable_restorationCoefficient_entry μ Z c hZ hc hb i j k).mul_prod (hg j k)))
  convert hi using 1
  funext ag
  rw [repeatedDirectionScore_eq_quadratic]
  simp only [matrixQuadratic, Matrix.sub_apply, rankOne, Matrix.one_apply,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- Actual independent fresh-array/Gaussian experiment. -/
theorem sum_integral_restorationScore_product_eq_trace (μ : Measure Ω) [SFinite μ]
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b)
    (w : Vector r → ℝ) (hw : Measurable w) (hwb : ∀ g, |w g| ≤ 1) :
    (∑ i, ∫ ag : Ω × Vector r,
      c i ag.1 * (repeatedDirectionScore ag.2 (Z i ag.1) * w ag.2)
        ∂μ.prod (standardGaussian r)) =
      Matrix.trace (restorationCoefficient μ Z c *
        weightedScore (standardGaussian r) id w) := by
  rw [← sum_integral_repeatedDirectionScore_eq_trace μ Z c hZ hc hb w hw hwb]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_prod _ (integrable_restorationScore_product μ Z c hZ hc hb w hw hwb i)]
  simp only [integral_const_mul]

end
end RectangleCLT.Companion
