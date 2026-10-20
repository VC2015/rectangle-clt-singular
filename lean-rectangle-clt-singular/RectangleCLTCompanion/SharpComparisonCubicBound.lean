import RectangleCLTCompanion.SharpComparisonCubic
import RectangleCLTCompanion.RestorationBound

open MeasureTheory
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace RectangleCLT.Companion

noncomputable section

variable {p r n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

/-- Truncation only on an exceptional null set permits pointwise coefficient
bounds while leaving every actual integral unchanged. -/
def cubicClippedCoefficient (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Fin n → Ξ → Vector r) (δ : ℝ) (f : Face p) (i : Fin n) (a : Ξ) : ℝ :=
  if |FaceSmoother.normalDot f (A.mulVec (Z i a))| ≤ δ then
    FaceSmoother.normalDot f (A.mulVec (Z i a)) else 0

def cubicFaceCoefficient (μ : Measure Ξ) (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Fin n → Ξ → Vector r) (δ : ℝ) (f : Face p) : Matrix (Fin r) (Fin r) ℝ :=
  restorationCoefficient μ Z (cubicClippedCoefficient A Z δ f)

private theorem measurable_projected (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Ξ → Vector r) (hZ : Measurable Z) : Measurable (fun a => A.mulVec (Z a)) := by
  apply measurable_pi_lambda
  intro j
  exact Finset.measurable_sum Finset.univ (fun k _ =>
    measurable_const.mul ((measurable_pi_apply k).comp hZ))

theorem cubicClippedCoefficient_measurable (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Fin n → Ξ → Vector r) (hZ : ∀ i, Measurable (Z i))
    (δ : ℝ) (f : Face p) (i : Fin n) : Measurable (cubicClippedCoefficient A Z δ f i) := by
  have hc := (FaceSmoother.continuous_normalDot f).measurable.comp
    (measurable_projected A (Z i) (hZ i))
  exact Measurable.ite (measurableSet_le hc.abs measurable_const) hc measurable_const

omit [MeasurableSpace Ξ] in
theorem abs_cubicClippedCoefficient_le (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Fin n → Ξ → Vector r) {δ : ℝ} (hδ : 0 ≤ δ)
    (f : Face p) (i : Fin n) (a : Ξ) :
    |cubicClippedCoefficient A Z δ f i a| ≤ δ := by
  unfold cubicClippedCoefficient
  split_ifs with h
  · exact h
  · simpa using hδ

theorem cubicClippedCoefficient_eq_ae (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Fin n → Ξ → Vector r) {δ : ℝ}
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ) (f : Face p) (i : Fin n) :
    cubicClippedCoefficient A Z δ f i =ᵐ[μ]
      (fun a => FaceSmoother.normalDot f (A.mulVec (Z i a))) := by
  filter_upwards [hb i] with a ha
  unfold cubicClippedCoefficient
  rw [if_pos]
  exact FaceSmoother.abs_normalDot_le_of_norm_le f ha

/-- The actual support-row covariance budget controls every signed face
coefficient, including when the full covariance is singular. -/
theorem cubicFaceCoefficient_quadratic_le (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Fin n → Ξ → Vector r)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    {δ : ℝ} (hδ : 0 ≤ δ)
    (hbudget : ∀ u : Vector r, ∑ i, ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ ≤ vectorNormSq u)
    (f : Face p) (u : Vector r) :
    |matrixQuadratic (cubicFaceCoefficient μ A Z δ f) u| ≤ δ * vectorNormSq u := by
  simpa only [mul_one, one_mul] using abs_matrixQuadratic_restorationCoefficient_le μ Z
    (cubicClippedCoefficient A Z δ f) hZ
    (fun i => (cubicClippedCoefficient_measurable A Z hZm δ f i).aestronglyMeasurable)
    (abs_cubicClippedCoefficient_le A Z hδ f) hδ
    (K := 1) (by simpa only [one_mul] using hbudget) u

/-- Actual independent fresh-row/Gaussian cubic expectation at a supplied
base. Its signed row sum is taken before its absolute value. -/
def cubicGaussianSum (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Fin n → Ξ → Vector r)
    (x : Vector p) (σ : ℝ) : ℝ :=
  ∑ i, ∫ a, (∫ g,
    s.translationD3 ((σ • A).mulVec g + x) (A.mulVec (Z i a))
      ∂standardGaussian r) ∂μ

theorem cubicGaussianSum_eq_selector_scores (s : FaceSmoother p)
    (μ : Measure Ξ) [SFinite μ] (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Fin n → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (x : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    cubicGaussianSum s μ A Z x σ = -(1 / (s.bandwidth * σ ^ 2)) *
      ∑ f : Face p, Matrix.trace (cubicFaceCoefficient μ A Z δ f *
        weightedScore (standardGaussian r) id
          (fun g => selectorTupleWeight s (fun _ : Fin 1 => f) ((σ • A).mulVec g + x))) := by
  let w := fun (f : Face p) (g : Vector r) =>
    selectorTupleWeight s (fun _ : Fin 1 => f) ((σ • A).mulVec g + x)
  have hw (f : Face p) : Measurable (w f) := by
    exact measurable_selectorTupleWeight_comp s _ _
      ((measurable_projected (σ • A) id measurable_id).add measurable_const)
  have hwb (f : Face p) (g : Vector r) : |w f g| ≤ 1 := by
    rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]
    exact selectorTupleWeight_le_one s _ _
  have hi (i : Fin n) (f : Face p) : Integrable (fun a =>
      cubicClippedCoefficient A Z δ f i a *
        (∫ g, repeatedDirectionScore g (Z i a) * w f g ∂standardGaussian r)) μ := by
    have hh := integrable_restorationScore_product μ Z (cubicClippedCoefficient A Z δ f)
      hZ (fun i => (cubicClippedCoefficient_measurable A Z hZm δ f i).aestronglyMeasurable)
      (abs_cubicClippedCoefficient_le A Z hδ f) (w f) (hw f) (hwb f) i
    simpa only [integral_const_mul] using hh.integral_prod_left
  have hone (i : Fin n) :
      (∫ a, (∫ g, s.translationD3 ((σ • A).mulVec g + x) (A.mulVec (Z i a))
        ∂standardGaussian r) ∂μ) =
      -(1 / (s.bandwidth * σ ^ 2)) * ∑ f : Face p, ∫ a,
        cubicClippedCoefficient A Z δ f i a *
          (∫ g, repeatedDirectionScore g (Z i a) * w f g ∂standardGaussian r) ∂μ := by
    calc
      _ = ∫ a, -(1 / (s.bandwidth * σ ^ 2)) * ∑ f : Face p,
          cubicClippedCoefficient A Z δ f i a *
            (∫ g, repeatedDirectionScore g (Z i a) * w f g ∂standardGaussian r) ∂μ := by
        apply integral_congr_ae
        filter_upwards [hb i] with a ha
        rw [cubic_repeated_gaussian_eq_face_scores s A x (Z i a) hσ]
        congr 1
        apply Finset.sum_congr rfl
        intro f _
        unfold cubicClippedCoefficient
        rw [if_pos (FaceSmoother.abs_normalDot_le_of_norm_le f ha)]
      _ = _ := by
        rw [integral_const_mul, integral_finset_sum _ (fun f _ => hi i f)]
  unfold cubicGaussianSum
  simp_rw [hone]
  rw [← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro f _
  exact sum_integral_repeatedDirectionScore_eq_trace μ Z (cubicClippedCoefficient A Z δ f)
    hZ (fun i => (cubicClippedCoefficient_measurable A Z hZm δ f i).aestronglyMeasurable)
    (abs_cubicClippedCoefficient_le A Z hδ f) (w f) (hw f) (hwb f)

private theorem sum_faces_fin_one (g : (Fin 1 → Face p) → ℝ) :
    (∑ α, g α) = ∑ f : Face p, g (fun _ : Fin 1 => f) := by
  let e : (Fin 1 → Face p) ≃ Face p :=
    { toFun := fun α => α 0
      invFun := fun f _ => f
      left_inv := by
        intro α
        funext j
        exact congrArg α (Subsingleton.elim 0 j)
      right_inv := fun _ => rfl }
  have hh := Equiv.sum_comp e.symm g
  exact hh.symm

/-- Unshifted cubic restoration from the actual q=1 averaged selector
matrix estimate. All directions and all Gaussian derivatives are genuine,
and only the actual support-row quadratic budget is used. -/
theorem abs_integral_cubicGaussianSum_le_of_matrix_estimate
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Fin n → Ξ → Vector r)
    (V : Ω → Vector p) (hV : Measurable V)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    {δ C T σ : ℝ} (hδ : 0 ≤ δ) (hσ : σ ≠ 0)
    (hb : ∀ i, ∀ᵐ a ∂μ, ‖A.mulVec (Z i a)‖ ≤ δ)
    (hbudget : ∀ u : Vector r, ∑ i, ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ ≤ vectorNormSq u)
    (hmatrix : AveragedSelectorMatrixEstimate s ν (σ • A) V C T) :
    |∫ ω, cubicGaussianSum s μ A Z (V ω) σ ∂ν| ≤
      δ * C ^ 2 * T / (s.bandwidth * σ ^ 2) := by
  let B := fun (α : Fin 1 → Face p) (_ : Ω) => cubicFaceCoefficient μ A Z δ (α 0)
  let M := fun ω => ∑ f : Face p, Matrix.trace (cubicFaceCoefficient μ A Z δ f *
    selectorGaussianScore s (σ • A) V (fun _ : Fin 1 => f) ω)
  let H := fun ω => ∑ f : Face p, |Matrix.trace (cubicFaceCoefficient μ A Z δ f *
    selectorGaussianScore s (σ • A) V (fun _ : Fin 1 => f) ω)|
  have he := hmatrix 1 (by decide) δ hδ B
    (fun _ _ _ => measurable_const)
    (fun α _ u => cubicFaceCoefficient_quadratic_le μ A Z hZm hZ hδ hbudget (α 0) u)
  have hsum (ω : Ω) : (∑ α : Fin 1 → Face p,
      |Matrix.trace (B α ω * selectorGaussianScore s (σ • A) V α ω)|) = H ω := by
    exact sum_faces_fin_one _
  have hiH : Integrable H ν := he.1.congr (ae_of_all _ hsum)
  have hHbound : (∫ ω, H ω ∂ν) ≤ δ * C ^ 2 * T := by
    convert he.2 using 1
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => (hsum ω).symm)
  have hMm : Measurable M := by
    apply Finset.measurable_sum
    intro f _
    change Measurable (fun ω => ∑ j, ∑ k,
      cubicFaceCoefficient μ A Z δ f j k *
        selectorGaussianScore s (σ • A) V (fun _ : Fin 1 => f) ω k j)
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul (measurable_selectorGaussianScore s _ V hV _ k j)
  have hnorm (ω : Ω) : ‖M ω‖ ≤ H ω := by
    exact Finset.abs_sum_le_sum_abs _ _
  have hiM : Integrable M ν := hiH.mono' hMm.aestronglyMeasurable (ae_of_all _ hnorm)
  have heq (ω : Ω) : cubicGaussianSum s μ A Z (V ω) σ =
      -(1 / (s.bandwidth * σ ^ 2)) * M ω :=
    cubicGaussianSum_eq_selector_scores s μ A Z hZm hZ hδ hb (V ω) hσ
  have heq' := integral_congr_ae (ae_of_all ν heq)
  have hden : 0 < s.bandwidth * σ ^ 2 := mul_pos s.bandwidth_pos (sq_pos_of_ne_zero hσ)
  have hcoef : 0 ≤ (1 / (s.bandwidth * σ ^ 2)) := (div_pos (by norm_num) hden).le
  rw [heq', integral_const_mul, abs_mul, abs_neg,
    abs_of_pos (div_pos (by norm_num) (mul_pos s.bandwidth_pos (sq_pos_of_ne_zero hσ)))]
  calc
    _ ≤ (1 / (s.bandwidth * σ ^ 2)) * ∫ ω, H ω ∂ν := by
      apply mul_le_mul_of_nonneg_left _ hcoef
      exact abs_integral_le_integral_abs.trans
        (integral_mono_ae hiM.abs hiH (ae_of_all _ hnorm))
    _ ≤ (1 / (s.bandwidth * σ ^ 2)) * (δ * C ^ 2 * T) :=
      mul_le_mul_of_nonneg_left hHbound hcoef
    _ = _ := by ring

end
end RectangleCLT.Companion
