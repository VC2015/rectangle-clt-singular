import RectangleCLTCompanion.RestorationFourthBound

/-! Actual paired fourth-convolution restoration for the comparison path.
The Gaussian integration by parts, both selector partitions, and every
fresh/Gaussian Fubini step are discharged here. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem abs_restorationHessian_le
    (s : FaceSmoother p) (x y w : Vector p) {δ : ℝ}
    (hδ : 0 ≤ δ) (hy : ‖y‖ ≤ δ) (hw : ‖w‖ ≤ δ) :
    |restorationHessian s x y w| ≤ 3 * δ ^ 2 / s.bandwidth ^ 2 := by
  have hy' (j : Fin p) : |y j| ≤ δ := (norm_le_pi_norm y j).trans hy
  have hw' (j : Fin p) : |w j| ≤ δ := (norm_le_pi_norm w j).trans hw
  have hs : (∑ j, ∑ l, |s.mixedSecondDerivativeF x j l|) ≤ 3 / s.bandwidth ^ 2 :=
    (s.sum_abs_mixedSecondDerivativeF_le_variance x).trans
      (div_le_div_of_nonneg_right (by nlinarith [s.variance_le_one x]) (sq_nonneg _))
  calc
    _ ≤ ∑ j, ∑ l, |s.mixedSecondDerivativeF x j l * y j * w l| :=
      (Finset.abs_sum_le_sum_abs _ _).trans
        (Finset.sum_le_sum (fun j _ => Finset.abs_sum_le_sum_abs _ _))
    _ ≤ ∑ j, ∑ l, |s.mixedSecondDerivativeF x j l| * δ ^ 2 := by
      apply Finset.sum_le_sum
      intro j _
      apply Finset.sum_le_sum
      intro l _
      rw [abs_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left
        (by simpa only [pow_two] using mul_le_mul (hy' j) (hw' l) (abs_nonneg _) hδ)
        (abs_nonneg _)
    _ = δ ^ 2 * (∑ j, ∑ l, |s.mixedSecondDerivativeF x j l|) := by
      simp only [Finset.sum_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ ≤ δ ^ 2 * (3 / s.bandwidth ^ 2) := mul_le_mul_of_nonneg_left hs (sq_nonneg _)
    _ = _ := by ring

theorem integrable_fixedRestorationHessianIntegrand
    (s : FaceSmoother p) (μ : Measure Ξ) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (Z : Fin n → Ξ → Vector p) (Y W v : Fin n → Ξ → Vector p)
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    (hY : ∀ i, Measurable (Y i)) (hW : ∀ i, Measurable (W i))
    (hv : ∀ i, Measurable (v i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i a, ‖Y i a‖ ≤ δ) (hWb : ∀ i a, ‖W i a‖ ≤ δ) (i : Fin n) :
    Integrable (fun ag : Ξ × Vector p => repeatedDirectionScore ag.2 (Z i ag.1) *
      restorationHessian s (A.mulVec ag.2 + x + v i ag.1) (Y i ag.1) (W i ag.1))
        (μ.prod (standardGaussian p)) := by
  have hscore : Integrable
      (fun ag : Ξ × Vector p => repeatedDirectionScore ag.2 (Z i ag.1))
      (μ.prod (standardGaussian p)) := by
    simpa only [one_mul, mul_one] using
      integrable_restorationScore_product μ Z (fun _ _ => 1) (b := 1) hZ
        (fun _ => measurable_const.aestronglyMeasurable) (by intro _ _; norm_num)
        (fun _ => 1) measurable_const (by intro _; norm_num) i
  have hU : Measurable (fun ag : Ξ × Vector p => A.mulVec ag.2 + x + v i ag.1) :=
    (((measurable_mulVec A).comp measurable_snd).add measurable_const).add
      ((hv i).comp measurable_fst)
  have hm : Measurable (fun ag : Ξ × Vector p =>
      restorationHessian s (A.mulVec ag.2 + x + v i ag.1) (Y i ag.1) (W i ag.1)) := by
    unfold restorationHessian
    apply Finset.measurable_sum
    intro j _
    exact Finset.measurable_sum _ (fun l _ =>
      (((s.continuous_secondDerivative j l).measurable.comp hU).mul
        ((measurable_pi_apply j).comp ((hY i).comp measurable_fst))).mul
          ((measurable_pi_apply l).comp ((hW i).comp measurable_fst)))
  simpa only [mul_comm] using hscore.bdd_mul hm.aestronglyMeasurable
    ⟨3 * δ ^ 2 / s.bandwidth ^ 2, fun ag =>
      abs_restorationHessian_le s _ _ _ hδ (hYb i ag.1) (hWb i ag.1)⟩

def fixedRestorationFourthExpectation (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector p) (Y W v : Fin n → Ξ → Vector p) : ℝ :=
  ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (σ • A)) (x + v i a)
    (A.mulVec (Z i a)) (A.mulVec (Z i a)) (Y i a) (W i a) ∂μ

/-- Actual fresh-array expectation of the fourth convolution tensor; the
first repeated pair is removed by the checked Gaussian identity. -/
theorem fixedRestorationFourthExpectation_eq_score
    (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : σ ≠ 0) (x : Vector p)
    (Z : Fin n → Ξ → Vector p) (Y W v : Fin n → Ξ → Vector p)
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    (hY : ∀ i, Measurable (Y i)) (hW : ∀ i, Measurable (W i))
    (hv : ∀ i, Measurable (v i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i a, ‖Y i a‖ ≤ δ) (hWb : ∀ i a, ‖W i a‖ ≤ δ) :
    fixedRestorationFourthExpectation s μ A σ x Z Y W v =
      fixedRestorationHessianExpectation s μ (σ • A) x Z Y W v / σ ^ 2 := by
  unfold fixedRestorationFourthExpectation fixedRestorationHessianExpectation
  simp_rw [convolutionFourthTensor_repeated_score_scaled s A _ _ _ _ hσ, integral_div]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  have hi := integrable_fixedRestorationHessianIntegrand s μ (σ • A) x Z Y W v
    hZ hY hW hv hδ hYb hWb i
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => by
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g => by dsimp only; rw [add_assoc]))

variable {Ω : Type*} [MeasurableSpace Ω]

/-- Actual translated paired fourth-convolution restoration.  The matrix
estimate is explicit; no fourth-derivative bound is a premise. -/
theorem restorationFourthExpectation_integrable_and_bound
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : σ ≠ 0) (V : Ω → Vector p)
    (Z : Ω → Fin n → Ξ → Vector p) (Y W : Ω → Fin n → Ξ → Vector p)
    (v : Fin n → Ω → Ξ → Vector p) {δ K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν (σ • A) V C T)
    (hV : Measurable V) (hZm : ∀ ω i, Measurable (Z ω i))
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hY : ∀ ω i, Measurable (Y ω i)) (hW : ∀ ω i, Measurable (W ω i))
    (hv : ∀ i ω, Measurable (v i ω))
    (hδ : 0 ≤ δ) (hYb : ∀ ω i a, ‖Y ω i a‖ ≤ δ) (hWb : ∀ ω i a, ‖W ω i a‖ ≤ δ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤ K * vectorNormSq u)
    (hBm1 : ∀ (ℓ : ℕ) (α : Fin 1 → Face p) (β : Fin ℓ → Face p) (j l : Fin p),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z
        (restorationHessianCoefficientsOne Y W) v α β ω j l))
    (hBm2 : ∀ (ℓ : ℕ) (α : Fin 2 → Face p) (β : Fin ℓ → Face p) (j l : Fin p),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z
        (restorationHessianCoefficientsTwo Y W) v α β ω j l))
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Integrable (fun ω => fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω)) ν ∧
    |∫ ω, fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω) ∂ν| ≤
        (2 * restorationSelectorCap s (δ ^ 2) K R C T 2 +
          restorationSelectorCap s (δ ^ 2) K R C T 1) /
            (s.bandwidth ^ 2 * σ ^ 2) := by
  have hh := restorationHessianExpectation_integrable_and_bound s ν μ (σ • A) V
    Z Y W v hmatrix hV hZm hZ hY hW hv hYb hWb hK hR hvb hbudget hBm1 hBm2 hC hT hsmall
  have hp (ω : Ω) :
      fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω) (Y ω) (W ω) (fun i => v i ω) =
        fixedRestorationHessianExpectation s μ (σ • A) (V ω) (Z ω)
          (Y ω) (W ω) (fun i => v i ω) / σ ^ 2 :=
    fixedRestorationFourthExpectation_eq_score s μ A hσ (V ω) (Z ω) (Y ω) (W ω)
      (fun i => v i ω) (hZ ω) (hY ω) (hW ω) (fun i => hv i ω) hδ (hYb ω) (hWb ω)
  constructor
  · convert hh.1.div_const (σ ^ 2) using 1
    funext ω
    exact hp ω
  · have heq : (∫ ω, fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω)
        (Y ω) (W ω) (fun i => v i ω) ∂ν) =
        (∫ ω, fixedRestorationHessianExpectation s μ (σ • A) (V ω) (Z ω)
          (Y ω) (W ω) (fun i => v i ω) ∂ν) / σ ^ 2 := by
      simp_rw [hp]
      rw [integral_div]
    rw [heq, abs_div, abs_of_nonneg (sq_nonneg σ)]
    simpa only [div_div] using div_le_div_of_nonneg_right hh.2 (sq_nonneg σ)

end
end RectangleCLT.Companion
