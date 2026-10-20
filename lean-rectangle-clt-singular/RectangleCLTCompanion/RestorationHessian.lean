import RectangleCLTCompanion.RestorationTensorIBP

/-! Actual paired fourth-derivative restoration reduced to the two exact
Hessian selector partitions. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r n : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

theorem integrable_fixedRestorationIntegrand
    (s : FaceSmoother p) (μ : Measure Ξ)
    (Z : Fin n → Ξ → Vector r)
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    {k : ℕ} (c : Fin n → (Fin k → Face p) → Ξ → ℝ)
    (U : Ξ × Vector r → Vector p) (hU : Measurable U)
    (hc : ∀ i α, Measurable (c i α)) {b : ℝ}
    (hb : ∀ i α a, |c i α a| ≤ b) (hb0 : 0 ≤ b) (i : Fin n) :
    Integrable (fun ag : Ξ × Vector r => ∑ α : Fin k → Face p,
      (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
        selectorTupleWeight s α (U ag)) (μ.prod (standardGaussian r)) := by
  let M : Ξ × Vector r → ℝ := fun ag =>
    ∑ α : Fin k → Face p, c i α ag.1 * selectorTupleWeight s α (U ag)
  have hMm : Measurable M := Finset.measurable_sum _ (fun α _ =>
    ((hc i α).comp measurable_fst).mul (measurable_selectorTupleWeight_comp s α U hU))
  have hMb (ag : Ξ × Vector r) : |M ag| ≤ b := by
    calc
      _ ≤ ∑ α : Fin k → Face p, |c i α ag.1| * selectorTupleWeight s α (U ag) := by
        simpa only [abs_mul, abs_of_nonneg (selectorTupleWeight_nonneg s _ _)] using
          Finset.abs_sum_le_sum_abs
            (fun α : Fin k → Face p => c i α ag.1 * selectorTupleWeight s α (U ag)) Finset.univ
      _ ≤ ∑ α : Fin k → Face p, b * selectorTupleWeight s α (U ag) :=
        Finset.sum_le_sum (fun α _ => mul_le_mul_of_nonneg_right (hb i α ag.1)
          (selectorTupleWeight_nonneg s α _))
      _ = b * ∑ α : Fin k → Face p, selectorTupleWeight s α (U ag) := (Finset.mul_sum ..).symm
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left (sum_selectorTupleWeight_le_one s k _) hb0
      _ = b := mul_one _
  have hscore : Integrable
      (fun ag : Ξ × Vector r => repeatedDirectionScore ag.2 (Z i ag.1))
      (μ.prod (standardGaussian r)) := by
    simpa only [one_mul, mul_one] using
      integrable_restorationScore_product μ Z (fun _ _ => 1) (b := 1) hZ
        (fun _ => measurable_const.aestronglyMeasurable) (by intro _ _; norm_num)
        (fun _ => 1) measurable_const (by intro _; norm_num) i
  have hi := hscore.bdd_mul hMm.aestronglyMeasurable ⟨b, hMb⟩
  convert hi using 1
  funext ag
  dsimp only [M]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro α _
  ring

def restorationHessianCoefficientOne (Y W : Fin n → Ξ → Vector p)
    (i : Fin n) (α : Fin 1 → Face p) (a : Ξ) : ℝ :=
  FaceSmoother.normalDot (α 0) (Y i a) * FaceSmoother.normalDot (α 0) (W i a)

def restorationHessianCoefficientTwo (Y W : Fin n → Ξ → Vector p)
    (i : Fin n) (α : Fin 2 → Face p) (a : Ξ) : ℝ :=
  FaceSmoother.normalDot (α 0) (Y i a) * FaceSmoother.normalDot (α 1) (W i a)

def fixedRestorationHessianExpectation (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (Y W v : Fin n → Ξ → Vector p) : ℝ :=
  ∑ i, ∫ ag : Ξ × Vector r, repeatedDirectionScore ag.2 (Z i ag.1) *
    restorationHessian s (A.mulVec ag.2 + x + v i ag.1) (Y i ag.1) (W i ag.1)
      ∂μ.prod (standardGaussian r)

omit [MeasurableSpace Ξ] in
theorem restorationHessianCoefficient_abs_le {Y W : Fin n → Ξ → Vector p}
    {δ : ℝ} (hY : ∀ i a, ‖Y i a‖ ≤ δ) (hW : ∀ i a, ‖W i a‖ ≤ δ)
    (i : Fin n) (f g : Face p) (a : Ξ) :
    |FaceSmoother.normalDot f (Y i a) * FaceSmoother.normalDot g (W i a)| ≤ δ ^ 2 := by
  rw [abs_mul, pow_two]
  exact mul_le_mul (FaceSmoother.abs_normalDot_le_of_norm_le f (hY i a))
    (FaceSmoother.abs_normalDot_le_of_norm_le g (hW i a)) (abs_nonneg _)
    ((norm_nonneg (Y i a)).trans (hY i a))

/-- Both actual derivative partitions, with the fresh directions and the
Gaussian score still inside the real product experiment. -/
theorem fixedRestorationHessianExpectation_eq_partitions
    (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (Y W v : Fin n → Ξ → Vector p)
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    (hY : ∀ i, Measurable (Y i)) (hW : ∀ i, Measurable (W i))
    (hv : ∀ i, Measurable (v i)) {δ : ℝ}
    (hYb : ∀ i a, ‖Y i a‖ ≤ δ) (hWb : ∀ i a, ‖W i a‖ ≤ δ) :
    fixedRestorationHessianExpectation s μ A x Z Y W v =
      (2 * fixedRestorationTranslatedExpectation s μ A x Z
        (restorationHessianCoefficientTwo Y W) v -
        fixedRestorationTranslatedExpectation s μ A x Z
          (restorationHessianCoefficientOne Y W) v) / s.bandwidth ^ 2 := by
  have hA : Measurable (fun ag : Ξ × Vector r => A.mulVec ag.2 + x) := by
    have hm : Measurable (fun g : Vector r => A.mulVec g) := by
      apply measurable_pi_lambda
      intro l
      change Measurable (fun g : Vector r => ∑ j, A l j * g j)
      exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
    exact (hm.add measurable_const).comp measurable_snd
  have hU (i : Fin n) := hA.add ((hv i).comp measurable_fst)
  have hc1 (i : Fin n) (α : Fin 1 → Face p) :
      Measurable (restorationHessianCoefficientOne Y W i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i))
  have hc2 (i : Fin n) (α : Fin 2 → Face p) :
      Measurable (restorationHessianCoefficientTwo Y W i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hW i))
  have hi1 (i : Fin n) := integrable_fixedRestorationIntegrand s μ Z hZ
    (restorationHessianCoefficientOne Y W) _ (hU i) hc1
    (fun i α a => restorationHessianCoefficient_abs_le hYb hWb i (α 0) (α 0) a)
    (sq_nonneg δ) i
  have hi2 (i : Fin n) := integrable_fixedRestorationIntegrand s μ Z hZ
    (restorationHessianCoefficientTwo Y W) _ (hU i) hc2
    (fun i α a => restorationHessianCoefficient_abs_le hYb hWb i (α 0) (α 1) a)
    (sq_nonneg δ) i
  have hp (i : Fin n) (ag : Ξ × Vector r) :
      repeatedDirectionScore ag.2 (Z i ag.1) *
        restorationHessian s (A.mulVec ag.2 + x + v i ag.1) (Y i ag.1) (W i ag.1) =
      (2 * (∑ α : Fin 2 → Face p,
        (restorationHessianCoefficientTwo Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1)) -
      (∑ α : Fin 1 → Face p,
        (restorationHessianCoefficientOne Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1))) / s.bandwidth ^ 2 := by
    rw [restorationHessian_eq_selector_partitions]
    rw [← mul_div_assoc]
    congr 1
    rw [mul_sub]
    congr 1
    · rw [mul_left_comm _ (2 : ℝ)]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      unfold restorationHessianCoefficientTwo
      ring
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      unfold restorationHessianCoefficientOne
      ring
  unfold fixedRestorationHessianExpectation
  simp_rw [hp, integral_div]
  have hs (i : Fin n) := integral_sub ((hi2 i).const_mul 2) (hi1 i)
  have hs' (i : Fin n) :
      (∫ ag : Ξ × Vector r,
        2 * (∑ α : Fin 2 → Face p,
          (restorationHessianCoefficientTwo Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
            selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1)) -
        (∑ α : Fin 1 → Face p,
          (restorationHessianCoefficientOne Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
            selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1))
          ∂μ.prod (standardGaussian r)) =
      2 * (∫ ag : Ξ × Vector r, ∑ α : Fin 2 → Face p,
        (restorationHessianCoefficientTwo Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1) ∂μ.prod (standardGaussian r)) -
      (∫ ag : Ξ × Vector r, ∑ α : Fin 1 → Face p,
        (restorationHessianCoefficientOne Y W i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1) ∂μ.prod (standardGaussian r)) := by
    have hsi := hs i
    simp only [Function.comp_apply] at hsi
    rw [integral_const_mul] at hsi
    exact hsi
  simp_rw [hs']
  simp only [fixedRestorationTranslatedExpectation, ← Finset.sum_div,
    Finset.sum_sub_distrib, Finset.mul_sum]

end
end RectangleCLT.Companion
