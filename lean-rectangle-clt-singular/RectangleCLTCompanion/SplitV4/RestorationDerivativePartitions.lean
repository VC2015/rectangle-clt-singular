import RectangleCLTCompanion.SplitV4.RestorationConditionalStein
import RectangleCLTCompanion.SharpComparisonCubic

/-! Exact first/second derivative selector partitions and the actual B.2
paired derivative expectations after the two Stein identities. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def restorationGradientCoefficient {Ω : Type*} {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (i : Fin n) (α : Fin 1 → Face p) (ω : Ω) : ℝ :=
  FaceSmoother.normalDot (α 0) (Y i ω)

theorem translationD1_eq_selector_partition {p : ℕ} (s : FaceSmoother p) (x y : Vector p) :
    s.translationD1 x y = -(1 / s.bandwidth) *
      ∑ α : Fin 1 → Face p, FaceSmoother.normalDot (α 0) y * selectorTupleWeight s α x := by
  have he := firstDerivative_contraction_eq_faces s x y
  have hsum : s.translationD1 x y = ∑ j, y j * s.coordinateDerivativeF x j :=
    Finset.sum_congr rfl (fun j _ => mul_comm _ _)
  rw [hsum, he, restoration_sum_pi_fin_one]
  rfl

theorem integrable_bounded_selector_score_sum
    {Ω : Type*} [MeasurableSpace Ω] {p r k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Z : Ω → Vector r) (hZ : ∀ j l, Integrable (fun ω => Z ω j * Z ω l) μ)
    (c : (Fin k → Face p) → Ω → ℝ) (hc : ∀ α, Measurable (c α))
    (X : Ω × Vector r → Vector p) (hX : Measurable X) {b : ℝ} (hb : 0 ≤ b)
    (hcb : ∀ α, ∀ᵐ ω ∂μ, |c α ω| ≤ b) :
    Integrable (fun z : Ω × Vector r => ∑ α : Fin k → Face p,
      (c α z.1 * repeatedDirectionScore z.2 (Z z.1)) * selectorTupleWeight s α (X z))
      (μ.prod (standardGaussian r)) := by
  let M : Ω × Vector r → ℝ := fun z => ∑ α : Fin k → Face p, c α z.1 * selectorTupleWeight s α (X z)
  have hM : Measurable M := Finset.measurable_sum _ (fun α _ => ((hc α).comp measurable_fst).mul
    (measurable_selectorTupleWeight_comp s α X hX))
  have hcbp (α : Fin k → Face p) : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), |c α z.1| ≤ b :=
    restoration_ae_abs_fst_le μ (standardGaussian r) (c α) (hc α) (hcb α)
  have hMb : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ‖M z‖ ≤ b := by
    filter_upwards [ae_all_iff.mpr hcbp] with z hz
    rw [Real.norm_eq_abs]
    calc
      _ ≤ ∑ α, |c α z.1| * selectorTupleWeight s α (X z) := by
        simpa only [abs_mul, abs_of_nonneg (selectorTupleWeight_nonneg s _ _)] using
          Finset.abs_sum_le_sum_abs (fun α => c α z.1 * selectorTupleWeight s α (X z)) Finset.univ
      _ ≤ ∑ α, b * selectorTupleWeight s α (X z) := Finset.sum_le_sum (fun α _ =>
        mul_le_mul_of_nonneg_right (hz α) (selectorTupleWeight_nonneg s α _))
      _ = b * ∑ α, selectorTupleWeight s α (X z) := (Finset.mul_sum _ _ _).symm
      _ ≤ b * 1 := mul_le_mul_of_nonneg_left (sum_selectorTupleWeight_le_one s k _) hb
      _ = b := mul_one _
  have hi := (integrable_random_repeatedDirectionScore μ Z hZ).bdd_mul' hM.aestronglyMeasurable hMb
  convert hi using 1
  funext z
  simp only [M, Finset.sum_mul]
  exact Finset.sum_congr rfl (fun α _ => by ring)

def restorationScoreExpectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (Z : Fin n → Ω → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ) (v : Fin n → Ω → Vector p) : ℝ :=
  ∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
    (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
      selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1) ∂μ.prod (standardGaussian r)

def restorationThirdExpectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (Z : Fin n → Ω → Vector r) (Y v : Fin n → Ω → Vector p) (σ : ℝ) : ℝ :=
  ∫ z : Ω × Vector r, ∑ i, restorationThirdDerivative s
    ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) ∂μ.prod (standardGaussian r)

def restorationFourthExpectation {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p) (σ : ℝ) : ℝ :=
  ∫ z : Ω × Vector r, ∑ i, restorationFourthDerivative s
    ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1) ∂μ.prod (standardGaussian r)

theorem array_gradient_selector_partition {Ω : Type*} {p r n : ℕ} (s : FaceSmoother p)
    (X : Fin n → Ω → Vector p) (Z : Fin n → Ω → Vector r) (Y : Fin n → Ω → Vector p)
    (g : Ω → Vector r) (ω : Ω) :
    (∑ i, repeatedDirectionScore (g ω) (Z i ω) * s.translationD1 (X i ω) (Y i ω)) =
      -(1 / s.bandwidth) * ∑ i, ∑ α : Fin 1 → Face p,
        (restorationGradientCoefficient Y i α ω * repeatedDirectionScore (g ω) (Z i ω)) *
          selectorTupleWeight s α (X i ω) := by
  simp_rw [translationD1_eq_selector_partition]
  conv_rhs => rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Finset.mul_sum, restorationGradientCoefficient]
  exact Finset.sum_congr rfl (fun α _ => by ring)

theorem array_hessian_selector_partitions {Ω : Type*} {p r n : ℕ} (s : FaceSmoother p)
    (X : Fin n → Ω → Vector p) (Z : Fin n → Ω → Vector r) (Y W : Fin n → Ω → Vector p)
    (g : Ω → Vector r) (ω : Ω) :
    (∑ i, repeatedDirectionScore (g ω) (Z i ω) * restorationHessian s (X i ω) (W i ω) (Y i ω)) =
      (2 * (∑ i, ∑ α : Fin 2 → Face p,
        (restorationHessianCoefficientTwo W Y i α ω * repeatedDirectionScore (g ω) (Z i ω)) *
          selectorTupleWeight s α (X i ω)) -
       (∑ i, ∑ α : Fin 1 → Face p,
        (restorationHessianCoefficientOne W Y i α ω * repeatedDirectionScore (g ω) (Z i ω)) *
          selectorTupleWeight s α (X i ω))) / s.bandwidth ^ 2 := by
  simp_rw [restorationHessian_eq_selector_partitions]
  conv_rhs => rw [Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  simp only [restorationHessianCoefficientTwo, restorationHessianCoefficientOne]
  have h₂ : (∑ α : Fin 2 → Face p, selectorTupleWeight s α (X i ω) *
      FaceSmoother.normalDot (α 0) (W i ω) * FaceSmoother.normalDot (α 1) (Y i ω)) *
      repeatedDirectionScore (g ω) (Z i ω) =
      ∑ α : Fin 2 → Face p, (FaceSmoother.normalDot (α 0) (W i ω) *
        FaceSmoother.normalDot (α 1) (Y i ω) * repeatedDirectionScore (g ω) (Z i ω)) *
          selectorTupleWeight s α (X i ω) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  have h₁ : (∑ α : Fin 1 → Face p, selectorTupleWeight s α (X i ω) *
      FaceSmoother.normalDot (α 0) (W i ω) * FaceSmoother.normalDot (α 0) (Y i ω)) *
      repeatedDirectionScore (g ω) (Z i ω) =
      ∑ α : Fin 1 → Face p, (FaceSmoother.normalDot (α 0) (W i ω) *
        FaceSmoother.normalDot (α 0) (Y i ω) * repeatedDirectionScore (g ω) (Z i ω)) *
          selectorTupleWeight s α (X i ω) := by
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun α _ => by ring)
  rw [← h₂, ← h₁]
  ring

theorem measurable_restorationGradientCoefficient {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) (i : Fin n) (α : Fin 1 → Face p) :
    Measurable (restorationGradientCoefficient Y i α) :=
  (FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)

theorem restorationGradientCoefficient_bound {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (Y : Fin n → Ω → Vector p) {δ : ℝ}
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (i : Fin n) (α : Fin 1 → Face p) :
    ∀ᵐ ω ∂μ, |restorationGradientCoefficient Y i α ω| ≤ δ :=
  (hYb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hω)

theorem restorationHessianCoefficients_bound {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (Y W : Fin n → Ω → Vector p) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) :
    (∀ i (α : Fin 1 → Face p), ∀ᵐ ω ∂μ, |restorationHessianCoefficientOne W Y i α ω| ≤ δ ^ 2) ∧
    (∀ i (α : Fin 2 → Face p), ∀ᵐ ω ∂μ, |restorationHessianCoefficientTwo W Y i α ω| ≤ δ ^ 2) := by
  constructor
  · intro i α
    filter_upwards [hYb i, hWb i] with ω hy hw
    rw [restorationHessianCoefficientOne, abs_mul, pow_two]
    exact mul_le_mul (FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hw)
      (FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hy) (abs_nonneg _) hδ
  · intro i α
    filter_upwards [hYb i, hWb i] with ω hy hw
    rw [restorationHessianCoefficientTwo, abs_mul, pow_two]
    exact mul_le_mul (FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hw)
      (FaceSmoother.abs_normalDot_le_of_norm_le (α 1) hy) (abs_nonneg _) hδ

theorem restorationThirdExpectation_eq_selector
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y v : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hσ : σ ≠ 0) :
    restorationThirdExpectation s μ A V Z Y v σ =
      -restorationScoreExpectation s μ (σ • A) V Z (restorationGradientCoefficient Y) v /
        (s.bandwidth * σ ^ 2) := by
  have hstein := array_restorationThirdDerivative_stein s μ A V hV v hv Z hZm hZ Y hY hδ hYb hσ
  let X : Fin n → (Ω × Vector r) → Vector p :=
    fun i z => (σ • A).mulVec z.2 + V z.1 + v i z.1
  have hp (z : Ω × Vector r) :
      (∑ i, repeatedDirectionScore z.2 (Z i z.1) * s.translationD1 (X i z) (Y i z.1)) =
        -(1 / s.bandwidth) * ∑ i, ∑ α : Fin 1 → Face p,
          (restorationGradientCoefficient Y i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
            selectorTupleWeight s α (X i z) :=
    array_gradient_selector_partition s X (fun i z => Z i z.1) (fun i z => Y i z.1) Prod.snd z
  have he : (∫ z : Ω × Vector r, ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
      s.translationD1 (X i z) (Y i z.1) ∂μ.prod (standardGaussian r)) =
        -(1 / s.bandwidth) * restorationScoreExpectation s μ (σ • A) V Z (restorationGradientCoefficient Y) v := by
    simp_rw [hp]
    rw [integral_const_mul]
    rfl
  change (∫ z : Ω × Vector r, ∑ i, restorationThirdDerivative s
    ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) ∂μ.prod (standardGaussian r)) = _
  rw [hstein.2.2, he]
  ring

theorem restorationFourthExpectation_eq_selectors
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) (hσ : σ ≠ 0) :
    restorationFourthExpectation s μ A V Z Y W v σ =
      (2 * restorationScoreExpectation s μ (σ • A) V Z (restorationHessianCoefficientTwo W Y) v -
        restorationScoreExpectation s μ (σ • A) V Z (restorationHessianCoefficientOne W Y) v) /
        (s.bandwidth ^ 2 * σ ^ 2) := by
  have hstein := array_restorationFourthDerivative_stein s μ A V hV v hv Z hZm hZ Y W hY hW hδ hYb hWb hσ
  let X : Fin n → (Ω × Vector r) → Vector p :=
    fun i z => (σ • A).mulVec z.2 + V z.1 + v i z.1
  have hX (i : Fin n) : Measurable (X i) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)).add ((hv i).comp measurable_fst)
  let F₂ : Ω × Vector r → ℝ := fun z => ∑ i, ∑ α : Fin 2 → Face p,
    (restorationHessianCoefficientTwo W Y i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
      selectorTupleWeight s α (X i z)
  let F₁ : Ω × Vector r → ℝ := fun z => ∑ i, ∑ α : Fin 1 → Face p,
    (restorationHessianCoefficientOne W Y i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
      selectorTupleWeight s α (X i z)
  have hc₂ (i : Fin n) (α : Fin 2 → Face p) : Measurable (restorationHessianCoefficientTwo W Y i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hY i))
  have hc₁ (i : Fin n) (α : Fin 1 → Face p) : Measurable (restorationHessianCoefficientOne W Y i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i))
  have hb := restorationHessianCoefficients_bound μ Y W hδ hYb hWb
  have hi₂ : Integrable F₂ (μ.prod (standardGaussian r)) := integrable_finset_sum _ (fun i _ =>
    integrable_bounded_selector_score_sum s μ (Z i) (hZ i) _ (hc₂ i) _ (hX i) (sq_nonneg δ) (hb.2 i))
  have hi₁ : Integrable F₁ (μ.prod (standardGaussian r)) := integrable_finset_sum _ (fun i _ =>
    integrable_bounded_selector_score_sum s μ (Z i) (hZ i) _ (hc₁ i) _ (hX i) (sq_nonneg δ) (hb.1 i))
  have hp (z : Ω × Vector r) :
      (∑ i, repeatedDirectionScore z.2 (Z i z.1) * restorationHessian s (X i z) (W i z.1) (Y i z.1)) =
        (2 * F₂ z - F₁ z) / s.bandwidth ^ 2 :=
    array_hessian_selector_partitions s X (fun i z => Z i z.1) (fun i z => Y i z.1)
      (fun i z => W i z.1) Prod.snd z
  have hsub : (∫ z : Ω × Vector r, 2 * F₂ z - F₁ z ∂μ.prod (standardGaussian r)) =
      2 * (∫ z, F₂ z ∂μ.prod (standardGaussian r)) - ∫ z, F₁ z ∂μ.prod (standardGaussian r) := by
    have he := integral_sub (hi₂.const_mul 2) hi₁
    change (∫ z, 2 * F₂ z - F₁ z ∂μ.prod (standardGaussian r)) = _ at he
    rw [integral_const_mul] at he
    exact he
  have he : (∫ z : Ω × Vector r, ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
      restorationHessian s (X i z) (W i z.1) (Y i z.1) ∂μ.prod (standardGaussian r)) =
        (2 * restorationScoreExpectation s μ (σ • A) V Z (restorationHessianCoefficientTwo W Y) v -
          restorationScoreExpectation s μ (σ • A) V Z (restorationHessianCoefficientOne W Y) v) /
            s.bandwidth ^ 2 := by
    simp_rw [hp]
    rw [integral_div, hsub]
    rfl
  change (∫ z : Ω × Vector r, ∑ i, restorationFourthDerivative s
    ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1) ∂μ.prod (standardGaussian r)) = _
  rw [hstein.2.2, he]
  ring

end

end RectangleCLT.Companion.SplitV4
