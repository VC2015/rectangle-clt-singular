import RectangleCLTCompanion.SplitV4.RestorationDerivativePartitions
import RectangleCLTCompanion.RestorationScales

/-! B.2 paired derivative bounds from the actual conditional coefficient
profiles and the actual averaged B.4 matrix estimate. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem restorationScoreExpectation_bound_of_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ) (hc : ∀ i α, @Measurable Ω ℝ mΩ inferInstance (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (hk : 1 ≤ k) {b M R : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c v M R)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    |restorationScoreExpectation (mΩ := mΩ) s μ A V Z c v| ≤ restorationSelectorCap s M 1 R C T k := by
  have he := (conditional_translated_score_restoration_of_budget (mΩ := mΩ) s μ H hH A V hV hmatrix
    Z hZm hZ c hc v hv hk hb hM hR hcb hvb hbudget hC hT hsmall).2
  simpa only [restorationScoreExpectation, restorationSelectorCap, mul_one] using he

theorem restorationThirdExpectation_bound_of_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C T : ℝ} (hσ : σ ≠ 0)
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ M R : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z (restorationGradientCoefficient Y) v M R)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    |restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y v σ| ≤
      restorationSelectorCap s M 1 R C T 1 / (s.bandwidth * σ ^ 2) := by
  have hc (i : Fin n) (α : Fin 1 → Face p) : @Measurable Ω ℝ mΩ inferInstance
      (restorationGradientCoefficient Y i α) :=
    (FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)
  have hcb (i : Fin n) (α : Fin 1 → Face p) : ∀ᵐ ω ∂μ, |restorationGradientCoefficient Y i α ω| ≤ δ :=
    (hYb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hω)
  have hbnd := restorationScoreExpectation_bound_of_budget (mΩ := mΩ) s μ H hH (σ • A) V hV hmatrix
    Z hZm hZ (restorationGradientCoefficient Y) hc v hv (by decide) hδ hM hR hcb hvb hbudget hC hT hsmall
  rw [restorationThirdExpectation_eq_selector (mΩ := mΩ) s μ A V (hV.mono hH le_rfl)
    Z hZm hZ Y v hY hv hδ hYb hσ, abs_div, abs_neg,
      abs_of_pos (mul_pos s.bandwidth_pos (sq_pos_of_ne_zero hσ))]
  exact div_le_div_of_nonneg_right hbnd (mul_nonneg s.bandwidth_pos.le (sq_nonneg σ))

theorem restorationFourthExpectation_bound_of_budgets
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C T : ℝ} (hσ : σ ≠ 0)
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ M R : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget₁ : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z (restorationHessianCoefficientOne W Y) v M R)
    (hbudget₂ : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z (restorationHessianCoefficientTwo W Y) v M R)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    |restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ| ≤
      (2 * restorationSelectorCap s M 1 R C T 2 + restorationSelectorCap s M 1 R C T 1) /
        (s.bandwidth ^ 2 * σ ^ 2) := by
  have hc₁ (i : Fin n) (α : Fin 1 → Face p) : @Measurable Ω ℝ mΩ inferInstance
      (restorationHessianCoefficientOne W Y i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i))
  have hc₂ (i : Fin n) (α : Fin 2 → Face p) : @Measurable Ω ℝ mΩ inferInstance
      (restorationHessianCoefficientTwo W Y i α) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hY i))
  have hcb := @restorationHessianCoefficients_bound Ω mΩ p n μ Y W δ hδ hYb hWb
  have hb₁ := restorationScoreExpectation_bound_of_budget (mΩ := mΩ) s μ H hH (σ • A) V hV hmatrix
    Z hZm hZ (restorationHessianCoefficientOne W Y) hc₁ v hv (by decide) (sq_nonneg δ) hM hR hcb.1 hvb hbudget₁ hC hT hsmall
  have hb₂ := restorationScoreExpectation_bound_of_budget (mΩ := mΩ) s μ H hH (σ • A) V hV hmatrix
    Z hZm hZ (restorationHessianCoefficientTwo W Y) hc₂ v hv (by decide) (sq_nonneg δ) hM hR hcb.2 hvb hbudget₂ hC hT hsmall
  rw [restorationFourthExpectation_eq_selectors (mΩ := mΩ) s μ A V (hV.mono hH le_rfl)
    Z hZm hZ Y W v hY hW hv hδ hYb hWb hσ, abs_div,
      abs_of_pos (mul_pos (sq_pos_of_pos s.bandwidth_pos) (sq_pos_of_ne_zero hσ))]
  apply div_le_div_of_nonneg_right _ (mul_nonneg (sq_nonneg _) (sq_nonneg _))
  calc
    _ ≤ |2 * restorationScoreExpectation (mΩ := mΩ) s μ (σ • A) V Z (restorationHessianCoefficientTwo W Y) v| +
        |restorationScoreExpectation (mΩ := mΩ) s μ (σ • A) V Z (restorationHessianCoefficientOne W Y) v| := abs_sub _ _
    _ = 2 * |restorationScoreExpectation (mΩ := mΩ) s μ (σ • A) V Z (restorationHessianCoefficientTwo W Y) v| +
        |restorationScoreExpectation (mΩ := mΩ) s μ (σ • A) V Z (restorationHessianCoefficientOne W Y) v| := by
      rw [abs_mul]
      norm_num
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left hb₂ (by norm_num)) hb₁

theorem restorationSelectorCap_one_le_42 {p : ℕ} (s : FaceSmoother p)
    {M R C T : ℝ} (hM : 0 ≤ M) (hR : 0 ≤ R) (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hhalf : C * (Real.exp (R / s.bandwidth) - 1) ≤ 1 / 2) :
    restorationSelectorCap s M 1 R C T 1 ≤ 42 * M * C ^ 3 * T := by
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hden : 0 ≤ 1 - C * (Real.exp (R / s.bandwidth) - 1) := by linarith
  have hcap₂ : 0 ≤ restorationSelectorCap s M 1 R C T 2 := by
    unfold restorationSelectorCap
    exact div_nonneg (by positivity) (pow_nonneg hden _)
  have he := two_restorationSelectorCaps_le s hM (by norm_num : (0 : ℝ) ≤ 1) hR hC hT hhalf
  simp only [mul_one] at he
  linarith

/-- Baseline paired B.2 derivatives under the actual conditional covariance
budget. This theorem consumes B.4's actual averaged matrix estimate; its
remaining hypotheses are genuine moments and the stated directional and
translation envelopes. -/
theorem restoration_paired_baseline_of_matrixEstimate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C T : ℝ} (hσ : σ ≠ 0)
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ R : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hband : restorationBandwidthConstant C * R ≤ s.bandwidth) :
    |restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y v σ| ≤
      (42 * C ^ 3 * δ * T) / (s.bandwidth * σ ^ 2) ∧
    |restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ| ≤
      (42 * C ^ 3 * δ ^ 2 * T) / (s.bandwidth ^ 2 * σ ^ 2) := by
  have hhalf := restoration_small_of_bandwidth s hC hR hband
  have hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1 := hhalf.trans_lt (by norm_num)
  have hvc (i : Fin n) : AEStronglyMeasurable (m := mΩ) (v i) μ := (hv i).aestronglyMeasurable
  have hcG (i : Fin n) (α : Fin 1 → Face p) : AEStronglyMeasurable (m := mΩ)
      (restorationGradientCoefficient Y i α) μ :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).aestronglyMeasurable
  have hbG (i : Fin n) (α : Fin 1 → Face p) : ∀ᵐ ω ∂μ, |restorationGradientCoefficient Y i α ω| ≤ δ :=
    (hYb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hω)
  have hg := ConditionalTranslatedCoefficientBudget.baseline (mΩ := mΩ) s μ H hH Z
    (restorationGradientCoefficient Y) v hZ hcG hvc hδ hR hbG hvb hbudget
  have hc₁ (i : Fin n) (α : Fin 1 → Face p) : AEStronglyMeasurable (m := mΩ)
      (restorationHessianCoefficientOne W Y i α) μ :=
    (((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i))).aestronglyMeasurable
  have hc₂ (i : Fin n) (α : Fin 2 → Face p) : AEStronglyMeasurable (m := mΩ)
      (restorationHessianCoefficientTwo W Y i α) μ :=
    (((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hY i))).aestronglyMeasurable
  have hcb := @restorationHessianCoefficients_bound Ω mΩ p n μ Y W δ hδ hYb hWb
  have h₁ := ConditionalTranslatedCoefficientBudget.baseline (mΩ := mΩ) s μ H hH Z
    (restorationHessianCoefficientOne W Y) v hZ hc₁ hvc (sq_nonneg δ) hR hcb.1 hvb hbudget
  have h₂ := ConditionalTranslatedCoefficientBudget.baseline (mΩ := mΩ) s μ H hH Z
    (restorationHessianCoefficientTwo W Y) v hZ hc₂ hvc (sq_nonneg δ) hR hcb.2 hvb hbudget
  have ht := restorationThirdExpectation_bound_of_budget (mΩ := mΩ) s μ H hH A V hV hσ hmatrix Z hZm hZ
    Y v hY hv hδ hδ hR hYb hvb hg hC hT hsmall
  have hf := restorationFourthExpectation_bound_of_budgets (mΩ := mΩ) s μ H hH A V hV hσ hmatrix Z hZm hZ
    Y W v hY hW hv hδ (sq_nonneg δ) hR hYb hWb hvb h₁ h₂ hC hT hsmall
  constructor
  · apply ht.trans
    have he := div_le_div_of_nonneg_right (restorationSelectorCap_one_le_42 s hδ hR hC hT hhalf)
      (mul_nonneg s.bandwidth_pos.le (sq_nonneg σ))
    simpa only [mul_assoc, mul_left_comm, mul_comm] using he
  · apply hf.trans
    have he := div_le_div_of_nonneg_right
      (two_restorationSelectorCaps_le s (sq_nonneg δ) (by norm_num : (0 : ℝ) ≤ 1) hR hC hT hhalf)
      (mul_nonneg (sq_nonneg s.bandwidth) (sq_nonneg σ))
    simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using he

/-- The relative cubic estimate retains the signed conditional coefficient.
Only the unshifted case is asserted, as in B.2's M1 refinement. -/
theorem restoration_third_relative_signed_of_matrixEstimate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C T : ℝ} (hσ : σ ≠ 0)
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hbudget : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => FaceSmoother.normalDot f (Y i z)) ω) u| ≤ M * vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T) :
    |restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y (fun _ _ => 0) σ| ≤
      (42 * C ^ 3 * M * T) / (s.bandwidth * σ ^ 2) := by
  have hc (i : Fin n) (α : Fin 1 → Face p) : AEStronglyMeasurable (m := mΩ)
      (restorationGradientCoefficient Y i α) μ :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).aestronglyMeasurable
  have hcb (i : Fin n) (α : Fin 1 → Face p) : ∀ᵐ ω ∂μ,
      |restorationGradientCoefficient Y i α ω| ≤ δ :=
    (hYb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (α 0) hω)
  have hi (i : Fin n) (α : Fin 1 → Face p) (j l : Fin r) : Integrable
      (fun ω => restorationGradientCoefficient Y i α ω * (Z i ω j * Z i ω l)) μ :=
    (hZ i j l).bdd_mul' (hc i α) (by simpa only [Real.norm_eq_abs] using hcb i α)
  have hp := ConditionalTranslatedCoefficientBudget.relative_signed_zero_shift (mΩ := mΩ)
    s μ H hH Z (restorationGradientCoefficient Y) hi (fun α => hbudget (α 0))
  have hhalf : C * (Real.exp ((0 : ℝ) / s.bandwidth) - 1) ≤ 1 / 2 := by norm_num
  have hb := restorationThirdExpectation_bound_of_budget (mΩ := mΩ) s μ H hH A V hV hσ hmatrix
    Z hZm hZ Y (fun _ _ => 0) hY (fun _ => measurable_const) hδ hM (le_refl 0)
    hYb (fun _ => by simp) hp hC hT (by norm_num)
  apply hb.trans
  have he := div_le_div_of_nonneg_right
    (restorationSelectorCap_one_le_42 s hM (le_refl 0) hC hT hhalf)
    (mul_nonneg s.bandwidth_pos.le (sq_nonneg σ))
  simpa only [mul_assoc, mul_left_comm, mul_comm] using he

/-- Both conditional face-square budgets control every mixed pair of
selector directions, including distinct faces in the Hessian partition. -/
theorem restoration_face_pair_profile
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ) (Z : Fin n → Ω → Vector r)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p)
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ R M : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudgetY : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (Y i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hbudgetW : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (W i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (f g : (Fin k → Face p) → Face p) :
    ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z
      (fun i α ω => FaceSmoother.normalDot (f α) (W i ω) *
        FaceSmoother.normalDot (g α) (Y i ω)) v M R := by
  apply ConditionalTranslatedCoefficientBudget.relative_pair (mΩ := mΩ) s μ H hH Z
    (fun i α ω => FaceSmoother.normalDot (f α) (W i ω))
    (fun i α ω => FaceSmoother.normalDot (g α) (Y i ω)) v hZ
  · intro i α
    exact ((FaceSmoother.continuous_normalDot (f α)).measurable.comp (hW i)).aestronglyMeasurable
  · intro i α
    exact ((FaceSmoother.continuous_normalDot (g α)).measurable.comp (hY i)).aestronglyMeasurable
  · exact fun i => (hv i).aestronglyMeasurable
  · exact hδ
  · exact hR
  · intro i α
    exact (hWb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (f α) hω)
  · intro i α
    exact (hYb i).mono (fun _ hω => FaceSmoother.abs_normalDot_le_of_norm_le (g α) hω)
  · exact hvb
  · exact fun α => hbudgetW (f α)
  · exact fun α => hbudgetY (g α)

/-- B.2's relative M2 estimate uses both stated conditional face-square
budgets. The arrays and translations may depend on one another. -/
theorem restoration_fourth_relative_pair_of_matrixEstimate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C T : ℝ} (hσ : σ ≠ 0)
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C T)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ R M : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudgetY : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (Y i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hbudgetW : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (W i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hband : restorationBandwidthConstant C * R ≤ s.bandwidth) :
    |restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ| ≤
      (42 * C ^ 3 * M * T) / (s.bandwidth ^ 2 * σ ^ 2) := by
  have hhalf := restoration_small_of_bandwidth s hC hR hband
  have hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1 := hhalf.trans_lt (by norm_num)
  have h₁ : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z
      (restorationHessianCoefficientOne W Y) v M R :=
    restoration_face_pair_profile (mΩ := mΩ) s μ H hH Z hZ Y W v hY hW hv hδ hR
      hYb hWb hvb hbudgetY hbudgetW (fun α => α 0) (fun α => α 0)
  have h₂ : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z
      (restorationHessianCoefficientTwo W Y) v M R :=
    restoration_face_pair_profile (mΩ := mΩ) s μ H hH Z hZ Y W v hY hW hv hδ hR
      hYb hWb hvb hbudgetY hbudgetW (fun α => α 0) (fun α => α 1)
  have hb := restorationFourthExpectation_bound_of_budgets (mΩ := mΩ) s μ H hH A V hV hσ hmatrix
    Z hZm hZ Y W v hY hW hv hδ hM hR hYb hWb hvb h₁ h₂ hC hT hsmall
  apply hb.trans
  have he := div_le_div_of_nonneg_right
    (two_restorationSelectorCaps_le s hM (by norm_num : (0 : ℝ) ≤ 1) hR hC hT hhalf)
    (mul_nonneg (sq_nonneg s.bandwidth) (sq_nonneg σ))
  simpa only [mul_one, one_mul, mul_assoc, mul_left_comm, mul_comm] using he

/-- Vanishing remaining directions settle the degenerate smoothing-scale
case without dividing by the scale or adding a positivity hypothesis. -/
theorem restorationThirdExpectation_eq_zero_of_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (Z : Fin n → Ω → Vector r) (Y v : Fin n → Ω → Vector p) (σ : ℝ)
    (hY : ∀ i, ∀ᵐ ω ∂μ, Y i ω = 0) :
    restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y v σ = 0 := by
  unfold restorationThirdExpectation
  rw [← integral_zero (Ω × Vector r) ℝ (μ := μ.prod (standardGaussian r))]
  apply integral_congr_ae
  have hp : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ∀ i, Y i z.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hY)
  filter_upwards [hp] with z hz
  simp only [restorationThirdDerivative_eq_coordinate, hz, Pi.zero_apply, zero_mul, Finset.sum_const_zero]

theorem restorationFourthExpectation_eq_zero_of_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p) (σ : ℝ)
    (hY : ∀ i, ∀ᵐ ω ∂μ, Y i ω = 0) :
    restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ = 0 := by
  unfold restorationFourthExpectation
  rw [← integral_zero (Ω × Vector r) ℝ (μ := μ.prod (standardGaussian r))]
  apply integral_congr_ae
  have hp : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ∀ i, Y i z.1 = 0 :=
    Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hY)
  filter_upwards [hp] with z hz
  simp only [restorationFourthDerivative_eq_coordinate, hz, Pi.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero]

theorem restoration_scale_zero_forces_delta_zero {p : ℕ} (hp : 1 ≤ p)
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hσ : σ = 0) : δ = 0 := by
  have hsqrt : 0 < Real.sqrt (dimensionLog p) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  have hm : δ * Real.sqrt (dimensionLog p) ≤ 0 * Real.sqrt (dimensionLog p) := by
    simpa only [hσ, zero_mul] using hscale
  exact le_antisymm ((mul_le_mul_right hsqrt).mp hm) hδ

end

end RectangleCLT.Companion.SplitV4
