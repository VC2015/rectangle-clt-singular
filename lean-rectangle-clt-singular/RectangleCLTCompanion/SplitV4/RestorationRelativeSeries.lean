import RectangleCLTCompanion.SplitV4.RestorationGaussianTraceExtraction

/-! Relative M1/M2 restoration uses the genuine signed conditional
coefficient budgets, while a separate coarse envelope supplies integrability.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def ConditionalTranslatedCoefficientBudget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (H : MeasurableSpace Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (M R : ℝ) : Prop :=
  ∀ (ℓ : ℕ) (α : Fin k → Face p) (β : Fin ℓ → Face p), ∀ᵐ ω ∂μ, ∀ u,
    |matrixQuadratic (conditionalTranslatedRestorationCoefficient (mΩ := mΩ) s μ H Z
      (fun i => c i α) v α β ω) u| ≤
      (M * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) * vectorNormSq u

theorem conditional_translated_order_bound_of_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k ℓ : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (hk : 1 ≤ k)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hc : ∀ i α, AEStronglyMeasurable (m := mΩ) (c i α) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b M R : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c v M R) :
    |∫ ω, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω) ∂μ| ≤
      (M * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) *
        C ^ (k + ℓ + 1) * T := by
  let E := Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ
  have hE : 0 ≤ E := restorationTranslationEnvelope_nonneg s hR k ℓ
  let B : (Fin (k + ℓ) → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ := fun γ =>
    restorationRankOneSum Z (fun i z => c i (fun a => γ (Fin.castAdd ℓ a)) z *
      restorationTranslationCoefficient s (fun a => γ (Fin.castAdd ℓ a))
        (fun a => γ (Fin.natAdd k a)) (v i z))
  have hBi (γ : Fin (k + ℓ) → Face p) (j l : Fin r) : Integrable (fun ω => B γ ω j l) μ := by
    apply integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z _ hZ
    · intro i
      exact (hc i _).mul ((continuous_restorationTranslationCoefficient s _ _).comp_aestronglyMeasurable (hv i))
    · intro i
      filter_upwards [hcb i (fun a => γ (Fin.castAdd ℓ a)), hvb i] with ω hcω hvω
      rw [abs_mul]
      exact mul_le_mul hcω (abs_restorationTranslationCoefficient_le s _ _ hR hvω) (abs_nonneg _) hb
  have hCE (γ : Fin (k + ℓ) → Face p) : ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B γ) ω) u| ≤
        (M * E) * vectorNormSq u := by
    simpa only [ConditionalTranslatedCoefficientBudget, conditionalTranslatedRestorationCoefficient,
      conditionalRestorationCoefficient, B, E, mul_assoc] using
      hbudget ℓ (fun a => γ (Fin.castAdd ℓ a)) (fun a => γ (Fin.natAdd k a))
  have hmain := conditional_restoration_matrix_order_bound (mΩ := mΩ) s μ H hH A V hV hmatrix
    (k + ℓ) (by omega) (mul_nonneg hM hE) B hBi hCE
  have hp (ω : Ω) : (∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω)) =
      ∑ γ : Fin (k + ℓ) → Face p, Matrix.trace (B γ ω * selectorGaussianScore s A V γ ω) := by
    rw [sum_faceTuples_append]
    apply Finset.sum_congr rfl
    intro γ _
    simp only [B, Fin.append_castAdd_natAdd]
  simp_rw [hp]
  simpa only [E, mul_assoc] using hmain.2

theorem restoration_scalar_series_bound {k : ℕ} (F : ℕ → ℝ) {M R C T h : ℝ}
    (hM : 0 ≤ M) (hR : 0 ≤ R) (hh : 0 < h) (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C * (Real.exp (R / h) - 1) < 1)
    (hF : ∀ ℓ, |F ℓ| ≤ (M * Real.exp ((k : ℝ) * R / h) * (Real.exp (R / h) - 1) ^ ℓ) *
      C ^ (k + ℓ + 1) * T) :
    Summable (fun ℓ => (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * F ℓ) ∧
    |∑' ℓ, (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * F ℓ| ≤
      (M * Real.exp ((k : ℝ) * R / h) * C ^ (k + 1) * T) /
        (1 - C * (Real.exp (R / h) - 1)) ^ (k + 1) := by
  let η := Real.exp (R / h) - 1
  let P := M * Real.exp ((k : ℝ) * R / h) * C ^ (k + 1) * T
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR hh.le))
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hG : HasSum (fun ℓ : ℕ => P * (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ))
      (P / (1 - C * η) ^ (k + 1)) := by
    convert (hasSum_restoration_matrix_majorant k hC₀ hη hsmall).mul_left P using 1
    ring
  have hnorm (ℓ : ℕ) : ‖(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * F ℓ‖ ≤
      P * (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ) := by
    rw [Real.norm_eq_abs, abs_mul]
    have hsign : |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ)| = ((k + ℓ).choose ℓ : ℝ) := by
      simp [abs_mul, abs_pow]
    rw [hsign]
    apply (mul_le_mul_of_nonneg_left (hF ℓ) (Nat.cast_nonneg _)).trans_eq
    dsimp only [P, η]
    rw [show k + ℓ + 1 = (k + 1) + ℓ by omega, pow_add, mul_pow]
    ring
  have hns : Summable (fun ℓ => ‖(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * F ℓ‖) :=
    Summable.of_nonneg_of_le (fun _ => norm_nonneg _) hnorm hG.summable
  have hs := hns.of_norm
  exact ⟨hs, by simpa only [Real.norm_eq_abs, P, η] using hs.hasSum.norm_le_of_bounded hG hnorm⟩

theorem ConditionalTranslatedCoefficientBudget.baseline
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hc : ∀ i α, AEStronglyMeasurable (m := mΩ) (c i α) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u) :
    ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c v b R := by
  intro ℓ α β
  exact conditional_translated_restoration_coefficient_baseline (mΩ := mΩ) s μ H hH Z
    (fun i => c i α) v hZ (fun i => hc i α) hv hb hR (fun i => hcb i α) hvb hbudget α β

theorem ConditionalTranslatedCoefficientBudget.relative_pair
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ) (Z : Fin n → Ω → Vector r)
    (Y W : Fin n → (Fin k → Face p) → Ω → ℝ) (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hY : ∀ i α, AEStronglyMeasurable (m := mΩ) (Y i α) μ)
    (hW : ∀ i α, AEStronglyMeasurable (m := mΩ) (W i α) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {δ R M : ℝ} (hδ : 0 ≤ δ) (hR : 0 ≤ R)
    (hYb : ∀ i α, ∀ᵐ ω ∂μ, |Y i α ω| ≤ δ) (hWb : ∀ i α, ∀ᵐ ω ∂μ, |W i α ω| ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudgetY : ∀ α, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (Y i α z) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hbudgetW : ∀ α, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i z => (W i α z) ^ 2) ω) u ≤ M * vectorNormSq u) :
    ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z (fun i α ω => Y i α ω * W i α ω) v M R := by
  intro ℓ α β
  exact conditional_translated_restoration_coefficient_relative_pair (mΩ := mΩ) s μ H hH Z
    (fun i => Y i α) (fun i => W i α) v hZ (fun i => hY i α) (fun i => hW i α) hv
    hδ hR (fun i => hYb i α) (fun i => hWb i α) hvb (hbudgetY α) (hbudgetW α) α β

theorem ConditionalTranslatedCoefficientBudget.relative_signed_zero_shift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ) (Z : Fin n → Ω → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (hi : ∀ i α j l, Integrable (fun ω => c i α ω * (Z i ω j * Z i ω l)) μ) {M : ℝ}
    (hbudget : ∀ α, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun i => c i α) ω) u| ≤ M * vectorNormSq u) :
    ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c (fun _ _ => 0) M 0 := by
  intro ℓ α β
  have he := (conditional_restoration_coefficient_relative_signed_zero_shift (mΩ := mΩ)
    s μ H hH Z (fun i => c i α) (fun i j l => hi i α j l) (hbudget α) α β).2
  cases ℓ with
  | zero => simpa using he
  | succ ℓ => simpa using he

theorem conditional_restoration_expected_series_bound_of_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (hk : 1 ≤ k)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (hc : ∀ i α, AEStronglyMeasurable (m := mΩ) (c i α) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b M R : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c v M R)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Summable (conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v) ∧
    |∑' ℓ, conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v ℓ| ≤
      (M * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
        (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  let F : ℕ → ℝ := fun ℓ => ∫ ω, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
    Matrix.trace (restorationRankOneSum Z
      (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
        selectorGaussianScore s A V (Fin.append α β) ω) ∂μ
  have hF (ℓ : ℕ) : |F ℓ| ≤
      (M * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) *
        C ^ (k + ℓ + 1) * T :=
    conditional_translated_order_bound_of_budget (mΩ := mΩ) s μ H hH A V hV hmatrix
      Z c v hk hZ hc hv hb hM hR hcb hvb hbudget
  simpa only [conditionalRestorationTraceOrderIntegral, F] using
    restoration_scalar_series_bound F hM hR s.bandwidth_pos hC hT hsmall hF

/-- The same genuine translated score expectation uses M1 or M2 through
its proved conditional coefficient budget. The coarse envelope is used
only to justify moments and series interchanges. -/
theorem conditional_translated_score_restoration_of_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (Z : Fin n → Ω → Vector r)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (hc : ∀ i α, @Measurable Ω ℝ mΩ inferInstance (c i α))
    (v : Fin n → Ω → Vector p)
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (hk : 1 ≤ k) {b M R : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ConditionalTranslatedCoefficientBudget (mΩ := mΩ) s μ H Z c v M R)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1))
          (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) ∧
    |∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤
      (M * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
        (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη₁ : Real.exp (R / s.bandwidth) - 1 < 1 :=
    (le_mul_of_one_le_left hη hC).trans_lt hsmall
  have hradius : R / s.bandwidth < Real.log 2 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hVm : @Measurable Ω (Vector p) mΩ inferInstance V := hV.mono hH le_rfl
  have he := translated_score_hasSum_expected_orders (mΩ := mΩ) s μ A V hVm Z hZm hZ c hc v hv hb hR hcb hvb hradius
  have hbnd := conditional_restoration_expected_series_bound_of_budget (mΩ := mΩ) s μ H hH A V hV hmatrix
    Z c v hk hZ (fun i α => (hc i α).aestronglyMeasurable) (fun i => (hv i).aestronglyMeasurable)
    hb hM hR hcb hvb hbudget hC hT hsmall
  refine ⟨he.1, ?_⟩
  rw [← he.2.tsum_eq]
  exact hbnd.2

end

end RectangleCLT.Companion.SplitV4
