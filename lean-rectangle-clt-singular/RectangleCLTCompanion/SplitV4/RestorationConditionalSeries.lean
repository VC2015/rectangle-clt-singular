import RectangleCLTCompanion.SplitV4.RestorationConditionalAveraging

/-! Actual translated restoration coefficient orders, with conditional
operator budgets and the unconditional averaged matrix estimate. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- A translated coefficient order summed at one common base. The
conditional covariance is used before the averaged Gaussian matrix norm;
the arrays may depend on the base and on one another. -/
theorem conditional_translated_restoration_order_bound
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
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcbound : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u) :
    Integrable (fun ω => ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω)) μ ∧
    |∫ ω, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω) ∂μ| ≤
      (b * Real.exp ((k : ℝ) * R / s.bandwidth) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) *
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
      filter_upwards [hcbound i (fun a => γ (Fin.castAdd ℓ a)), hvb i] with ω hcω hvω
      rw [abs_mul]
      exact mul_le_mul hcω (abs_restorationTranslationCoefficient_le s _ _ hR hvω) (abs_nonneg _) hb
  have hCE (γ : Fin (k + ℓ) → Face p) : ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B γ) ω) u| ≤
        (b * E) * vectorNormSq u := by
    have hh := conditional_translated_restoration_coefficient_baseline (mΩ := mΩ) s μ H hH Z
      (fun i => c i (fun a => γ (Fin.castAdd ℓ a))) v hZ
      (fun i => hc i _) hv hb hR (fun i => hcbound i _) hvb hbudget
      (fun a => γ (Fin.castAdd ℓ a)) (fun a => γ (Fin.natAdd k a))
    simpa only [conditionalTranslatedRestorationCoefficient, conditionalRestorationCoefficient, B, E, mul_assoc] using hh
  have hmain := conditional_restoration_matrix_order_bound (mΩ := mΩ) s μ H hH A V hV hmatrix
    (k + ℓ) (by omega) (mul_nonneg hb hE) B hBi hCE
  have hp (ω : Ω) : (∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω)) =
      ∑ γ : Fin (k + ℓ) → Face p, Matrix.trace (B γ ω * selectorGaussianScore s A V γ ω) := by
    rw [sum_faceTuples_append]
    apply Finset.sum_congr rfl
    intro γ _
    simp only [B, Fin.append_castAdd_natAdd]
  refine ⟨hmain.1.congr (ae_of_all _ (fun ω => (hp ω).symm)), ?_⟩
  simp_rw [hp]
  simpa only [E, mul_assoc] using hmain.2

def conditionalRestorationTraceOrderIntegral {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {p r n k : ℕ} (s : FaceSmoother p) (μ : Measure Ω)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (ℓ : ℕ) : ℝ :=
  (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
    ∫ ω, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z * restorationTranslationCoefficient s α β (v i z)) ω *
          selectorGaussianScore s A V (Fin.append α β) ω) ∂μ

/-- Absolute summability and the rank-free bound after conditional
averaging. The interchange with the original translated expectation is a
separate integrability step; cancellation is preserved here. -/
theorem conditional_restoration_expected_series_bound
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
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcbound : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Summable (conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v) ∧
    |∑' ℓ, conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v ℓ| ≤
      (b * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
        (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  let η := Real.exp (R / s.bandwidth) - 1
  let P := b * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hC₀ : 0 ≤ C := zero_le_one.trans hC
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hG : HasSum (fun ℓ : ℕ => P * (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ))
      (P / (1 - C * η) ^ (k + 1)) := by
    convert (hasSum_restoration_matrix_majorant k hC₀ hη hsmall).mul_left P using 1
    ring
  have hnorm (ℓ : ℕ) : ‖conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v ℓ‖ ≤
      P * (((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ) := by
    have horder := (conditional_translated_restoration_order_bound (mΩ := mΩ) s μ H hH A V hV hmatrix
      Z c v hk hZ hc hv hb hR hcbound hvb hbudget (ℓ := ℓ)).2
    unfold conditionalRestorationTraceOrderIntegral
    rw [Real.norm_eq_abs, abs_mul]
    have hsign : |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ)| = ((k + ℓ).choose ℓ : ℝ) := by
      simp [abs_mul, abs_pow]
    rw [hsign]
    apply (mul_le_mul_of_nonneg_left horder (Nat.cast_nonneg _)).trans_eq
    dsimp only [P, η]
    rw [show k + ℓ + 1 = (k + 1) + ℓ by omega, pow_add, mul_pow]
    ring
  have hns : Summable (fun ℓ => ‖conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v ℓ‖) :=
    Summable.of_nonneg_of_le (fun ℓ => norm_nonneg _) hnorm hG.summable
  have hs : Summable (conditionalRestorationTraceOrderIntegral (mΩ := mΩ) s μ A V Z c v) := hns.of_norm
  refine ⟨hs, ?_⟩
  simpa only [Real.norm_eq_abs, P, η] using hs.hasSum.norm_le_of_bounded hG hnorm

end

end RectangleCLT.Companion.SplitV4
