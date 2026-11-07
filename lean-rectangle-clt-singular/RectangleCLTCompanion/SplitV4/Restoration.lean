import RectangleCLTCompanion.SplitV4.RestorationConditionalTransport
import RectangleCLTCompanion.SplitV4.NuclearSelectorMatrixInterface

/-! Full B.2 in face coordinates: actual conditional joint-array
independence, actual conditional matrix budgets, and unconditional base
concentration. The fixed repeated directions are pulled through the
rectangular unit-row Gaussian factor; all auxiliary arrays may depend on
one another and on H. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def restorationOriginalThird {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (G : Ω → Vector r) (Z : Fin n → Ω → Vector r)
    (Y v : Fin n → Ω → Vector p) (σ : ℝ) : ℝ :=
  ∑ i, ∫ ω, restorationThirdDerivative s ((σ • A).mulVec (G ω) + V ω + v i ω)
    (A.mulVec (Z i ω)) (Y i ω) ∂μ

def restorationOriginalFourth {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (G : Ω → Vector r) (Z : Fin n → Ω → Vector r)
    (Y W v : Fin n → Ω → Vector p) (σ : ℝ) : ℝ :=
  ∑ i, ∫ ω, restorationFourthDerivative s ((σ • A).mulVec (G ω) + V ω + v i ω)
    (A.mulVec (Z i ω)) (Y i ω) (W i ω) ∂μ

def PairedRestorationConclusion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (H : MeasurableSpace Ω)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (G : Ω → Vector r)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p) (σ δ Cb : ℝ) : Prop :=
  (|restorationOriginalThird (mΩ := mΩ) s μ A V G Z Y v σ| ≤
      Cb / σ ^ 2 * δ * dimensionLog p * Real.sqrt (dimensionLog p) ∧
    |restorationOriginalFourth (mΩ := mΩ) s μ A V G Z Y W v σ| ≤
      Cb / σ ^ 2 * δ ^ 2 / s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) ∧
  (v = (fun _ _ => 0) → ∀ M : ℝ, 0 ≤ M →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => FaceSmoother.normalDot f (Y i z)) ω) u| ≤ M * vectorNormSq u) →
    |restorationOriginalThird (mΩ := mΩ) s μ A V G Z Y v σ| ≤
      Cb / σ ^ 2 * M * dimensionLog p * Real.sqrt (dimensionLog p)) ∧
  (∀ M : ℝ, 0 ≤ M →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (Y i z)) ^ 2) ω) u ≤ M * vectorNormSq u) →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (W i z)) ^ 2) ω) u ≤ M * vectorNormSq u) →
    |restorationOriginalFourth (mΩ := mΩ) s μ A V G Z Y W v σ| ≤
      Cb / σ ^ 2 * M / s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p))

set_option linter.unusedVariables false in
/-- Complete source contract of B.2, including both optional refinements.
The conditional-independence premise is bounded-indicator factorization,
so no disintegration or standard-Borel restriction is hidden. -/
def PairedRestorationContract (Ab Cb C₀ b : ℝ) : Prop :=
  ∀ {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : ∀ j, vectorNormSq (A j) = 1)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ = standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hσ₁ : σ ≤ 1)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ b * δ)
    (hcov : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hconcentration : RectangleBaseConcentration
      (@Measure.map Ω (Vector p) mΩ inferInstance V μ) C₀ δ (dimensionLog p))
    (hband : Ab * δ ≤ s.bandwidth),
    PairedRestorationConclusion (mΩ := mΩ) s μ H A V G Z Y W v σ δ Cb

theorem paired_restoration_contract {b C₀ : ℝ} (hb : 0 ≤ b) (hC₀ : 0 < C₀) :
    PairedRestorationContract (restorationPairedBandwidth logisticMatrixConstant b)
      (restorationPairedConstant logisticMatrixConstant C₀) C₀ b := by
  intro Ω mΩ p r n hp s μ hprob H hH A hA V hV Z Y W v hZm hZ hY hW hv
    G hG hGlaw hHG hCI δ σ hδ _hσ₁ hscale hYb hWb hvb hcov hc hband
  letI : MeasurableSpace Ω := mΩ
  have hδh : δ ≤ s.bandwidth := by
    calc
      δ = 1 * δ := (one_mul _).symm
      _ ≤ restorationPairedBandwidth logisticMatrixConstant b * δ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) hδ
      _ ≤ _ := hband
  have hσ : 0 ≤ σ := (mul_nonneg hδ (Real.sqrt_nonneg _)).trans hscale
  have hm : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V logisticMatrixConstant
      (C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
    simpa only [mul_assoc] using averagedSelectorMatrixEstimate_of_rectangle_concentration
      hp μ V (hV.mono hH le_rfl) s A hA hC₀ hδ hδh hσ hscale hc
  have ht := (restorationThirdExpectation_conditional_transport (mΩ := mΩ) (σ := σ) s μ H hH A V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hYb).2
  have hf := (restorationFourthExpectation_conditional_transport (mΩ := mΩ) (σ := σ) s μ H hH A V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hYb hWb).2
  change restorationOriginalThird s μ A V G Z Y v σ = _ at ht
  change restorationOriginalFourth s μ A V G Z Y W v σ = _ at hf
  have hbase := restoration_paired_baseline_product (mΩ := mΩ) hp s μ H hH A V hV hm
    Z hZm hZ Y W v hY hW hv hδ hb hYb hWb hvb hcov logisticMatrixConstant_ge_one hC₀.le hscale hband
  refine ⟨?_, ?_, ?_⟩
  · simpa only [ht, hf] using hbase
  · intro hvzero M hM hbudget
    have he := restoration_third_relative_product (mΩ := mΩ) hp s μ H hH A V hV hm
      Z hZm hZ Y hY hδ hM hYb hbudget logisticMatrixConstant_ge_one hC₀.le hscale
    rw [ht]
    simpa only [hvzero] using he
  · intro M hM hbudgetY hbudgetW
    have he := restoration_fourth_relative_product (mΩ := mΩ) hp s μ H hH A V hV hm
      Z hZm hZ Y W v hY hW hv hδ hb hM hYb hWb hvb hbudgetY hbudgetW
      logisticMatrixConstant_ge_one hC₀.le hscale hband
    simpa only [hf] using he

/-- Whole Lemma B.2. Both constants are fixed before all dimensions,
probability spaces, bases, and possibly dependent auxiliary arrays. -/
theorem lemma_paired_restoration {b C₀ : ℝ} (hb : 0 ≤ b) (hC₀ : 0 < C₀) :
    ∃ Ab > 0, ∃ Cb > 0, PairedRestorationContract Ab Cb C₀ b :=
  ⟨restorationPairedBandwidth logisticMatrixConstant b,
    restorationPairedBandwidth_pos _ _, restorationPairedConstant logisticMatrixConstant C₀,
    restorationPairedConstant_pos logisticMatrixConstant_ge_one hC₀,
    paired_restoration_contract hb hC₀⟩

end

end RectangleCLT.Companion.SplitV4
