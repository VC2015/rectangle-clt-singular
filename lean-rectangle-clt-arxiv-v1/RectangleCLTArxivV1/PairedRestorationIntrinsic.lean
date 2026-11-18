import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTCompanion.SplitV4.Restoration

/-!
# Lemma B.2 with the intrinsic boundary coefficient

The actual conditional joint-array model and its Gaussian transport are retained.
Only the concentration constant is rescaled. In particular, neither the Gaussian
scale condition nor either conditional signed moment budget is weakened.
-/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def IntrinsicPairedRestorationConclusion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (H : MeasurableSpace Ω)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (G : Ω → Vector r)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p) (σ δ κ Cb : ℝ) : Prop :=
  (|restorationOriginalThird (mΩ := mΩ) s μ A V G Z Y v σ| ≤
      Cb / σ ^ 2 * δ * dimensionLog p * κ ∧
    |restorationOriginalFourth (mΩ := mΩ) s μ A V G Z Y W v σ| ≤
      Cb / σ ^ 2 * δ ^ 2 / s.bandwidth * dimensionLog p * κ) ∧
  (v = (fun _ _ => 0) → ∀ M : ℝ, 0 ≤ M →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => FaceSmoother.normalDot f (Y i z)) ω) u| ≤ M * vectorNormSq u) →
    |restorationOriginalThird (mΩ := mΩ) s μ A V G Z Y v σ| ≤
      Cb / σ ^ 2 * M * dimensionLog p * κ) ∧
  (∀ M : ℝ, 0 ≤ M →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (Y i z)) ^ 2) ω) u ≤ M * vectorNormSq u) →
    (∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (W i z)) ^ 2) ω) u ≤ M * vectorNormSq u) →
    |restorationOriginalFourth (mΩ := mΩ) s μ A V G Z Y W v σ| ≤
      Cb / σ ^ 2 * M / s.bandwidth * dimensionLog p * κ)

set_option linter.unusedVariables false in
/-- Complete source contract of B.2, including both optional refinements.
The conditional-independence premise is bounded-indicator factorization,
so no disintegration or standard-Borel restriction is hidden. -/
def IntrinsicPairedRestorationContract (Ab Cb C₀ b : ℝ) : Prop :=
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
    {δ σ κ : ℝ} (hκ : 0 < κ) (hδ : 0 ≤ δ) (hσ₁ : σ ≤ 1)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ b * δ)
    (hcov : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hconcentration : IntrinsicRectangleConcentration
      (@Measure.map Ω (Vector p) mΩ inferInstance V μ) C₀ δ κ)
    (hband : Ab * δ ≤ s.bandwidth),
    IntrinsicPairedRestorationConclusion (mΩ := mΩ) s μ H A V G Z Y W v σ δ κ Cb

theorem paired_restoration_contract_intrinsic {b C₀ : ℝ}
    (hb : 0 ≤ b) (hC₀ : 0 < C₀) :
    IntrinsicPairedRestorationContract (restorationPairedBandwidth logisticMatrixConstant b)
      (restorationPairedConstant logisticMatrixConstant C₀) C₀ b := by
  intro Ω mΩ p r n hp s μ hprob H hH A hA V hV Z Y W v hZm hZ hY hW hv
    G hG hGlaw hHG hCI δ σ κ hκ hδ hσ₁ hscale hYb hWb hvb hcov hc hband
  letI : MeasurableSpace Ω := mΩ
  have hroot : 0 < Real.sqrt (dimensionLog p) :=
    Real.sqrt_pos.mpr (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))
  let C' := C₀ * κ / Real.sqrt (dimensionLog p)
  have hC' : 0 < C' := div_pos (mul_pos hC₀ hκ) hroot
  have base := paired_restoration_contract hb hC' hp s μ H hH A hA V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hσ₁ hscale hYb hWb hvb hcov
    (intrinsicRectangleConcentration_rescale hp _ hc) hband
  rcases base with ⟨⟨ht, hf⟩, hthird, hfourth⟩
  have hc' : restorationPairedConstant logisticMatrixConstant C' *
        Real.sqrt (dimensionLog p) =
      restorationPairedConstant logisticMatrixConstant C₀ * κ := by
    unfold restorationPairedConstant
    dsimp only [C']
    field_simp
    ring
  have heq (x : ℝ) :
      restorationPairedConstant logisticMatrixConstant C' / σ ^ 2 * x *
          dimensionLog p * Real.sqrt (dimensionLog p) =
      restorationPairedConstant logisticMatrixConstant C₀ / σ ^ 2 * x *
          dimensionLog p * κ := by
    calc
      _ = (restorationPairedConstant logisticMatrixConstant C' *
          Real.sqrt (dimensionLog p)) / σ ^ 2 * x * dimensionLog p := by ring
      _ = _ := by rw [hc']; ring
  refine ⟨⟨ht.trans_eq (heq δ), ?_⟩, ?_, ?_⟩
  · convert hf.trans_eq (by
      calc
        _ = restorationPairedConstant logisticMatrixConstant C' / σ ^ 2 *
            (δ ^ 2 / s.bandwidth) * dimensionLog p * Real.sqrt (dimensionLog p) := by ring
        _ = _ := heq (δ ^ 2 / s.bandwidth)) using 1 <;> ring
  · intro hvzero M hM hbudget
    exact (hthird hvzero M hM hbudget).trans_eq (heq M)
  · intro M hM hbudgetY hbudgetW
    convert (hfourth M hM hbudgetY hbudgetW).trans_eq (by
      calc
        _ = restorationPairedConstant logisticMatrixConstant C' / σ ^ 2 *
            (M / s.bandwidth) * dimensionLog p * Real.sqrt (dimensionLog p) := by ring
        _ = _ := heq (M / s.bandwidth)) using 1 <;> ring

/-- Full B.2: both baseline bounds and both conditional moment refinements.
The constants precede every dimension, law, threshold, and auxiliary array. -/
theorem lemma_B2_intrinsic_paired_restoration {b C₀ : ℝ}
    (hb : 0 ≤ b) (hC₀ : 0 < C₀) :
    ∃ Ab > 0, ∃ Cb > 0, IntrinsicPairedRestorationContract Ab Cb C₀ b :=
  ⟨restorationPairedBandwidth logisticMatrixConstant b,
    restorationPairedBandwidth_pos _ _, restorationPairedConstant logisticMatrixConstant C₀,
    restorationPairedConstant_pos logisticMatrixConstant_ge_one hC₀,
    paired_restoration_contract_intrinsic hb hC₀⟩

end
end RectangleCLTArxivV1
