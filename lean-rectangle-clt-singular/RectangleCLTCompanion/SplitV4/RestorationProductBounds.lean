import RectangleCLTCompanion.SplitV4.RestorationPairedBounds

/-! Source-scale B.2 bounds on the genuine independent-Gaussian product
model. The remaining B.4 hypothesis is the actual matrix-integral estimate.
The source's possible zero smoothing scale is included. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def restorationPairedBandwidth (C b : ℝ) : ℝ := max 1 (restorationBandwidthConstant C * b)

def restorationPairedConstant (C C₀ : ℝ) : ℝ := 42 * C ^ 3 * C₀

theorem restorationPairedBandwidth_pos (C b : ℝ) : 0 < restorationPairedBandwidth C b :=
  zero_lt_one.trans_le (le_max_left _ _)

theorem restorationPairedConstant_pos {C C₀ : ℝ} (hC : 1 ≤ C) (hC₀ : 0 < C₀) :
    0 < restorationPairedConstant C C₀ := by
  unfold restorationPairedConstant
  positivity

theorem restorationPairedBandwidth_suffices {p : ℕ} (s : FaceSmoother p)
    {C b δ : ℝ} (hδ : 0 ≤ δ)
    (hband : restorationPairedBandwidth C b * δ ≤ s.bandwidth) :
    restorationBandwidthConstant C * (b * δ) ≤ s.bandwidth := by
  calc
    _ = (restorationBandwidthConstant C * b) * δ := (mul_assoc _ _ _).symm
    _ ≤ restorationPairedBandwidth C b * δ :=
      mul_le_mul_of_nonneg_right (le_max_right _ _) hδ
    _ ≤ _ := hband

theorem restoration_paired_baseline_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C C₀ : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C
      (C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)))
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ b : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ b * δ)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hC₀ : 0 ≤ C₀)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hband : restorationPairedBandwidth C b * δ ≤ s.bandwidth) :
    |restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y v σ| ≤
      restorationPairedConstant C C₀ / σ ^ 2 * δ * dimensionLog p * Real.sqrt (dimensionLog p) ∧
    |restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ| ≤
      restorationPairedConstant C C₀ / σ ^ 2 * δ ^ 2 / s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) := by
  by_cases hσ : σ = 0
  · have hd := restoration_scale_zero_forces_delta_zero hp hδ hscale hσ
    have hY₀ (i : Fin n) : ∀ᵐ ω ∂μ, Y i ω = 0 :=
      (hYb i).mono (fun _ hω => norm_le_zero_iff.mp (hd ▸ hω))
    rw [restorationThirdExpectation_eq_zero_of_ae_zero (mΩ := mΩ) s μ A V Z Y v σ hY₀,
      restorationFourthExpectation_eq_zero_of_ae_zero (mΩ := mΩ) s μ A V Z Y W v σ hY₀]
    simp [hσ]
  · have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
    have hT : 0 ≤ C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₀ s.bandwidth_pos.le) hL) (Real.sqrt_nonneg _)
    have hmain := restoration_paired_baseline_of_matrixEstimate (mΩ := mΩ) s μ H hH A V hV hσ hmatrix
      Z hZm hZ Y W v hY hW hv hδ (mul_nonneg hb hδ) hYb hWb hvb hbudget hC hT
      (restorationPairedBandwidth_suffices s hδ hband)
    constructor
    · apply hmain.1.trans_eq
      unfold restorationPairedConstant
      field_simp [s.bandwidth_pos.ne', hσ]
      ring
    · apply hmain.2.trans_eq
      unfold restorationPairedConstant
      field_simp [s.bandwidth_pos.ne', hσ]
      ring

theorem restoration_third_relative_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C C₀ : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C
      (C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)))
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    {δ M : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hbudget : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => FaceSmoother.normalDot f (Y i z)) ω) u| ≤ M * vectorNormSq u)
    (hC : 1 ≤ C) (hC₀ : 0 ≤ C₀)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ) :
    |restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y (fun _ _ => 0) σ| ≤
      restorationPairedConstant C C₀ / σ ^ 2 * M * dimensionLog p * Real.sqrt (dimensionLog p) := by
  by_cases hσ : σ = 0
  · have hd := restoration_scale_zero_forces_delta_zero hp hδ hscale hσ
    have hY₀ (i : Fin n) : ∀ᵐ ω ∂μ, Y i ω = 0 :=
      (hYb i).mono (fun _ hω => norm_le_zero_iff.mp (hd ▸ hω))
    rw [restorationThirdExpectation_eq_zero_of_ae_zero (mΩ := mΩ) s μ A V Z Y (fun _ _ => 0) σ hY₀]
    simp [hσ]
  · have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
    have hT : 0 ≤ C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₀ s.bandwidth_pos.le) hL) (Real.sqrt_nonneg _)
    have hmain := restoration_third_relative_signed_of_matrixEstimate (mΩ := mΩ) s μ H hH A V hV hσ hmatrix
      Z hZm hZ Y hY hδ hM hYb hbudget hC hT
    apply hmain.trans_eq
    unfold restorationPairedConstant
    field_simp [s.bandwidth_pos.ne', hσ]
    ring

theorem restoration_fourth_relative_product
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {σ C C₀ : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V C
      (C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)))
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    {δ b M : ℝ} (hδ : 0 ≤ δ) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ b * δ)
    (hbudgetY : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (Y i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hbudgetW : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => (FaceSmoother.normalDot f (W i z)) ^ 2) ω) u ≤ M * vectorNormSq u)
    (hC : 1 ≤ C) (hC₀ : 0 ≤ C₀)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hband : restorationPairedBandwidth C b * δ ≤ s.bandwidth) :
    |restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ| ≤
      restorationPairedConstant C C₀ / σ ^ 2 * M / s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) := by
  by_cases hσ : σ = 0
  · have hd := restoration_scale_zero_forces_delta_zero hp hδ hscale hσ
    have hY₀ (i : Fin n) : ∀ᵐ ω ∂μ, Y i ω = 0 :=
      (hYb i).mono (fun _ hω => norm_le_zero_iff.mp (hd ▸ hω))
    rw [restorationFourthExpectation_eq_zero_of_ae_zero (mΩ := mΩ) s μ A V Z Y W v σ hY₀]
    simp [hσ]
  · have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
    have hT : 0 ≤ C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p) :=
      mul_nonneg (mul_nonneg (mul_nonneg hC₀ s.bandwidth_pos.le) hL) (Real.sqrt_nonneg _)
    have hmain := restoration_fourth_relative_pair_of_matrixEstimate (mΩ := mΩ) s μ H hH A V hV hσ hmatrix
      Z hZm hZ Y W v hY hW hv hδ (mul_nonneg hb hδ) hM hYb hWb hvb hbudgetY hbudgetW hC hT
      (restorationPairedBandwidth_suffices s hδ hband)
    apply hmain.trans_eq
    unfold restorationPairedConstant
    field_simp [s.bandwidth_pos.ne', hσ]
    ring

end

end RectangleCLT.Companion.SplitV4
