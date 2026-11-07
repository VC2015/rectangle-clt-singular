import RectangleCLTCompanion.SplitV4.Restoration

/-! Almost-sure zero shifts in B.2's signed M1 refinement. The original
conditional-independence assumption is retained; only genuine derivative
integrals are transported under the a.e. equality of the shifts. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem restorationThirdExpectation_congr_ae_shift
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (Z : Fin n → Ω → Vector r) (Y v v' : Fin n → Ω → Vector p) (σ : ℝ)
    (hvv' : ∀ i, v i =ᵐ[μ] v' i) :
    restorationThirdExpectation s μ A V Z Y v σ = restorationThirdExpectation s μ A V Z Y v' σ := by
  unfold restorationThirdExpectation
  apply integral_congr_ae
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hvv')] with z hz
  exact Finset.sum_congr rfl (fun i _ => by rw [hz i])

theorem restorationOriginalThird_congr_ae_shift
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (G : Ω → Vector r) (Z : Fin n → Ω → Vector r)
    (Y v v' : Fin n → Ω → Vector p) (σ : ℝ) (hvv' : ∀ i, v i =ᵐ[μ] v' i) :
    restorationOriginalThird s μ A V G Z Y v σ = restorationOriginalThird s μ A V G Z Y v' σ := by
  unfold restorationOriginalThird
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact (hvv' i).mono (fun _ hω => by dsimp only; rw [hω])

/-- Signed relative M1 under the source's a.e. zero-shift interpretation.
The actual B.4 estimate is discharged from unconditional base concentration;
no changed conditional law or additional independence assumption is used. -/
theorem restoration_signed_relative_ae_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ} (hp : 1 ≤ p)
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
    {δ σ M C₀ : ℝ} (hδ : 0 ≤ δ) (hM : 0 ≤ M) (hC₀ : 0 < C₀)
    (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ) (hδh : δ ≤ s.bandwidth)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hvzero : ∀ i, v i =ᵐ[μ] fun _ => 0)
    (hbudget : ∀ f : Face p, ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z
        (fun i z => FaceSmoother.normalDot f (Y i z)) ω) u| ≤ M * vectorNormSq u)
    (hconcentration : RectangleBaseConcentration
      (@Measure.map Ω (Vector p) mΩ inferInstance V μ) C₀ δ (dimensionLog p)) :
    |restorationOriginalThird (mΩ := mΩ) s μ A V G Z Y v σ| ≤
      restorationPairedConstant logisticMatrixConstant C₀ / σ ^ 2 * M *
        dimensionLog p * Real.sqrt (dimensionLog p) := by
  letI : MeasurableSpace Ω := mΩ
  have hm : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ (σ • A) V logisticMatrixConstant
      (C₀ * s.bandwidth * dimensionLog p * Real.sqrt (dimensionLog p)) := by
    simpa only [mul_assoc] using averagedSelectorMatrixEstimate_of_rectangle_concentration hp μ V
      (hV.mono hH le_rfl) s A hA hC₀ hδ hδh
      ((mul_nonneg hδ (Real.sqrt_nonneg _)).trans hscale) hscale hconcentration
  have he := (restorationThirdExpectation_conditional_transport (mΩ := mΩ) (σ := σ) s μ H hH A V hV
    Z Y W v hZm hZ hY hW hv G hG hGlaw hHG hCI hδ hYb).2
  change restorationOriginalThird s μ A V G Z Y v σ = _ at he
  rw [he, restorationThirdExpectation_congr_ae_shift s μ A V Z Y v (fun _ _ => 0) σ hvzero]
  exact restoration_third_relative_product (mΩ := mΩ) hp s μ H hH A V hV hm
    Z hZm hZ Y hY hδ hM hYb hbudget logisticMatrixConstant_ge_one hC₀.le hscale

end

end RectangleCLT.Companion.SplitV4
