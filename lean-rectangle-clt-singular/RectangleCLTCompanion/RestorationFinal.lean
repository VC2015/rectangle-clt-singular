import RectangleCLTCompanion.RestorationFourth
import RectangleCLTCompanion.RestorationScales
import RectangleCLTCompanion.RestorationMeasurability

/-! A concrete translated paired-fourth restoration theorem, conditional
only on the independently supplied actual averaged selector matrix estimate.
All structural coefficient measurability and integrability are discharged. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

/-- Appendix B restoration for the actual fourth-convolution experiment.
The output is integrable and has the universal factor `42 * C^3` under a
linear bandwidth condition; it assumes no fourth-derivative estimate. -/
theorem restorationFourth_le_of_matrixEstimate
    {p n : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : σ ≠ 0) (V : Ω → Vector p)
    (Z : Ω → Fin n → Ξ → Vector p) (Y W : Ω → Fin n → Ξ → Vector p)
    (v : Fin n → Ω → Ξ → Vector p) {δ K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν (σ • A) V C T)
    (hV : Measurable V)
    (hZm : ∀ i, Measurable (fun wa : Ω × Ξ => Z wa.1 i wa.2))
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hY : ∀ i, Measurable (fun wa : Ω × Ξ => Y wa.1 i wa.2))
    (hW : ∀ i, Measurable (fun wa : Ω × Ξ => W wa.1 i wa.2))
    (hv : ∀ i, Measurable (fun wa : Ω × Ξ => v i wa.1 wa.2))
    (hδ : 0 ≤ δ) (hYb : ∀ ω i a, ‖Y ω i a‖ ≤ δ) (hWb : ∀ ω i a, ‖W ω i a‖ ≤ δ)
    (hK : 0 ≤ K) (hR : 0 ≤ R) (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤ K * vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hband : restorationBandwidthConstant C * R ≤ s.bandwidth) :
    Integrable (fun ω => fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω)) ν ∧
    |∫ ω, fixedRestorationFourthExpectation s μ A σ (V ω) (Z ω)
      (Y ω) (W ω) (fun i => v i ω) ∂ν| ≤
        (42 * C ^ 3 * K * δ ^ 2 * T) / (s.bandwidth ^ 2 * σ ^ 2) := by
  have hZ' (ω : Ω) (i : Fin n) : Measurable (Z ω i) :=
    (hZm i).comp (measurable_const.prodMk measurable_id)
  have hY' (ω : Ω) (i : Fin n) : Measurable (Y ω i) :=
    (hY i).comp (measurable_const.prodMk measurable_id)
  have hW' (ω : Ω) (i : Fin n) : Measurable (W ω i) :=
    (hW i).comp (measurable_const.prodMk measurable_id)
  have hv' (i : Fin n) (ω : Ω) : Measurable (v i ω) :=
    (hv i).comp (measurable_const.prodMk measurable_id)
  have hc1 (i : Fin n) (α : Fin 1 → Face p) : Measurable
      (fun wa : Ω × Ξ => restorationHessianCoefficientsOne Y W i α wa.1 wa.2) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).mul
      ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hW i))
  have hc2 (i : Fin n) (α : Fin 2 → Face p) : Measurable
      (fun wa : Ω × Ξ => restorationHessianCoefficientsTwo Y W i α wa.1 wa.2) :=
    ((FaceSmoother.continuous_normalDot (α 0)).measurable.comp (hY i)).mul
      ((FaceSmoother.continuous_normalDot (α 1)).measurable.comp (hW i))
  have hhalf := restoration_small_of_bandwidth s hC hR hband
  have hs := restorationFourthExpectation_integrable_and_bound s ν μ A hσ V Z Y W v
    hmatrix hV hZ' hZ hY' hW' hv' hδ hYb hWb hK hR hvb hbudget
    (fun ℓ α β j l => measurable_translatedRestorationCoefficient s μ Z
      (restorationHessianCoefficientsOne Y W) v hZm hc1 hv α β j l)
    (fun ℓ α β j l => measurable_translatedRestorationCoefficient s μ Z
      (restorationHessianCoefficientsTwo Y W) v hZm hc2 hv α β j l)
    hC hT (hhalf.trans_lt (by norm_num))
  refine ⟨hs.1, hs.2.trans ?_⟩
  have hcap := two_restorationSelectorCaps_le s (sq_nonneg δ) hK hR hC hT hhalf
  calc
    _ ≤ (42 * δ ^ 2 * K * C ^ 3 * T) / (s.bandwidth ^ 2 * σ ^ 2) :=
      div_le_div_of_nonneg_right hcap (mul_nonneg (sq_nonneg _) (sq_nonneg _))
    _ = _ := by ring

end
end RectangleCLT.Companion
