import RectangleCLTCompanion.RestorationIntegration

/-! Integrability of the actual limit of an absolutely L¹-summable series.
This records integrability separately from its Bochner integral value. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

theorem integrable_of_hasSum_integral_norm
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω)
    (F : ℕ → Ω → ℝ) (f : Ω → ℝ)
    (hFi : ∀ ℓ, Integrable (F ℓ) ν)
    (hf : ∀ ω, HasSum (fun ℓ => F ℓ ω) (f ω))
    (hsum : Summable (fun ℓ => ∫ ω, ‖F ℓ ω‖ ∂ν)) : Integrable f ν := by
  let S : ℕ → Ω → ℝ := fun N ω => ∑ ℓ ∈ Finset.range N, F ℓ ω
  have hSi (N : ℕ) : Integrable (S N) ν :=
    integrable_finset_sum _ (fun ℓ _ => hFi ℓ)
  have hlim (ω : Ω) : Filter.Tendsto (fun N => S N ω) Filter.atTop (nhds (f ω)) :=
    (hf ω).tendsto_sum_nat
  have hfm : AEStronglyMeasurable f ν :=
    aestronglyMeasurable_of_tendsto_ae Filter.atTop (fun N => (hSi N).aestronglyMeasurable)
      (Filter.Eventually.of_forall hlim)
  have hbound (N : ℕ) : (∫ ω, ‖S N ω‖ ∂ν) ≤ ∑' ℓ, ∫ ω, ‖F ℓ ω‖ ∂ν := by
    calc
      _ ≤ ∫ ω, ∑ ℓ ∈ Finset.range N, ‖F ℓ ω‖ ∂ν :=
        integral_mono_ae (hSi N).norm
          (integrable_finset_sum _ (fun ℓ _ => (hFi ℓ).norm))
          (Filter.Eventually.of_forall (fun ω => norm_sum_le _ _))
      _ = ∑ ℓ ∈ Finset.range N, ∫ ω, ‖F ℓ ω‖ ∂ν :=
        integral_finset_sum _ (fun ℓ _ => (hFi ℓ).norm)
      _ ≤ _ := hsum.sum_le_tsum _ (fun ℓ _ => integral_nonneg (fun _ => norm_nonneg _))
  have hbound' (N : ℕ) : (∫⁻ ω, ‖S N ω‖ₑ ∂ν) ≤
      ENNReal.ofReal (∑' ℓ, ∫ ω, ‖F ℓ ω‖ ∂ν) := by
    rw [← ofReal_integral_norm_eq_lintegral_enorm (hSi N)]
    exact ENNReal.ofReal_le_ofReal (hbound N)
  have hfatou : (∫⁻ ω, ‖f ω‖ₑ ∂ν) ≤
      ENNReal.ofReal (∑' ℓ, ∫ ω, ‖F ℓ ω‖ ∂ν) := by
    calc
      _ = ∫⁻ ω, Filter.liminf (fun N => ‖S N ω‖ₑ) Filter.atTop ∂ν := by
        apply lintegral_congr
        intro ω
        exact ((continuous_enorm.tendsto (f ω)).comp (hlim ω)).liminf_eq.symm
      _ ≤ Filter.liminf (fun N => ∫⁻ ω, ‖S N ω‖ₑ ∂ν) Filter.atTop :=
        lintegral_liminf_le' (fun N => (hSi N).aestronglyMeasurable.enorm)
      _ ≤ _ := by
        exact Filter.liminf_le_of_frequently_le
          (Filter.Eventually.frequently (Filter.Eventually.of_forall hbound'))
  exact ⟨hfm, lt_of_le_of_lt hfatou ENNReal.ofReal_lt_top⟩

end
end RectangleCLT.Companion
