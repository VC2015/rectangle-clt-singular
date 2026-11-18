import RectangleCLTCompanion.SubexponentialOrlicz
import Mathlib.Analysis.SpecificLimits.Basic

/-! Endpoint closedness for the manuscript's infimum-based Orlicz norm.
The limiting exponential moment is a genuine integrable function. -/

namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion
open scoped Topology ENNReal
noncomputable section

theorem mem_psi1Scales_of_norm_le {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {X : Ω → ℝ} (hX : Measurable X) {K : ℝ}
    (hK : 0 < K) (hnorm : psi1Norm μ X ≤ ENNReal.ofReal K) :
    K ∈ psi1Scales μ X := by
  obtain ⟨hne,hle⟩ := (psi1Norm_le_iff (μ := μ) (X := X) hK.le).mp hnorm
  let s : ℕ → ℝ := fun n => K + 1 / ((n:ℝ)+1)
  have hs (n : ℕ) : s n ∈ psi1Scales μ X := by
    have hp : (0:ℝ) < 1/((n:ℝ)+1) := by positivity
    have hlt : sInf (psi1Scales μ X) < s n := hle.trans_lt (by dsimp [s]; linarith)
    obtain ⟨t,ht,hts⟩ := (csInf_lt_iff (psi1Scales_bddBelow μ X) hne).mp hlt
    exact psi1Scales_mono hX ht hts.le
  have hslim : Tendsto s atTop (𝓝 K) := by
    simpa only [add_zero] using tendsto_const_nhds.add tendsto_one_div_add_atTop_nhds_zero_nat
  let f : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal (Real.exp (|X ω|/s n))
  let F : Ω → ℝ := fun ω => Real.exp (|X ω|/K)
  have hf (n : ℕ) : Measurable (f n) := by
    exact (((hX.norm.div_const (s n)).exp).ennreal_ofReal)
  have hF : Measurable F := (hX.norm.div_const K).exp
  have hlim (ω : Ω) : Tendsto (fun n => f n ω) atTop (𝓝 (ENNReal.ofReal (F ω))) := by
    have hh : Tendsto (fun n => |X ω|/s n) atTop (𝓝 (|X ω|/K)) :=
      tendsto_const_nhds.div hslim hK.ne'
    exact ENNReal.continuous_ofReal.continuousAt.tendsto.comp (Real.continuous_exp.continuousAt.tendsto.comp hh)
  have hb (n : ℕ) : (∫⁻ ω, f n ω ∂μ) ≤ 2 := by
    rw [show (∫⁻ ω, f n ω ∂μ) = ENNReal.ofReal (∫ ω, Real.exp (|X ω|/s n) ∂μ) from
      (ofReal_integral_eq_lintegral_ofReal (hs n).2.1 (ae_of_all _ fun _ => Real.exp_nonneg _)).symm]
    exact (ENNReal.ofReal_le_ofReal (hs n).2.2).trans_eq (by norm_num)
  have hbound : (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) ≤ 2 := by
    have hh := lintegral_liminf_le (μ := μ) hf
    simp only [(hlim _).liminf_eq] at hh
    exact hh.trans (liminf_le_of_frequently_le' (Eventually.of_forall hb).frequently)
  have hi : Integrable F μ := by
    apply (lintegral_ofReal_ne_top_iff_integrable hF.aestronglyMeasurable
      (ae_of_all _ fun _ => Real.exp_nonneg _)).mp
    exact ne_top_of_le_ne_top (by norm_num) hbound
  refine ⟨hK,hi,?_⟩
  have hh := ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun _ => Real.exp_nonneg _)
  rw [←hh] at hbound
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0:ℝ) ≤ 2)).mp (by simpa using hbound)

theorem psi1_exponentialHypotheses_exact
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}
    {X : Fin n → Ω → Vector p} {K : ℝ} (h : Psi1IndependentHypotheses μ X K) :
    SubexponentialIndependentHypotheses μ X K := by
  have hs (i : Fin n) (j : Fin p) := mem_psi1Scales_of_norm_le
    ((measurable_pi_apply j).comp (h.measurable i))
    (zero_lt_one.trans_le h.one_le_scale) (h.psi1_le i j)
  exact ⟨h.measurable,h.independent,h.centered,fun i j => (hs i j).2.1,
    fun i j => (hs i j).2.2,h.one_le_scale⟩

end
end RectangleCLTArxivV1
