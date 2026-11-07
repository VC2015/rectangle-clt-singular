import RectangleCLTCompanion.SubexponentialOrlicz
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Analysis.SpecificLimits.Basic

/-! The actual endpoint-closedness step printed in Appendix D: scales
strictly above K decrease to K, and monotone convergence proves genuine
exponential integrability at K itself. No factor-two replacement is used. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped ENNReal Topology
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem mem_psi1Scales_of_norm_le_of_lt
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {K t : ℝ} (hK : 0 ≤ K)
    (hnorm : psi1Norm μ X ≤ ENNReal.ofReal K) (hKt : K < t) :
    t ∈ psi1Scales μ X := by
  obtain ⟨hne,hle⟩ := (psi1Norm_le_iff hK).mp hnorm
  obtain ⟨s,hs,hst⟩ := (csInf_lt_iff (psi1Scales_bddBelow μ X) hne).mp (hle.trans_lt hKt)
  exact psi1Scales_mono hX hs hst.le

theorem mem_psi1Scales_at_positive_norm_bound
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}
    (hX : Measurable X) {K : ℝ} (hK : 0 < K)
    (hnorm : psi1Norm μ X ≤ ENNReal.ofReal K) : K ∈ psi1Scales μ X := by
  let s : ℕ → ℝ := fun n => K+1/((n : ℝ)+1)
  let f : ℕ → Ω → ℝ := fun n ω => Real.exp (|X ω|/s n)
  let F : Ω → ℝ := fun ω => Real.exp (|X ω|/K)
  have hs (n : ℕ) : s n ∈ psi1Scales μ X := by
    apply mem_psi1Scales_of_norm_le_of_lt hX hK.le hnorm
    dsimp [s]
    have hh : (0 : ℝ) < 1/((n : ℝ)+1) := by positivity
    linarith
  have hs_antitone : Antitone s := by
    intro n m hnm
    apply add_le_add_left
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.add_le_add_right hnm 1)
  have hs_lim : Tendsto s atTop (𝓝 K) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := K)).add tendsto_one_div_add_atTop_nhds_zero_nat
  have hf_meas (n : ℕ) : Measurable (f n) := by
    exact ((hX.abs.div_const _).exp)
  have hF_meas : Measurable F := (hX.abs.div_const K).exp
  have hf_mono (ω : Ω) : Monotone (fun n => f n ω) := by
    intro n m hnm
    apply Real.exp_le_exp.mpr
    exact div_le_div_of_nonneg_left (abs_nonneg _) (hs m).1 (hs_antitone hnm)
  have hf_lim (ω : Ω) : Tendsto (fun n => f n ω) atTop (𝓝 (F ω)) := by
    exact Real.continuous_exp.continuousAt.tendsto.comp
      (tendsto_const_nhds.div hs_lim hK.ne')
  have hlin_lim := lintegral_tendsto_of_tendsto_of_monotone (μ := μ)
    (fun n => (hf_meas n).ennreal_ofReal.aemeasurable)
    (ae_of_all _ (fun ω n m hnm => ENNReal.ofReal_le_ofReal (hf_mono ω hnm)))
    (ae_of_all _ (fun ω => ENNReal.continuous_ofReal.continuousAt.tendsto.comp (hf_lim ω)))
  have hlin_bound : (∫⁻ ω, ENNReal.ofReal (F ω) ∂μ) ≤ ENNReal.ofReal 2 := by
    apply le_of_tendsto hlin_lim
    apply Eventually.of_forall
    intro n
    rw [← ofReal_integral_eq_lintegral_ofReal (hs n).2.1
      (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
    exact ENNReal.ofReal_le_ofReal (hs n).2.2
  have hFi : Integrable F μ :=
    (lintegral_ofReal_ne_top_iff_integrable hF_meas.aestronglyMeasurable
      (ae_of_all _ (fun ω => (Real.exp_pos _).le))).mp
        (ne_of_lt (hlin_bound.trans_lt ENNReal.ofReal_lt_top))
  refine ⟨hK,hFi,?_⟩
  have hh : ENNReal.ofReal (∫ ω, F ω ∂μ) ≤ ENNReal.ofReal 2 := by
    rw [ofReal_integral_eq_lintegral_ofReal hFi (ae_of_all _ (fun ω => (Real.exp_pos _).le))]
    exact hlin_bound
  exact (ENNReal.ofReal_le_ofReal_iff (by norm_num : (0 : ℝ) ≤ 2)).mp hh

theorem psi1_hypotheses_exponential_at_same_scale
    {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}
    {X : Fin n → Ω → Vector p} {K : ℝ} (h : Psi1IndependentHypotheses μ X K) :
    SubexponentialIndependentHypotheses μ X K := by
  have hK : 0 < K := zero_lt_one.trans_le h.one_le_scale
  have hs (i : Fin n) (j : Fin p) := mem_psi1Scales_at_positive_norm_bound
    ((measurable_pi_apply j).comp (h.measurable i)) hK (h.psi1_le i j)
  exact ⟨h.measurable,h.independent,h.centered,
    fun i j => (hs i j).2.1,fun i j => (hs i j).2.2,h.one_le_scale⟩

end
end RectangleCLT.Companion.SplitV4.Printed
