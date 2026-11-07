import RectangleCLTCompanion.SplitV4.SymmetricFamilyProperties
import Mathlib.MeasureTheory.Function.LpSeminorm.TriangleInequality

/-! Genuine Lq envelope, with the common Bernoulli activation retained. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem memLp_family_finite {Ω E : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) (p : ℝ≥0∞) : MemLp f p μ := by
  classical
  apply (memLp_top_of_bound (measurable_of_finite f).aestronglyMeasurable
    (∑ ω, ‖f ω‖) (ae_of_all _ (fun ω =>
      Finset.single_le_sum (fun w _ => norm_nonneg (f w)) (Finset.mem_univ ω)))).mono_exponent le_top

theorem familyFinite_minkowski {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f g : Ω → ℝ) {q : ℝ} (hq : 1 ≤ q) :
    (∫ ω, ‖f ω + g ω‖ ^ q ∂μ) ^ (1 / q) ≤
      (∫ ω, ‖f ω‖ ^ q ∂μ) ^ (1 / q) + (∫ ω, ‖g ω‖ ^ q ∂μ) ^ (1 / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  let p : ℝ≥0∞ := ENNReal.ofReal q
  have hp0 : p ≠ 0 := (ENNReal.ofReal_pos.mpr hqpos).ne'
  have hp1 : 1 ≤ p := by simpa only [p, ← ENNReal.ofReal_one] using ENNReal.ofReal_le_ofReal hq
  have hpq : p.toReal = q := ENNReal.toReal_ofReal hqpos.le
  have hf := memLp_family_finite μ f p
  have hg := memLp_family_finite μ g p
  have hh := eLpNorm_add_le hf.aestronglyMeasurable hg.aestronglyMeasurable hp1
  rw [(memLp_family_finite μ (f + g) p).eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    hf.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top,
    hg.eLpNorm_eq_integral_rpow_norm hp0 ENNReal.ofReal_ne_top] at hh
  have hreal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨ENNReal.ofReal_ne_top, ENNReal.ofReal_ne_top⟩) hh
  rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top] at hreal
  simpa only [hpq, one_div, Pi.add_apply, ENNReal.toReal_add, ENNReal.toReal_ofReal
    (Real.rpow_nonneg (integral_nonneg (fun ω => Real.rpow_nonneg (norm_nonneg _) _)) _)] using hreal

theorem integral_familySeed_indicator_function (P : SymmetricFamilyParameters) (m : ℕ) (f : Bool → ℝ) :
    (∫ z : FamilySeed m, f z.2.2.1 ∂familySeedLaw P m) = ∫ b, f b ∂familyBernoulli (familyTheta P) := by
  have h1 := MeasureTheory.integral_fun_snd (μ := familySignLaw m) (ν := familyRestLaw P m)
    (fun z : FamilySigns m × (Bool × FamilySigns m) => f z.2.1)
  have h2 := MeasureTheory.integral_fun_snd (μ := familySignLaw m)
    (ν := (familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))
    (fun z : Bool × FamilySigns m => f z.1)
  have h3 := MeasureTheory.integral_fun_fst (μ := familyBernoulli (familyTheta P))
    (ν := familyMaskLaw P m) f
  simp only [measureReal_univ_eq_one, one_smul] at h1 h2 h3
  exact h1.trans (h2.trans h3)


theorem integral_familyActivation_rpow (P : SymmetricFamilyParameters) (m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    (∫ z : FamilySeed m, ‖P.amplitude * familyIndicator z.2.2.1‖ ^ q ∂familySeedLaw P m) =
      P.theta * P.amplitude ^ q := by
  rw [integral_familySeed_indicator_function P m
    (fun b => ‖P.amplitude * familyIndicator b‖ ^ q), integral_familyBernoulli]
  simp [familyIndicator, Real.norm_eq_abs, abs_of_pos P.amplitude_pos,
    Real.zero_rpow hq.ne', familyTheta]

theorem family_rpow_q_root {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    (a ^ q) ^ (1 / q) = a := by
  rw [← Real.rpow_mul ha]
  simp [hq.ne']

theorem familyObservation_Lq_envelope (P : SymmetricFamilyParameters) (m : ℕ)
    {q : ℝ} (hq : 1 ≤ q) :
    (∫ z : FamilySeed m, ‖familyObservation P z‖ ^ q ∂familySeedLaw P m) ^ (1 / q) ≤
      P.scale + P.amplitude * P.theta ^ (1 / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnonneg (z : FamilySeed m) : 0 ≤ P.scale + P.amplitude * familyIndicator z.2.2.1 :=
    add_nonneg P.scale_pos.le (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _))
  have hmono : (∫ z : FamilySeed m, ‖familyObservation P z‖ ^ q ∂familySeedLaw P m) ≤
      ∫ z : FamilySeed m, ‖P.scale + P.amplitude * familyIndicator z.2.2.1‖ ^ q ∂familySeedLaw P m := by
    apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
    intro z
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact Real.rpow_le_rpow (norm_nonneg _) (familyObservation_norm_le P z) hqpos.le
  have htri := familyFinite_minkowski (familySeedLaw P m) (fun _ => P.scale)
    (fun z : FamilySeed m => P.amplitude * familyIndicator z.2.2.1) hq
  have hc : (∫ z : FamilySeed m, ‖P.scale‖ ^ q ∂familySeedLaw P m) ^ (1 / q) = P.scale := by
    simp only [integral_const, measureReal_univ_eq_one, one_smul, Real.norm_eq_abs,
      abs_of_pos P.scale_pos]
    exact family_rpow_q_root P.scale_pos.le hqpos
  have ha : (∫ z : FamilySeed m, ‖P.amplitude * familyIndicator z.2.2.1‖ ^ q
      ∂familySeedLaw P m) ^ (1 / q) = P.amplitude * P.theta ^ (1 / q) := by
    rw [integral_familyActivation_rpow P m hqpos,
      Real.mul_rpow P.theta_pos.le (Real.rpow_nonneg P.amplitude_pos.le q),
      family_rpow_q_root P.amplitude_pos.le hqpos]
    ring
  exact (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    hmono (by positivity)).trans (by simpa only [hc, ha] using htri)

theorem familyRawObservations_Lq_envelope (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) {q : ℝ} (hq : 1 ≤ q) :
    (∫ z, ‖familyRawObservations P i z‖ ^ q ∂familyArrayLaw P n m) ^ (1 / q) ≤
      P.scale + P.amplitude * P.theta ^ (1 / q) := by
  have hi := (familyRawObservations_identDistrib P (m := m) i).comp
    (continuous_norm.measurable.pow_const q)
  have heq := hi.integral_eq
  change (∫ z, ‖familyRawObservations P i z‖ ^ q ∂familyArrayLaw P n m) =
    ∫ z, ‖familyObservation P z‖ ^ q ∂familySeedLaw P m at heq
  rw [heq]
  exact familyObservation_Lq_envelope P m hq

end
end RectangleCLT.Companion.SplitV4
