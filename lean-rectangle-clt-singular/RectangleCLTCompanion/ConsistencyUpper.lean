import RectangleCLTCompanion.ConsistencyStatement
import RectangleCLT.GeneralMain
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-! The sufficient directions of the exact fixed-gap thresholds.
The nonlinear branches of the general CLT suffice without an additional
logarithmic restriction on the dimension. -/

open MeasureTheory Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

def fixedGapConsistencyModulus (r c : ℝ) : ℝ :=
  r ^ (1 / 3 : ℝ) / c ^ (2 / 3 : ℝ) + Real.sqrt r / c ^ (3 / 4 : ℝ) + r / c

def zeroSkewConsistencyModulus (r c : ℝ) : ℝ :=
  Real.sqrt r / c ^ (3 / 4 : ℝ) + r / c

lemma nonlinear_third_envelope {γ δ L : ℝ}
    (hγ : 0 ≤ γ) (hγδ : γ ≤ δ) (hL : 0 ≤ L) :
    γ ^ (1 / 3 : ℝ) * Real.sqrt L ≤ (δ * L ^ (3 / 2 : ℝ)) ^ (1 / 3 : ℝ) := by
  have hδ := hγ.trans hγδ
  rw [Real.mul_rpow hδ (Real.rpow_nonneg hL _)]
  rw [← Real.rpow_mul hL]
  norm_num only [show (3 / 2 : ℝ) * (1 / 3 : ℝ) = 1 / 2 by norm_num]
  rw [← Real.sqrt_eq_rpow]
  exact mul_le_mul_of_nonneg_right
    (Real.rpow_le_rpow hγ hγδ (by norm_num)) (Real.sqrt_nonneg _)

lemma nonlinear_fourth_envelope {γ δ L : ℝ}
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hγδ : γ ≤ δ ^ 2) (hL : 0 ≤ L) :
    γ ^ (1 / 4 : ℝ) * Real.sqrt L ≤ Real.sqrt (δ * L) := by
  have hr := Real.rpow_le_rpow hγ hγδ (by norm_num : (0 : ℝ) ≤ 1/4)
  have he : (δ ^ 2) ^ (1 / 4 : ℝ) = Real.sqrt δ := by
    rw [← Real.rpow_natCast_mul hδ]
    norm_num only [show (2 : ℝ) * (1 / 4 : ℝ) = 1 / 2 by norm_num]
    exact (Real.sqrt_eq_rpow δ).symm
  rw [he] at hr
  rw [Real.sqrt_mul hδ]
  exact mul_le_mul_of_nonneg_right hr (Real.sqrt_nonneg _)

lemma generalBoundedRate_le_consistencyModulus
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) {δ c₀ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hc₀ : 0 < c₀) (hgap : c₀ ≤ pairGap (covariance μ (sumVector ξ))) :
    generalBoundedRate μ ξ δ (covariance μ (sumVector ξ)) ≤
      fixedGapConsistencyModulus (δ * dimensionLog p ^ (3 / 2 : ℝ)) c₀ := by
  let L := dimensionLog p
  let c := pairGap (covariance μ (sumVector ξ))
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 ≤ L := zero_le_one.trans hL1
  have hc : 0 < c := hc₀.trans_le hgap
  have hLsqrt : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
  have hLpow : L ^ (3 / 2 : ℝ) = L * Real.sqrt L := by
    rw [show (3 / 2 : ℝ) = 1 + 1/2 by norm_num, Real.rpow_add (zero_lt_one.trans_le hL1)]
    simp only [Real.rpow_one, ← Real.sqrt_eq_rpow]
  have htq : δ * L ≤ δ * L ^ (3 / 2 : ℝ) := by
    rw [hLpow]
    nlinarith [mul_nonneg h.delta_nonneg hL]
  have hsq : δ * Real.sqrt L ≤ δ * L ^ (3 / 2 : ℝ) := by
    rw [hLpow]
    exact mul_le_mul_of_nonneg_left
      (le_mul_of_one_le_left (Real.sqrt_nonneg L) hL1) h.delta_nonneg
  have hthird := nonlinear_third_envelope (gamma3_nonneg μ ξ)
    (h.gamma3_le_delta hunit) hL
  have hfourth := nonlinear_fourth_envelope (gamma4_nonneg μ ξ) h.delta_nonneg
    (h.gamma4_le_delta_sq hunit) hL
  have hthird0 : 0 ≤ gamma3 μ ξ ^ (1/3 : ℝ) * Real.sqrt L := mul_nonneg (Real.rpow_nonneg (gamma3_nonneg μ ξ) _) (Real.sqrt_nonneg L)
  have hfourth0 : 0 ≤ gamma4 μ ξ ^ (1/4 : ℝ) * Real.sqrt L := mul_nonneg (Real.rpow_nonneg (gamma4_nonneg μ ξ) _) (Real.sqrt_nonneg L)
  have hthirdCap : generalThirdRate (gamma3 μ ξ) L
      (fullCovarianceScale (covariance μ (sumVector ξ))) c
      (a3 (covariance μ (sumVector ξ))) ≤
      (δ * L ^ (3/2 : ℝ)) ^ (1/3 : ℝ) / c₀ ^ (2/3 : ℝ) := by
    apply (optionalMin_le_fallback _ _ _).trans
    apply (optionalMin_le_fallback _ _ _).trans
    exact div_le_div₀ (Real.rpow_nonneg (mul_nonneg h.delta_nonneg (Real.rpow_nonneg hL _)) _) hthird (Real.rpow_pos_of_pos hc₀ _)
      (Real.rpow_le_rpow hc₀.le hgap (by norm_num))
  have hfourthCap : generalFourthRate (gamma4 μ ξ) L
      (fullCovarianceScale (covariance μ (sumVector ξ))) c
      (a3 (covariance μ (sumVector ξ))) (a4 (covariance μ (sumVector ξ))) ≤
      Real.sqrt (δ * L ^ (3/2 : ℝ)) / c₀ ^ (3/4 : ℝ) := by
    apply (optionalMin_le_fallback _ _ _).trans
    apply (optionalMin_le_fallback _ _ _).trans
    exact div_le_div₀ (Real.sqrt_nonneg _) (hfourth.trans (Real.sqrt_le_sqrt htq))
      (Real.rpow_pos_of_pos hc₀ _) (Real.rpow_le_rpow hc₀.le hgap (by norm_num))
  have hdeltaCap : δ * Real.sqrt L / c ≤ δ * L ^ (3/2 : ℝ) / c₀ :=
    div_le_div₀ (mul_nonneg h.delta_nonneg (Real.rpow_nonneg hL _)) hsq hc₀ hgap
  exact add_le_add (add_le_add hthirdCap hfourthCap) hdeltaCap

lemma generalBoundedRate_zeroSkew_le_consistencyModulus
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) {δ c₀ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hc₀ : 0 < c₀) (hgap : c₀ ≤ pairGap (covariance μ (sumVector ξ)))
    (hcancel : AggregateThirdMomentsVanish μ ξ) :
    generalBoundedRate μ ξ δ (covariance μ (sumVector ξ)) ≤
      zeroSkewConsistencyModulus (δ * dimensionLog p) c₀ := by
  let L := dimensionLog p
  let c := pairGap (covariance μ (sumVector ξ))
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 ≤ L := zero_le_one.trans hL1
  have hc : 0 < c := hc₀.trans_le hgap
  have hzero : gamma3 μ ξ = 0 := (gamma3_eq_zero_iff μ ξ).mpr hcancel
  have hthird : generalThirdRate (gamma3 μ ξ) L
      (fullCovarianceScale (covariance μ (sumVector ξ))) c
      (a3 (covariance μ (sumVector ξ))) = 0 := by
    rw [hzero]
    norm_num [generalThirdRate, optionalMin]
  have hfourth := nonlinear_fourth_envelope (gamma4_nonneg μ ξ) h.delta_nonneg
    (h.gamma4_le_delta_sq hunit) hL
  have hfourthCap : generalFourthRate (gamma4 μ ξ) L
      (fullCovarianceScale (covariance μ (sumVector ξ))) c
      (a3 (covariance μ (sumVector ξ))) (a4 (covariance μ (sumVector ξ))) ≤
      Real.sqrt (δ * L) / c₀ ^ (3/4 : ℝ) := by
    apply (optionalMin_le_fallback _ _ _).trans
    apply (optionalMin_le_fallback _ _ _).trans
    exact div_le_div₀ (Real.sqrt_nonneg _) hfourth (Real.rpow_pos_of_pos hc₀ _)
      (Real.rpow_le_rpow hc₀.le hgap (by norm_num))
  have hsqrt : Real.sqrt L ≤ L := by
    apply (Real.sqrt_le_iff).mpr
    exact ⟨hL, by nlinarith⟩
  have hdeltaCap : δ * Real.sqrt L / c ≤ δ * L / c₀ :=
    div_le_div₀ (mul_nonneg h.delta_nonneg hL)
      (mul_le_mul_of_nonneg_left hsqrt h.delta_nonneg) hc₀ hgap
  change generalThirdRate _ _ _ _ _ + generalFourthRate _ _ _ _ _ _ + _ ≤ _
  rw [hthird, zero_add]
  exact add_le_add hfourthCap hdeltaCap

lemma continuous_fixedGapConsistencyModulus (c : ℝ) :
    Continuous (fun r => fixedGapConsistencyModulus r c) := by
  exact (((Real.continuous_rpow_const (by norm_num : (0 : ℝ) ≤ 1/3)).div_const _).add
    (Real.continuous_sqrt.div_const _)).add (continuous_id.div_const _)

lemma continuous_zeroSkewConsistencyModulus (c : ℝ) :
    Continuous (fun r => zeroSkewConsistencyModulus r c) :=
  (Real.continuous_sqrt.div_const _).add (continuous_id.div_const _)

/-- The sufficient direction of Theorem 5, uniformly over the full
probability class rather than for a preselected sequence of laws. -/
theorem fixedGapUniformConsistency_of_rate_tendsto_zero
    {c₀ : ℝ} (hc₀ : 0 < c₀) (B : ℕ → ℝ) (p : ℕ → ℕ)
    (hp : ∀ n, 1 ≤ p n)
    (hrate : Tendsto (fun n => B n / Real.sqrt n *
      dimensionLog (p n) ^ (3/2 : ℝ)) atTop (𝓝 0)) :
    FixedGapUniformConsistency.{u} c₀ B p := by
  have hlim : Tendsto (fun n => generalCLTConstant * fixedGapConsistencyModulus
      (B n / Real.sqrt n * dimensionLog (p n) ^ (3/2 : ℝ)) c₀) atTop (𝓝 0) := by
    have hh := ((continuous_fixedGapConsistencyModulus c₀).tendsto 0).comp hrate
    simpa [fixedGapConsistencyModulus] using hh.const_mul generalCLTConstant
  intro ε hε
  filter_upwards [hlim.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1]
    with n herr hn
  intro Ω _ μ _ ξ A h hunit hgap hfactor R
  have hh := generalRectangleCLT μ (p n) n (hp n) hn ξ
    (B n / Real.sqrt n) A h hunit (hc₀.trans_le hgap) hfactor R
  exact lt_of_le_of_lt (hh.trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (generalBoundedRate_le_consistencyModulus
      μ (hp n) ξ h hunit hc₀ hgap))
    (zero_le_one.trans generalCLTConstant_ge_one))) herr

/-- Cancellation removes the cubic requirement: δ L → 0 suffices. -/
theorem zeroSkewFixedGapUniformConsistency_of_rate_tendsto_zero
    {c₀ B : ℝ} (hc₀ : 0 < c₀) (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (hrate : Tendsto (fun n : ℕ => B / Real.sqrt n * dimensionLog (p n)) atTop (𝓝 0)) :
    ZeroSkewFixedGapUniformConsistency.{u} c₀ B p := by
  have hlim : Tendsto (fun n : ℕ => generalCLTConstant * zeroSkewConsistencyModulus
      (B / Real.sqrt n * dimensionLog (p n)) c₀) atTop (𝓝 0) := by
    have hh := ((continuous_zeroSkewConsistencyModulus c₀).tendsto 0).comp hrate
    simpa [zeroSkewConsistencyModulus] using hh.const_mul generalCLTConstant
  intro ε hε
  filter_upwards [hlim.eventually (eventually_lt_nhds hε), eventually_ge_atTop 1]
    with n herr hn
  intro Ω _ μ _ ξ A h hunit hgap hfactor hcancel R
  have hh := generalRectangleCLT μ (p n) n (hp n) hn ξ
    (B / Real.sqrt n) A h hunit (hc₀.trans_le hgap) hfactor R
  exact lt_of_le_of_lt (hh.trans (mul_le_mul_of_nonneg_left
    ((min_le_right _ _).trans (generalBoundedRate_zeroSkew_le_consistencyModulus
      μ (hp n) ξ h hunit hc₀ hgap hcancel))
    (zero_le_one.trans generalCLTConstant_ge_one))) herr

lemma dimensionLog_eq_one_add_log {p : ℕ} (hp : 1 ≤ p) :
    dimensionLog p = 1 + Real.log (p : ℝ) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hp0, Real.log_exp]

lemma normalized_fixed_envelope_log_rate_tendsto_zero
    (B : ℝ) (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (hlog : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => B / Real.sqrt n * dimensionLog (p n)) atTop (𝓝 0) := by
  have hs : Tendsto (fun n : ℕ => Real.sqrt n) atTop atTop := by
    simpa only [Real.sqrt_eq_rpow] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1/2)).comp tendsto_natCast_atTop_atTop
  have hi : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 0) := by
    simpa only [one_div] using tendsto_inv_atTop_zero.comp hs
  have hh := (hi.add hlog).const_mul B
  simp only [zero_add, mul_zero] at hh
  convert hh using 1
  ext n
  rw [dimensionLog_eq_one_add_log (hp n)]
  ring

/-- The zero-skew sufficient condition in the exact notation of the
manuscript: log p=o(sqrt n), for each fixed envelope. -/
theorem zeroSkewFixedGapUniformConsistency_of_log_rate_tendsto_zero
    {c₀ B : ℝ} (hc₀ : 0 < c₀) (p : ℕ → ℕ) (hp : ∀ n, 1 ≤ p n)
    (hlog : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0)) :
    ZeroSkewFixedGapUniformConsistency.{u} c₀ B p :=
  zeroSkewFixedGapUniformConsistency_of_rate_tendsto_zero hc₀ p hp
    (normalized_fixed_envelope_log_rate_tendsto_zero B p hp hlog)

end

end RectangleCLT.Companion
