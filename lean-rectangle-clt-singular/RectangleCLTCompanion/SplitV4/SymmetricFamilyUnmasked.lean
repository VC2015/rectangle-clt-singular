import RectangleCLTCompanion.SplitV4.SymmetricFamilyAllActive
import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Quantitative activation calibration for the unmasked lower-bound family. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyUnmasked_failure_bound (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (hθ : (n : ℝ) * P.theta = Real.log (m : ℝ) / 2) (hπ : P.pi = 1)
    (hL : 0 < Real.log (m : ℝ)) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z} ≤
      2 / Real.log (m : ℝ) +
        Real.exp (-(m : ℝ) * (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m : ℝ))) := by
  let b := Nat.ceil (Real.log (m : ℝ))
  have hb : Real.log (m : ℝ) ≤ (b : ℝ) := Nat.le_ceil _
  have hk : (n : ℝ) * P.theta < b := by rw [hθ]; linarith
  have htail := familyActivationCount_upper_tail P n m hk
  rw [hθ] at htail
  have hden : 0 < (b : ℝ) - Real.log (m : ℝ) / 2 := by linarith
  have hfrac : (Real.log (m : ℝ) / 2) / ((b : ℝ) - Real.log (m : ℝ) / 2) ^ 2 ≤ 2 / Real.log (m : ℝ) := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hL).mpr
    nlinarith only [hb, hL, sq_nonneg ((b : ℝ) - Real.log (m : ℝ))]
  have hh := familyMaskedSignMaximum_all_active_bound P n m b
  rw [hπ] at hh
  exact hh.trans (add_le_add_right (htail.trans hfrac) _)

theorem familyMaskedSignMaximum_mean_ratio_error (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (hk : 1 ≤ (n : ℝ) * P.theta) :
    |(∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m) / ((n : ℝ) * P.theta) - 1| ≤
      3 * Real.sqrt ((familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z}) := by
  have hkpos : 0 < (n : ℝ) * P.theta := by linarith
  have hmean := integral_familyMaskedSignMaximum_le P n m
  have hdef := familyMaskedSignMaximum_mean_deficit P n m
  have hsqrt : Real.sqrt ((n : ℝ) * P.theta * ((n : ℝ) * P.theta + 1)) ≤ (3 / 2) * ((n : ℝ) * P.theta) := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith only [hk, sq_nonneg ((n : ℝ) * P.theta - 1)]
  have hbound := mul_le_mul_of_nonneg_right hsqrt (Real.sqrt_nonneg
    ((familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z}))
  rw [abs_of_nonpos (by exact (div_le_one hkpos).mpr hmean |> sub_nonpos.mpr)]
  rw [show -((∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m) / ((n : ℝ) * P.theta) - 1) =
      ((n : ℝ) * P.theta - (∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m)) / ((n : ℝ) * P.theta) by
    field_simp]
  apply (div_le_iff₀ hkpos).mpr
  nlinarith only [hdef, hbound]


theorem tendsto_unmasked_coverage_exponent :
    Tendsto (fun m : ℕ => (m : ℝ) * (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m : ℝ))) atTop atTop := by
  have hc : 0 < 1 - Real.log (2 : ℝ) := by
    have hh := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlow := (Real.tendsto_exp_atTop.comp (hlog.const_mul_atTop hc)).const_mul_atTop (by norm_num : (0 : ℝ) < 1 / 2)
  have hbound : ∀ᶠ m : ℕ in atTop,
      (1 / 2 : ℝ) * Real.exp ((1 - Real.log (2 : ℝ)) * Real.log (m : ℝ)) ≤
        (m : ℝ) * (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m : ℝ)) := by
    filter_upwards [eventually_ge_atTop 1] with m hm
    have hmp : (0 : ℝ) < m := by exact_mod_cast hm
    have hLm : 0 ≤ Real.log (m : ℝ) := Real.log_nonneg (by exact_mod_cast hm)
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log (2 : ℝ) := by simp
    have hhalfneg : Real.log (1 / 2 : ℝ) ≤ 0 := (Real.log_neg (by norm_num) (by norm_num)).le
    have hceil := mul_le_mul_of_nonpos_right (Nat.ceil_lt_add_one hLm).le hhalfneg
    have he := mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hceil) hmp.le
    have hpowe : Real.exp ((Nat.ceil (Real.log (m : ℝ)) : ℝ) * Real.log (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m : ℝ)) := by rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    rw [hpowe] at he
    have heq : (m : ℝ) * Real.exp ((Real.log (m : ℝ) + 1) * Real.log (1 / 2 : ℝ)) =
        (1 / 2 : ℝ) * Real.exp ((1 - Real.log (2 : ℝ)) * Real.log (m : ℝ)) := by
      rw [← Real.exp_log hmp, ← Real.exp_log (by norm_num : (0 : ℝ) < 1 / 2), ← Real.exp_add, ← Real.exp_add, hhalf]
      simp only [Real.log_exp]
      congr 1
      ring
    exact heq ▸ he
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hlow.eventually (eventually_ge_atTop b), hbound] with m hm hb
  exact hm.trans hb

theorem tendsto_unmasked_failure_envelope :
    Tendsto (fun m : ℕ => 2 / Real.log (m : ℝ) +
      Real.exp (-(m : ℝ) * (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m : ℝ)))) atTop (𝓝 0) := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have h1 : Tendsto (fun m : ℕ => 2 / Real.log (m : ℝ)) atTop (𝓝 0) := tendsto_const_nhds.div_atTop hlog
  have h2 := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp tendsto_unmasked_coverage_exponent)
  have hh := h1.add h2
  simpa only [zero_add, Function.comp_apply, neg_mul] using hh


theorem tendsto_familyUnmasked_maximum_mean_ratio (P : ℕ → SymmetricFamilyParameters) (m : ℕ → ℕ)
    [∀ n, NeZero (m n)] (hm : Tendsto m atTop atTop)
    (hθ : ∀ᶠ n : ℕ in atTop, (n : ℝ) * (P n).theta = Real.log (m n : ℝ) / 2)
    (hπ : ∀ᶠ n : ℕ in atTop, (P n).pi = 1) :
    Tendsto (fun n : ℕ => (∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw (P n) n (m n)) /
      ((n : ℝ) * (P n).theta)) atTop (𝓝 1) := by
  let bad : ℕ → ℝ := fun n => (familyRestArrayLaw (P n) n (m n)).real
    {z | familyMaskedSignMaximum z ≠ familyActivationCount z}
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hm)
  have hbadbound : ∀ᶠ n : ℕ in atTop, bad n ≤ 2 / Real.log (m n : ℝ) +
      Real.exp (-(m n : ℝ) * (1 / 2 : ℝ) ^ Nat.ceil (Real.log (m n : ℝ))) := by
    filter_upwards [hθ, hπ, hlog.eventually (eventually_gt_atTop 0)] with n hnθ hnπ hnL
    exact familyUnmasked_failure_bound (P n) n (m n) hnθ hnπ hnL
  have hbad : Tendsto bad atTop (𝓝 0) := squeeze_zero'
    (Eventually.of_forall (fun n => measureReal_nonneg)) hbadbound (tendsto_unmasked_failure_envelope.comp hm)
  have hroot := Real.continuous_sqrt.continuousAt.tendsto.comp hbad
  have hroot' : Tendsto (fun n : ℕ => 3 * Real.sqrt (bad n)) atTop (𝓝 0) := by
    simpa only [Real.sqrt_zero, mul_zero] using hroot.const_mul 3
  have herr : ∀ᶠ n : ℕ in atTop,
      |(∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw (P n) n (m n)) / ((n : ℝ) * (P n).theta) - 1| ≤
        3 * Real.sqrt (bad n) := by
    filter_upwards [hθ, hlog.eventually (eventually_ge_atTop 2)] with n hnθ hnL
    exact familyMaskedSignMaximum_mean_ratio_error (P n) n (m n) (by rw [hnθ]; linarith)
  have habs := squeeze_zero' (Eventually.of_forall (fun n => abs_nonneg _)) herr hroot'
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

end
end RectangleCLT.Companion.SplitV4
