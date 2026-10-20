import RectangleCLTCompanion.Statement
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-! Elementary algebra of the companion manuscript's exact logarithmic rates.
Only the implication between explicitly assumed CLT propositions is proved. -/

open MeasureTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

@[simp] theorem logPlus_nonneg (x : ℝ) : 0 ≤ logPlus x := le_max_left _ _

theorem logPlus_mono {x y : ℝ} (hx : 0 < x) (hxy : x ≤ y) : logPlus x ≤ logPlus y :=
  max_le_max le_rfl (Real.log_le_log hx hxy)

theorem one_le_D_L (δ L : ℝ) : 1 ≤ D_L δ L := by
  unfold D_L
  linarith [logPlus_nonneg (1 / (δ * Real.sqrt L))]

theorem D_L_nonneg (δ L : ℝ) : 0 ≤ D_L δ L := zero_le_one.trans (one_le_D_L δ L)

theorem one_le_gapLog (L δ κ : ℝ) : 1 ≤ gapLog L δ κ := by
  unfold gapLog
  linarith [logPlus_nonneg (Real.sqrt κ / (δ * L))]

theorem gapLog_nonneg (L δ κ : ℝ) : 0 ≤ gapLog L δ κ :=
  zero_le_one.trans (one_le_gapLog L δ κ)

@[simp] theorem kappa_zero (L : ℝ) : kappa L 0 = L := by simp [kappa]

theorem kappa_le (L c : ℝ) : kappa L c ≤ L := by
  unfold kappa
  split_ifs
  · exact min_le_left _ _
  · exact le_rfl

theorem kappa_nonneg {L c : ℝ} (hL : 0 ≤ L) : 0 ≤ kappa L c := by
  unfold kappa
  split_ifs with hc
  · exact le_min hL (inv_nonneg.mpr hc.le)
  · exact hL

theorem kappa_pos {L c : ℝ} (hL : 0 < L) : 0 < kappa L c := by
  unfold kappa
  split_ifs with hc
  · exact lt_min hL (inv_pos.mpr hc)
  · exact hL

theorem one_le_kappa {L c : ℝ} (hL : 1 ≤ L) (_hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    1 ≤ kappa L c := by
  unfold kappa
  split_ifs with hc
  · exact le_min hL ((one_le_inv₀ hc).mpr hc1)
  · exact hL

theorem kappa_le_inv {L c : ℝ} (hc : 0 < c) : kappa L c ≤ c⁻¹ := by
  simp only [kappa, if_pos hc]
  exact min_le_right _ _

theorem unrestrictedRate_nonneg {δ L : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    0 ≤ unrestrictedRate δ L := by
  unfold unrestrictedRate
  positivity

theorem zeroSkewRate_nonneg {δ L c : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    0 ≤ zeroSkewRate δ L c := by
  unfold zeroSkewRate
  positivity

theorem gapRate_nonneg {δ L c : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    0 ≤ gapRate δ L c := by
  unfold gapRate
  positivity

theorem gapRate_eq_cubic_add_zeroSkewRate (δ L c : ℝ) :
    gapRate δ L c = δ * L ^ (3 / 2 : ℝ) + zeroSkewRate δ L c := by
  unfold gapRate zeroSkewRate
  ring

private theorem sqrt_div_eq_one_div {δ L : ℝ} (hδ : 0 < δ) (hL : 0 < L) :
    Real.sqrt L / (δ * L) = 1 / (δ * Real.sqrt L) := by
  apply (div_eq_div_iff (mul_ne_zero hδ.ne' hL.ne')
    (mul_ne_zero hδ.ne' (Real.sqrt_pos.mpr hL).ne')).mpr
  calc
    _ = δ * (Real.sqrt L) ^ 2 := by ring
    _ = δ * L := by rw [Real.sq_sqrt hL.le]
    _ = _ := by ring

/-- The optional gap logarithm is always bounded by the unrestricted one. -/
theorem gapLog_le_D_L {δ L κ : ℝ} (hδ : 0 ≤ δ) (hL : 1 ≤ L)
    (hκ0 : 0 ≤ κ) (hκL : κ ≤ L) : gapLog L δ κ ≤ D_L δ L := by
  by_cases hδ0 : δ = 0
  · simp [hδ0, gapLog, D_L]
  · have hδp : 0 < δ := lt_of_le_of_ne hδ (Ne.symm hδ0)
    have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
    have hden : 0 < δ * L := mul_pos hδp hLp
    have hratio : Real.sqrt κ / (δ * L) ≤ 1 / (δ * Real.sqrt L) := by
      calc
        _ ≤ Real.sqrt L / (δ * L) :=
          div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hκL) hden.le
        _ = _ := sqrt_div_eq_one_div hδp hLp
    by_cases hκ : κ = 0
    · subst κ
      have heq : logPlus (Real.sqrt 0 / (δ * L)) = 0 := by norm_num [logPlus]
      unfold gapLog D_L
      rw [heq]
      linarith [logPlus_nonneg (1 / (δ * Real.sqrt L))]
    · have hleft : 0 < Real.sqrt κ / (δ * L) :=
        div_pos (Real.sqrt_pos.mpr (lt_of_le_of_ne hκ0 (Ne.symm hκ))) hden
      exact add_le_add_left (logPlus_mono hleft hratio) 1


private theorem mul_sqrt_eq_rpow_three_halves {L : ℝ} (hL : 0 < L) :
    L * Real.sqrt L = L ^ (3 / 2 : ℝ) := by
  calc
    _ = L ^ (1 : ℝ) * L ^ (1 / 2 : ℝ) := by rw [Real.rpow_one, Real.sqrt_eq_rpow]
    _ = L ^ ((1 : ℝ) + (1 / 2 : ℝ)) := (Real.rpow_add hL _ _).symm
    _ = _ := by norm_num

/-- The exact real-power normalization used by the manuscript's rates. -/
theorem rpow_three_halves_eq_mul_sqrt {L : ℝ} (hL : 0 < L) :
    L ^ (3 / 2 : ℝ) = L * Real.sqrt L :=
  (mul_sqrt_eq_rpow_three_halves hL).symm

/-- The logarithmic gap improvement is no worse than twice the unrestricted
rate. This includes the zero-gap fallback. -/
theorem gapRate_le_two_unrestrictedRate {δ L c : ℝ} (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    gapRate δ L c ≤ 2 * unrestrictedRate δ L := by
  have hL0 : 0 ≤ L := zero_le_one.trans hL
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hκ := kappa_le L c
  have hκ0 := kappa_nonneg (c := c) hL0
  have hE := gapLog_le_D_L hδ hL hκ0 hκ
  have hprod : kappa L c * gapLog L δ (kappa L c) ≤ L * D_L δ L :=
    mul_le_mul hκ hE (gapLog_nonneg _ _ _) hL0
  have hs : Real.sqrt (kappa L c * gapLog L δ (kappa L c)) ≤
      Real.sqrt L * Real.sqrt (D_L δ L) := by
    rw [← Real.sqrt_mul hL0]
    exact Real.sqrt_le_sqrt hprod
  have hsecond : L * Real.sqrt (kappa L c * gapLog L δ (kappa L c)) ≤
      L ^ (3 / 2 : ℝ) * Real.sqrt (D_L δ L) := by
    calc
      _ ≤ L * (Real.sqrt L * Real.sqrt (D_L δ L)) := mul_le_mul_of_nonneg_left hs hL0
      _ = (L * Real.sqrt L) * Real.sqrt (D_L δ L) := by ring
      _ = _ := by rw [mul_sqrt_eq_rpow_three_halves hLp]
  have hfirst : L ^ (3 / 2 : ℝ) ≤ L ^ (3 / 2 : ℝ) * Real.sqrt (D_L δ L) :=
    le_mul_of_one_le_right (Real.rpow_nonneg hL0 _) (Real.one_le_sqrt.mpr (one_le_D_L δ L))
  have hh := mul_le_mul_of_nonneg_left (add_le_add hfirst hsecond) hδ
  unfold gapRate unrestrictedRate
  convert hh using 1
  ring

/-- The zero-skew rate is the non-cubic part of the gap-sensitive rate. -/
theorem zeroSkewRate_le_gapRate {δ L c : ℝ} (hδ : 0 ≤ δ) (hL : 0 ≤ L) :
    zeroSkewRate δ L c ≤ gapRate δ L c := by
  rw [gapRate_eq_cubic_add_zeroSkewRate]
  have hc : 0 ≤ δ * L ^ (3 / 2 : ℝ) := mul_nonneg hδ (Real.rpow_nonneg hL _)
  linarith

/-- Saturating the rates by one retains the same factor two. -/
theorem min_one_gapRate_le_two_min_one_unrestrictedRate {δ L c : ℝ}
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) :
    min 1 (gapRate δ L c) ≤ 2 * min 1 (unrestrictedRate δ L) := by
  by_cases hr : unrestrictedRate δ L ≤ 1
  · rw [min_eq_right hr]
    exact (min_le_right _ _).trans (gapRate_le_two_unrestrictedRate hδ hL)
  · rw [min_eq_left (le_of_lt (lt_of_not_ge hr))]
    exact (min_le_left _ _).trans (by norm_num)

/-- Conditional implication between the two concrete CLT propositions.
The gap-sensitive CLT remains an explicit hypothesis. -/
theorem GapSensitiveCLT.toUnrestrictedCLT {C : ℝ} (hC : 0 ≤ C)
    (hgap : GapSensitiveCLT.{u} C) : UnrestrictedCLT.{u} (2 * C) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hunit hA R
  have hh := hgap μ p n hp hn ξ δ A hdata hunit hA R
  have hr := min_one_gapRate_le_two_min_one_unrestrictedRate
    (c := pairGap (covariance μ (sumVector ξ))) hdata.delta_nonneg (log_exp_mul_nat_ge_one hp)
  calc
    _ ≤ C * min 1 (gapRate δ (dimensionLog p) (pairGap (covariance μ (sumVector ξ)))) := hh
    _ ≤ C * (2 * min 1 (unrestrictedRate δ (dimensionLog p))) := mul_le_mul_of_nonneg_left hr hC
    _ = _ := by ring

/-- The conditional existential form still chooses one constant before all data. -/
theorem unrestrictedCLTExists_of_gapSensitiveCLTExists
    (hgap : GapSensitiveCLTExists.{u}) : UnrestrictedCLTExists.{u} := by
  obtain ⟨C, hC, hgap⟩ := hgap
  refine ⟨2 * C, by linarith, ?_⟩
  exact GapSensitiveCLT.toUnrestrictedCLT (zero_le_one.trans hC) hgap

end

end RectangleCLT.Companion
