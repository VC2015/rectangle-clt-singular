import RectangleCLTCompanion.Rates
import RectangleCLTCompanion.SubexponentialStatement
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-! Elementary rate comparisons for clipping and marginal standardization. -/

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

theorem subexponentialScale_pos {n : ℕ} {K : ℝ} (hn : 1 ≤ n) (hK : 1 ≤ K) :
    0 < subexponentialScale n K := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos (mul_pos (zero_lt_one.trans_le hK)
    (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn))) (Real.sqrt_pos.mpr hnR)

theorem logPlus_mul_le {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logPlus (x * y) ≤ logPlus x + logPlus y := by
  unfold logPlus
  rw [Real.log_mul hx.ne' hy.ne']
  apply max_le
  · exact add_nonneg (le_max_left _ _) (le_max_left _ _)
  · exact add_le_add (le_max_right _ _) (le_max_right _ _)

/-- Enlarging a positive envelope decreases the logarithmic correction. -/
theorem D_L_mul_le {a b L : ℝ} (ha : 1 ≤ a) (hb : 0 < b) (hL : 0 < L) :
    D_L (a * b) L ≤ D_L b L := by
  have hbL : 0 < b * Real.sqrt L := mul_pos hb (Real.sqrt_pos.mpr hL)
  have hden : b * Real.sqrt L ≤ (a * b) * Real.sqrt L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hbL.le]
  exact add_le_add_left
    (logPlus_mono (one_div_pos.mpr (hbL.trans_le hden))
      (one_div_le_one_div_of_le hbL hden)) 1

theorem unrestrictedRate_mul_le {a b L : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hL : 0 < L) :
    unrestrictedRate (a * b) L ≤ a * unrestrictedRate b L := by
  have h := Real.sqrt_le_sqrt (D_L_mul_le ha hb hL)
  unfold unrestrictedRate
  calc
    _ ≤ (a * b) * L ^ (3 / 2 : ℝ) * Real.sqrt (D_L b L) :=
      mul_le_mul_of_nonneg_left h (mul_nonneg
        (mul_nonneg (zero_le_one.trans ha) hb.le) (Real.rpow_nonneg hL.le _))
    _ = _ := by ring

theorem min_one_le_mul_min_one {x r a : ℝ} (ha : 1 ≤ a) (hxr : x ≤ a * r) :
    min 1 x ≤ a * min 1 r := by
  by_cases hr : r ≤ 1
  · rw [min_eq_right hr]
    exact (min_le_right _ _).trans hxr
  · rw [min_eq_left (le_of_not_ge hr)]
    simpa only [mul_one] using (min_le_left (1 : ℝ) x).trans ha

theorem min_one_unrestrictedRate_mul_le {a b L : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hL : 0 < L) :
    min 1 (unrestrictedRate (a * b) L) ≤ a * min 1 (unrestrictedRate b L) :=
  min_one_le_mul_min_one ha (unrestrictedRate_mul_le ha hb hL)

theorem base_le_unrestrictedRate {b L : ℝ} (hb : 0 ≤ b) (hL : 1 ≤ L) :
    b ≤ unrestrictedRate b L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hpow : 1 ≤ L ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_mul_sqrt hLp]
    exact one_le_mul_of_one_le_of_one_le hL (Real.one_le_sqrt.mpr hL)
  have hD : 1 ≤ Real.sqrt (D_L b L) := Real.one_le_sqrt.mpr (one_le_D_L b L)
  unfold unrestrictedRate
  exact (le_mul_of_one_le_right hb hpow).trans
    (le_mul_of_one_le_right (mul_nonneg hb (Real.rpow_nonneg hLp.le _)) hD)

theorem base_le_fixedGapSubexponentialRate {b L : ℝ}
    (hb : 0 ≤ b) (hL : 1 ≤ L) : b ≤ fixedGapSubexponentialRate b L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hpow : 1 ≤ L ^ (3 / 2 : ℝ) := by
    rw [rpow_three_halves_eq_mul_sqrt hLp]
    exact one_le_mul_of_one_le_of_one_le hL (Real.one_le_sqrt.mpr hL)
  unfold fixedGapSubexponentialRate
  apply le_mul_of_one_le_right hb
  exact hpow.trans (le_add_of_nonneg_right (mul_nonneg hLp.le (Real.sqrt_nonneg _)))

/-- A fixed upper bound on `κ` costs only a constant in the gap logarithm. -/
theorem gapLog_le_fixedGapLog {a b L κ M : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hL : 0 < L)
    (hκ : 0 < κ) (hκM : κ ≤ M) :
    gapLog L (a * b) κ ≤
      (1 + logPlus (Real.sqrt M)) * (1 + logPlus (1 / (b * L))) := by
  have hM : 0 < M := hκ.trans_le hκM
  have hbL : 0 < b * L := mul_pos hb hL
  have habL : 0 < (a * b) * L := mul_pos (mul_pos (zero_lt_one.trans_le ha) hb) hL
  have hden : b * L ≤ (a * b) * L := by
    nlinarith [mul_nonneg (sub_nonneg.mpr ha) hbL.le]
  have hratio : Real.sqrt κ / ((a * b) * L) ≤ Real.sqrt M * (1 / (b * L)) := by
    calc
      _ ≤ Real.sqrt M / ((a * b) * L) :=
        div_le_div_of_nonneg_right (Real.sqrt_le_sqrt hκM) habL.le
      _ ≤ Real.sqrt M / (b * L) :=
        div_le_div_of_nonneg_left (Real.sqrt_nonneg _) hbL hden
      _ = _ := by ring
  have hlog := (logPlus_mono
    (div_pos (Real.sqrt_pos.mpr hκ) habL) hratio).trans
    (logPlus_mul_le (Real.sqrt_pos.mpr hM) (one_div_pos.mpr hbL))
  unfold gapLog
  have hcross := mul_nonneg (logPlus_nonneg (Real.sqrt M))
    (logPlus_nonneg (1 / (b * L)))
  nlinarith

/-- Explicit constant absorption for a bounded correlation parameter. -/
theorem gapRate_le_fixedGapSubexponentialRate {a b L c M : ℝ}
    (ha : 1 ≤ a) (hb : 0 < b) (hL : 1 ≤ L)
    (hM : 1 ≤ M) (hκM : kappa L c ≤ M) :
    gapRate (a * b) L c ≤
      (a * (1 + Real.sqrt (M * (1 + logPlus (Real.sqrt M))))) *
        fixedGapSubexponentialRate b L := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hκp := kappa_pos (c := c) hLp
  let D : ℝ := 1 + logPlus (1 / (b * L))
  let Q : ℝ := M * (1 + logPlus (Real.sqrt M))
  have hD : 0 ≤ D := by dsimp [D]; linarith [logPlus_nonneg (1 / (b * L))]
  have hQ : 0 ≤ Q := mul_nonneg (zero_le_one.trans hM)
    (by linarith [logPlus_nonneg (Real.sqrt M)])
  have hlog := gapLog_le_fixedGapLog ha hb hLp hκp hκM
  have hprod : kappa L c * gapLog L (a * b) (kappa L c) ≤ Q * D := by
    have h := mul_le_mul hκM hlog (gapLog_nonneg _ _ _) (zero_le_one.trans hM)
    simpa only [Q, D, mul_assoc] using h
  have hs : Real.sqrt (kappa L c * gapLog L (a * b) (kappa L c)) ≤
      Real.sqrt Q * Real.sqrt D := by
    rw [← Real.sqrt_mul hQ]
    exact Real.sqrt_le_sqrt hprod
  have ht := mul_le_mul_of_nonneg_left hs hLp.le
  have hpow : 0 ≤ L ^ (3 / 2 : ℝ) := Real.rpow_nonneg hLp.le _
  have hcross := mul_nonneg (Real.sqrt_nonneg Q) hpow
  have hterm := mul_nonneg hLp.le (Real.sqrt_nonneg D)
  have hinner : L ^ (3 / 2 : ℝ) +
      L * Real.sqrt (kappa L c * gapLog L (a * b) (kappa L c)) ≤
      (1 + Real.sqrt Q) * (L ^ (3 / 2 : ℝ) + L * Real.sqrt D) := by
    nlinarith
  have hscaled := mul_le_mul_of_nonneg_left hinner
    (mul_nonneg (zero_le_one.trans ha) hb.le)
  unfold gapRate fixedGapSubexponentialRate
  convert hscaled using 1 <;> dsimp [Q, D] <;> ring

end
end RectangleCLT.Companion
