import RectangleCLTCompanion.LowerSkewScales
import RectangleCLTCompanion.ConsistencyUpper
import Mathlib.Analysis.SpecificLimits.Basic

/-! Critical dimensions selected by the normalized envelope. The floor,
logarithm, and real-power limits below preserve the arbitrary-envelope
quantifiers of the fixed-gap consistency theorem. -/

open Filter Set
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def lowerCriticalExponent (a δ : ℝ) : ℝ := a * (δ⁻¹) ^ (2 / 3 : ℝ)

def lowerCriticalDimension (a δ : ℝ) : ℕ :=
  Nat.floor (Real.exp (lowerCriticalExponent a δ))

theorem lowerCriticalExponent_pos {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    0 < lowerCriticalExponent a δ :=
  mul_pos ha (Real.rpow_pos_of_pos (inv_pos.mpr hδ) _)

theorem lowerCriticalExponent_power_balance {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ) :
    δ * (lowerCriticalExponent a δ) ^ (3 / 2 : ℝ) = a ^ (3 / 2 : ℝ) := by
  rw [lowerCriticalExponent, Real.mul_rpow ha.le
    (Real.rpow_nonneg (inv_nonneg.mpr hδ.le) _),
    ← Real.rpow_mul (inv_nonneg.mpr hδ.le)]
  norm_num
  field_simp

theorem lowerCriticalExponent_tendsto_atTop {a : ℝ} (ha : 0 < a)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < δ n) :
    Tendsto (fun n => lowerCriticalExponent a (δ n)) atTop atTop := by
  have hinv := (tendsto_nhdsWithin_iff.mpr ⟨hδ, hpos⟩).inv_tendsto_nhdsGT_zero
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hinv
  simpa only [lowerCriticalExponent, mul_comm] using hpow.atTop_mul_const ha

theorem lowerCriticalDimension_tendsto_atTop {a : ℝ} (ha : 0 < a)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < δ n) :
    Tendsto (fun n => lowerCriticalDimension a (δ n)) atTop atTop :=
  tendsto_nat_floor_atTop.comp (Real.tendsto_exp_atTop.comp
    (lowerCriticalExponent_tendsto_atTop ha hδ hpos))

theorem lowerCriticalDimension_log_ratio {a : ℝ} (ha : 0 < a)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < δ n) :
    Tendsto (fun n => Real.log (lowerCriticalDimension a (δ n) : ℝ) /
      lowerCriticalExponent a (δ n)) atTop (𝓝 1) := by
  have hT := lowerCriticalExponent_tendsto_atTop ha hδ hpos
  have hExp := Real.tendsto_exp_atTop.comp hT
  have hfloor := tendsto_nat_floor_div_atTop.comp hExp
  have hlog := (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hfloor
  simp only [Real.log_one] at hlog
  have hh := (hlog.div_atTop hT).add_const 1
  simp only [zero_add] at hh
  apply hh.congr'
  filter_upwards [hpos, (lowerCriticalDimension_tendsto_atTop ha hδ hpos).eventually
    (eventually_ge_atTop 1)] with n hn hq
  have hqpos : (0 : ℝ) < lowerCriticalDimension a (δ n) := by exact_mod_cast hq
  have hTpos := lowerCriticalExponent_pos ha hn
  change Real.log ((lowerCriticalDimension a (δ n) : ℝ) /
    Real.exp (lowerCriticalExponent a (δ n))) / lowerCriticalExponent a (δ n) + 1 = _
  rw [Real.log_div hqpos.ne' (Real.exp_ne_zero _), Real.log_exp]
  field_simp [hTpos.ne'] <;> ring

theorem lowerCriticalDimension_rate_tendsto {a : ℝ} (ha : 0 < a)
    {δ : ℕ → ℝ} (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < δ n) :
    Tendsto (fun n => δ n * (Real.log (lowerCriticalDimension a (δ n) : ℝ)) ^ (3 / 2 : ℝ))
      atTop (𝓝 (a ^ (3 / 2 : ℝ))) := by
  have hh := ((lowerCriticalDimension_log_ratio ha hδ hpos).rpow_const
    (Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))).const_mul (a ^ (3 / 2 : ℝ))
  simp only [Real.one_rpow, mul_one] at hh
  apply hh.congr'
  filter_upwards [hpos, (lowerCriticalDimension_tendsto_atTop ha hδ hpos).eventually
    (eventually_ge_atTop 1)] with n hn hq
  have hql : 0 ≤ Real.log (lowerCriticalDimension a (δ n) : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hq)
  have hT := lowerCriticalExponent_pos ha hn
  rw [Real.div_rpow hql hT.le, ← lowerCriticalExponent_power_balance ha hn]
  field_simp [(Real.rpow_pos_of_pos hT (3 / 2 : ℝ)).ne']
  ring

theorem lowerCriticalDimension_log_bound {a δ : ℝ} {p : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hcap : p ≤ lowerCriticalDimension a δ) :
    Real.log (p : ℝ) ≤ lowerCriticalExponent a δ := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hfloor := Nat.floor_le (Real.exp_pos (lowerCriticalExponent a δ)).le
  have hpq : (p : ℝ) ≤ lowerCriticalDimension a δ := by exact_mod_cast hcap
  have hh := Real.log_le_log hpR (hpq.trans hfloor)
  simpa only [Real.log_exp] using hh

theorem lowerCriticalDimension_rate_bound {a δ : ℝ} {p : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hcap : p ≤ lowerCriticalDimension a δ) :
    δ * (Real.log (p : ℝ)) ^ (3 / 2 : ℝ) ≤ a ^ (3 / 2 : ℝ) := by
  have hl : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  exact (mul_le_mul_of_nonneg_left
    (Real.rpow_le_rpow hl (lowerCriticalDimension_log_bound ha hδ hp hcap)
      (by norm_num : (0 : ℝ) ≤ 3 / 2)) hδ.le).trans_eq
        (lowerCriticalExponent_power_balance ha hδ)

theorem lowerCriticalDimension_root_rate_bound {a δ : ℝ} {p : ℕ}
    (ha : 0 < a) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hcap : p ≤ lowerCriticalDimension a δ) :
    δ ^ (2 / 3 : ℝ) * dimensionLog p ≤ δ ^ (2 / 3 : ℝ) + a := by
  have hinv : δ ^ (2 / 3 : ℝ) * (δ⁻¹) ^ (2 / 3 : ℝ) = 1 := by
    rw [← Real.mul_rpow hδ.le (inv_nonneg.mpr hδ.le), mul_inv_cancel₀ hδ.ne']
    norm_num
  have hlog := mul_le_mul_of_nonneg_left
    (lowerCriticalDimension_log_bound ha hδ hp hcap) (Real.rpow_nonneg hδ.le (2 / 3 : ℝ))
  rw [dimensionLog_eq_one_add_log hp]
  unfold lowerCriticalExponent at hlog
  calc
    _ = δ ^ (2 / 3 : ℝ) + δ ^ (2 / 3 : ℝ) * Real.log (p : ℝ) := by ring
    _ ≤ δ ^ (2 / 3 : ℝ) + δ ^ (2 / 3 : ℝ) * (a * (δ⁻¹) ^ (2 / 3 : ℝ)) :=
      add_le_add_left hlog _
    _ = δ ^ (2 / 3 : ℝ) + a * (δ ^ (2 / 3 : ℝ) * (δ⁻¹) ^ (2 / 3 : ℝ)) := by ring
    _ = _ := by rw [hinv, mul_one]

/-- Eventual domination by every positive critical dimension forces the
exact `δ*log(ep)^(3/2)` criterion to vanish, with arbitrary positive
dimension sequences and arbitrary eventually positive envelopes. -/
theorem lowerCriticalDimension_caps_imply_rate_tendsto_zero
    {δ : ℕ → ℝ} {p : ℕ → ℕ} (hp : ∀ n, 1 ≤ p n)
    (hδ : Tendsto δ atTop (𝓝 0)) (hpos : ∀ᶠ n in atTop, 0 < δ n)
    (hcap : ∀ a : ℝ, 0 < a → ∀ᶠ n in atTop, p n ≤ lowerCriticalDimension a (δ n)) :
    Tendsto (fun n => δ n * dimensionLog (p n) ^ (3 / 2 : ℝ)) atTop (𝓝 0) := by
  have hroot : Tendsto (fun n => (δ n) ^ (2 / 3 : ℝ)) atTop (𝓝 0) := by
    simpa only [Real.zero_rpow (by norm_num : (2 / 3 : ℝ) ≠ 0)] using
      hδ.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 2 / 3))
  have ht : Tendsto (fun n => (δ n) ^ (2 / 3 : ℝ) * dimensionLog (p n)) atTop (𝓝 0) := by
    apply tendsto_order.mpr
    constructor
    · intro b hb
      filter_upwards [hpos] with n hn
      have hnon : 0 ≤ (δ n) ^ (2 / 3 : ℝ) * dimensionLog (p n) :=
        mul_nonneg (Real.rpow_nonneg hn.le _) (zero_le_one.trans (log_exp_mul_nat_ge_one (hp n)))
      exact hb.trans_le hnon
    · intro ε hε
      filter_upwards [hpos, hcap (ε / 2) (half_pos hε),
        hroot.eventually (eventually_lt_nhds (half_pos hε))] with n hn hpn hsmall
      have hb := lowerCriticalDimension_root_rate_bound (half_pos hε) hn (hp n) hpn
      linarith only [hb, hsmall]
  have hh := ht.rpow_const (Or.inr (by norm_num : (0 : ℝ) ≤ 3 / 2))
  simp only [Real.zero_rpow (by norm_num : (3 / 2 : ℝ) ≠ 0)] at hh
  apply hh.congr'
  filter_upwards [hpos] with n hn
  rw [Real.mul_rpow (Real.rpow_nonneg hn.le (2 / 3 : ℝ))
    (show 0 ≤ dimensionLog (p n) from zero_le_one.trans (log_exp_mul_nat_ge_one (hp n))),
    ← Real.rpow_mul hn.le]
  norm_num

end

end RectangleCLT.Companion
