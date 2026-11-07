import RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumTail

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def rademacherGlobalError (n m : ℕ) : ℝ :=
  Real.sqrt (dimensionLog m) / Real.sqrt n + dimensionLog m ^ 2 / n

theorem rademacherRelativeTailError_central {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m)
    {x : ℝ} (hx : 0 ≤ x) (hxc : x ≤ 2 * Real.sqrt (dimensionLog m)) :
    rademacherRelativeTailError n x ≤
      16 * moderateTailRemainderConstant * rademacherGlobalError n m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one (show 1 ≤ m by omega)
  have hL0 : 0 ≤ dimensionLog m := by linarith
  have hs := Real.one_le_sqrt.mpr hL
  have hC := moderateTailRemainderConstant_bounds.1.le
  have hx1 : 1 + x ≤ 3 * Real.sqrt (dimensionLog m) := by linarith
  have hx4 : x ^ 4 ≤ 16 * dimensionLog m ^ 2 := by
    have hh := pow_le_pow_left₀ hx hxc 4
    have he : (2 * Real.sqrt (dimensionLog m)) ^ 4 = 16 * dimensionLog m ^ 2 := by
      calc
        _ = 16 * ((Real.sqrt (dimensionLog m)) ^ 2) ^ 2 := by ring
        _ = _ := by rw [Real.sq_sqrt hL0]
    exact hh.trans_eq he
  unfold rademacherRelativeTailError
  have ha := div_le_div_of_nonneg_right hx1 (Real.sqrt_nonneg (n : ℝ))
  have hb := div_le_div_of_nonneg_right hx4 hn0.le
  have hs0 : 0 ≤ Real.sqrt (dimensionLog m) / Real.sqrt n := by positivity
  have hh : (1 + x) / Real.sqrt n + x ^ 4 / n ≤ 16 * rademacherGlobalError n m := by
    unfold rademacherGlobalError
    simp only [mul_div_assoc] at ha hb
    nlinarith only [ha, hb, hs0]
  exact (mul_le_mul_of_nonneg_left hh hC).trans_eq (by ring)

theorem polynomial_times_gaussian_le {x : ℝ} (hx : 0 ≤ x) :
    (1 + x + x ^ 4) * Real.exp (-x ^ 2 / 4) ≤ 67 := by
  have h1 : Real.exp (-x ^ 2 / 4) ≤ 1 :=
    Real.exp_le_one_iff.mpr (by nlinarith [sq_nonneg x])
  have hxexp : x * Real.exp (-x ^ 2 / 4) ≤ 2 := by
    have hh : x / 2 ≤ Real.exp (x ^ 2 / 4) := by
      have := Real.add_one_le_exp (x ^ 2 / 4)
      nlinarith [sq_nonneg (x - 1)]
    have hh' := mul_le_mul_of_nonneg_right hh (Real.exp_pos (-x ^ 2 / 4)).le
    rw [← Real.exp_add] at hh'
    rw [show x ^ 2 / 4 + -x ^ 2 / 4 = 0 by ring, Real.exp_zero] at hh'
    nlinarith
  have hx4 : x ^ 4 * Real.exp (-x ^ 2 / 4) ≤ 64 := by
    have hh := nonneg_sq_mul_exp_neg_half_le (by positivity : 0 ≤ x ^ 2 / 2)
    have he : - (x ^ 2 / 2) / 2 = -x ^ 2 / 4 := by ring
    rw [he] at hh
    nlinarith
  nlinarith

theorem rademacherRelativeTailError_gaussian_weighted {n : ℕ} (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x) :
    rademacherRelativeTailError n x * Real.exp (-x ^ 2 / 4) ≤
      67 * moderateTailRemainderConstant / Real.sqrt n := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) < n := by linarith
  have hs : Real.sqrt n ≤ (n : ℝ) := by
    have hh := Real.sq_sqrt hn0.le
    have hh0 := Real.sqrt_nonneg (n : ℝ)
    nlinarith
  have hs0 := Real.sqrt_pos.mpr hn0
  have hC := moderateTailRemainderConstant_bounds.1.le
  have hx4 : x ^ 4 / n ≤ x ^ 4 / Real.sqrt n :=
    div_le_div_of_nonneg_left (pow_nonneg hx _) hs0 hs
  have hh := polynomial_times_gaussian_le hx
  unfold rademacherRelativeTailError
  calc
    _ ≤ moderateTailRemainderConstant *
        ((1 + x) / Real.sqrt n + x ^ 4 / Real.sqrt n) * Real.exp (-x ^ 2 / 4) := by gcongr
    _ = (moderateTailRemainderConstant / Real.sqrt n) *
        ((1 + x + x ^ 4) * Real.exp (-x ^ 2 / 4)) := by ring
    _ ≤ (moderateTailRemainderConstant / Real.sqrt n) * 67 :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ = _ := by ring

theorem normal_tail_mass_far_positive {m : ℕ} (hm : 2 ≤ m)
    {x : ℝ} (hx : 0 ≤ x) (hxc : 2 * Real.sqrt (dimensionLog m) ≤ x) :
    (m : ℝ) * standardNormalUpperTail x ≤ Real.exp (-x ^ 2 / 4) := by
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one (show 1 ≤ m by omega)
  have hL0 : 0 ≤ dimensionLog m := by linarith
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hxsq : 4 * dimensionLog m ≤ x ^ 2 := by
    nlinarith [Real.sq_sqrt hL0,
      pow_le_pow_left₀ (by positivity : 0 ≤ 2 * Real.sqrt (dimensionLog m)) hxc 2]
  have heL : dimensionLog m = 1 + Real.log (m : ℝ) := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
  rw [heL] at hxsq
  calc
    _ ≤ (m : ℝ) * Real.exp (-x ^ 2 / 2) :=
      mul_le_mul_of_nonneg_left (standardNormalUpperTail_subgaussian hx) hm0.le
    _ = Real.exp (Real.log (m : ℝ) - x ^ 2 / 2) := by
      rw [Real.exp_sub, Real.exp_log hm0, show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring, Real.exp_neg]
      rfl
    _ ≤ _ := Real.exp_le_exp.mpr (by linarith)

theorem familyRademacherMaximum_moderate_far_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x)
    (hxc : 2 * Real.sqrt (dimensionLog m) ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1)
    (herror : rademacherRelativeTailError n x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      67 * Real.exp 1 * moderateTailRemainderConstant / Real.sqrt n := by
  have hC := moderateTailRemainderConstant_bounds.1.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hE : 0 ≤ rademacherRelativeTailError n x := by
    unfold rademacherRelativeTailError
    positivity
  calc
    _ ≤ Real.exp 1 * ((m : ℝ) * standardNormalUpperTail x) * rademacherRelativeTailError n x :=
      familyRademacherMaximum_pointwise_error_printed hn hm hx hsmall herror
    _ ≤ Real.exp 1 * Real.exp (-x ^ 2 / 4) * rademacherRelativeTailError n x := by
      gcongr
      exact normal_tail_mass_far_positive hm hx hxc
    _ = Real.exp 1 * (rademacherRelativeTailError n x * Real.exp (-x ^ 2 / 4)) := by ring
    _ ≤ Real.exp 1 * (67 * moderateTailRemainderConstant / Real.sqrt n) :=
      mul_le_mul_of_nonneg_left (rademacherRelativeTailError_gaussian_weighted hn hx) (Real.exp_pos _).le
    _ = _ := by ring

theorem familyRademacherMaximum_central_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x)
    (hxc : x ≤ 2 * Real.sqrt (dimensionLog m))
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1)
    (herror : rademacherRelativeTailError n x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      (32 * Real.exp 1 * moderateTailRemainderConstant / Real.exp (-1)) * rademacherGlobalError n m := by
  have hE : 0 ≤ rademacherRelativeTailError n x :=
    (abs_nonneg _).trans (familyRademacher_log_tail_printed hn hx hsmall).2
  have hw : 0 ≤ (m : ℝ) * standardNormalUpperTail x :=
    mul_nonneg (Nat.cast_nonneg m) (standardNormalUpperTail_pos x).le
  have hh := familyRademacherMaximum_damped_error hn hm hx hsmall herror
  calc
    _ ≤ Real.exp 1 * rademacherRelativeTailError n x *
        (((m : ℝ) * standardNormalUpperTail x) *
          Real.exp (-(Real.exp (-1) * ((m : ℝ) * standardNormalUpperTail x)) / 2)) := by
      convert hh using 1 <;> ring
    _ ≤ Real.exp 1 * rademacherRelativeTailError n x * (2 / Real.exp (-1)) :=
      mul_le_mul_of_nonneg_left (damped_tail_mass_le hw (Real.exp_pos _)) (by positivity)
    _ ≤ Real.exp 1 * (16 * moderateTailRemainderConstant * rademacherGlobalError n m) *
        (2 / Real.exp (-1)) := by
      gcongr
      exact rademacherRelativeTailError_central hn hm hx hxc
    _ = _ := by ring

theorem familyRademacherMaximum_above_cutoff_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) {a x : ℝ} (ha : 0 < a)
    (hx : a * Real.sqrt (Real.sqrt n) ≤ x)
    (hL : dimensionLog m ≤ a ^ 2 * Real.sqrt n / 4) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      (8 / a ^ 2) / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  have hm0 : (0 : ℝ) < m := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne m))
  have hx0 : 0 ≤ x := (mul_nonneg ha.le (Real.sqrt_nonneg _)).trans hx
  have hxsq : a ^ 2 * Real.sqrt n ≤ x ^ 2 := by
    have hh := pow_le_pow_left₀ (mul_nonneg ha.le (Real.sqrt_nonneg _)) hx 2
    rw [mul_pow, Real.sq_sqrt hs.le] at hh
    exact hh
  have heL : dimensionLog m = 1 + Real.log (m : ℝ) := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hm0.ne', Real.log_exp]
  have htail : (m : ℝ) * Real.exp (-x ^ 2 / 2) ≤ Real.exp (-(a ^ 2 * Real.sqrt n) / 4) := by
    calc
      _ = Real.exp (Real.log (m : ℝ) - x ^ 2 / 2) := by
        rw [Real.exp_sub, Real.exp_log hm0, show -x ^ 2 / 2 = -(x ^ 2 / 2) by ring, Real.exp_neg]
        rfl
      _ ≤ _ := Real.exp_le_exp.mpr (by rw [heL] at hL; nlinarith)
  have hdamp := damped_tail_mass_le hs.le (by positivity : 0 < a ^ 2 / 2)
  have hdamp' : Real.exp (-(a ^ 2 * Real.sqrt n) / 4) ≤
      (4 / a ^ 2) / Real.sqrt n := by
    have he : -((a ^ 2 / 2) * Real.sqrt n) / 2 = -(a ^ 2 * Real.sqrt n) / 4 := by ring
    rw [he] at hdamp
    apply (le_div_iff₀ hs).mpr
    convert hdamp using 1 <;> ring
  exact (familyRademacherMaximum_outer_error hn hx0).trans (by
    have hh := (mul_le_mul_of_nonneg_left htail (by norm_num : (0 : ℝ) ≤ 2)).trans
      (mul_le_mul_of_nonneg_left hdamp' (by norm_num : (0 : ℝ) ≤ 2))
    convert hh using 1 <;> ring)

def rademacherCutoffAmplitude : ℝ := 1 / (2 * (moderateTailRemainderConstant + 1))

theorem rademacherCutoffAmplitude_bounds :
    0 < rademacherCutoffAmplitude ∧ rademacherCutoffAmplitude ≤ 1 ∧
      moderateTailRemainderConstant * rademacherCutoffAmplitude ^ 4 < 1 := by
  have hR := moderateTailRemainderConstant_bounds.1
  have hden : 0 < 2 * (moderateTailRemainderConstant + 1) := by positivity
  have ha : 0 < rademacherCutoffAmplitude := by unfold rademacherCutoffAmplitude; positivity
  have ha1 : rademacherCutoffAmplitude ≤ 1 := by
    unfold rademacherCutoffAmplitude
    exact (div_le_one hden).mpr (by linarith)
  have hra : moderateTailRemainderConstant * rademacherCutoffAmplitude < 1 := by
    unfold rademacherCutoffAmplitude
    rw [mul_one_div]
    apply (div_lt_iff₀ hden).mpr
    linarith
  refine ⟨ha, ha1, lt_of_le_of_lt ?_ hra⟩
  have hp : rademacherCutoffAmplitude ^ 4 ≤ rademacherCutoffAmplitude := by
    have hh := pow_le_pow_of_le_one ha.le ha1 (by decide : 1 ≤ 4)
    simpa only [pow_one] using hh
  exact mul_le_mul_of_nonneg_left hp hR.le

def rademacherGlobalSmallConstant : ℝ := rademacherCutoffAmplitude ^ 2 / 4

def rademacherGlobalConstant : ℝ :=
  2 * scalarBerryEsseenConstant / (1 - rademacherCDFCap) +
  32 * Real.exp 1 * moderateTailRemainderConstant / Real.exp (-1) +
  67 * Real.exp 1 * moderateTailRemainderConstant + 8 / rademacherCutoffAmplitude ^ 2

theorem rademacherGlobalConstant_pos : 0 < rademacherGlobalConstant := by
  have := scalarBerryEsseenConstant_pos
  have := moderateTailRemainderConstant_bounds.1
  have := sub_pos.mpr rademacherCDFCap_bounds.2
  have := rademacherCutoffAmplitude_bounds.1
  unfold rademacherGlobalConstant
  positivity

theorem rademacherRelativeTailError_mono {n : ℕ} (hn : 1 ≤ n)
    {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) :
    rademacherRelativeTailError n x ≤ rademacherRelativeTailError n y := by
  have hR := moderateTailRemainderConstant_bounds.1.le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rademacherRelativeTailError
  gcongr

theorem rademacherGlobalError_ge_inverse_sqrt {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    1 / Real.sqrt n ≤ rademacherGlobalError n m := by
  have hL : 1 ≤ dimensionLog m := log_exp_mul_nat_ge_one (by omega)
  have hs := Real.one_le_sqrt.mpr hL
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rademacherGlobalError
  exact (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _)).trans (le_add_of_nonneg_right (by positivity))

/-- Quantitative all-threshold comparison, after the three explicit
numeric large-`n` conditions have been discharged. No distributional
approximation or remainder estimate is assumed as a premise. -/
theorem familyRademacherMaximum_global_error_of_cutoff_conditions {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hBE : scalarBerryEsseenConstant / Real.sqrt n ≤ 1 - rademacherCDFCap)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) *
      (1 + rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n))) ≤ 1)
    (herror : rademacherRelativeTailError n
      (rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n)) ≤ 1)
    (hL : dimensionLog m ≤ rademacherGlobalSmallConstant * Real.sqrt n) (x : ℝ) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      rademacherGlobalConstant * rademacherGlobalError n m := by
  have hR := moderateTailRemainderConstant_bounds.1.le
  have hB := scalarBerryEsseenConstant_pos.le
  have hd := sub_pos.mpr rademacherCDFCap_bounds.2
  have ha := rademacherCutoffAmplitude_bounds.1
  have hG := rademacherGlobalError_ge_inverse_sqrt hn hm
  have hG0 : 0 ≤ rademacherGlobalError n m := by
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ)).trans hG
  have hp1 : 0 ≤ 2 * scalarBerryEsseenConstant / (1 - rademacherCDFCap) := by positivity
  have hp2 : 0 ≤ 32 * Real.exp 1 * moderateTailRemainderConstant / Real.exp (-1) := by positivity
  have hp3 : 0 ≤ 67 * Real.exp 1 * moderateTailRemainderConstant := by positivity
  have hp4 : 0 ≤ 8 / rademacherCutoffAmplitude ^ 2 := by positivity
  have hscale (K : ℝ) (hK : 0 ≤ K) : K / Real.sqrt n ≤ K * rademacherGlobalError n m := by
    simpa only [mul_one_div] using mul_le_mul_of_nonneg_left hG hK
  have hKlow : 2 * scalarBerryEsseenConstant / (1 - rademacherCDFCap) ≤ rademacherGlobalConstant := by
    unfold rademacherGlobalConstant
    linarith
  have hKcentral : 32 * Real.exp 1 * moderateTailRemainderConstant / Real.exp (-1) ≤ rademacherGlobalConstant := by
    unfold rademacherGlobalConstant
    linarith
  have hKfar : 67 * Real.exp 1 * moderateTailRemainderConstant ≤ rademacherGlobalConstant := by
    unfold rademacherGlobalConstant
    linarith
  have hKouter : 8 / rademacherCutoffAmplitude ^ 2 ≤ rademacherGlobalConstant := by
    unfold rademacherGlobalConstant
    linarith
  by_cases hx1 : x ≤ 1
  · exact (familyRademacherMaximum_low_error hn hm hBE hx1).trans
      ((hscale _ hp1).trans
        (mul_le_mul_of_nonneg_right hKlow hG0))
  have hx0 : 0 ≤ x := by linarith
  by_cases hxA : x ≤ rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n)
  · have hs : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1 := by
      have hS := moderateTailSmallConstant_bounds.1.le
      exact (by gcongr : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤
        moderateTailSmallConstant * ((1 / Real.sqrt n) *
          (1 + rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n)))).trans hsmall
    have he := (rademacherRelativeTailError_mono hn hx0 hxA).trans herror
    by_cases hxc : x ≤ 2 * Real.sqrt (dimensionLog m)
    · exact (familyRademacherMaximum_central_error hn hm hx0 hxc hs he).trans
        (mul_le_mul_of_nonneg_right hKcentral hG0)
    · exact (familyRademacherMaximum_moderate_far_error hn hm hx0 (le_of_not_ge hxc) hs he).trans
        ((hscale _ hp3).trans
          (mul_le_mul_of_nonneg_right hKfar hG0))
  · exact (familyRademacherMaximum_above_cutoff_error hn ha (le_of_not_ge hxA)
      (by simpa only [rademacherGlobalSmallConstant, div_mul_eq_mul_div] using hL)).trans
      ((hscale _ hp4).trans
        (mul_le_mul_of_nonneg_right hKouter hG0))

theorem rademacherGlobalSmallConstant_pos : 0 < rademacherGlobalSmallConstant := by
  have := rademacherCutoffAmplitude_bounds.1
  unfold rademacherGlobalSmallConstant
  positivity

theorem tendsto_sqrt_atTop_of_tendsto {f : ℕ → ℝ} (hf : Tendsto f atTop atTop) :
    Tendsto (fun n => Real.sqrt (f n)) atTop atTop := by
  apply tendsto_atTop.mpr
  intro b
  filter_upwards [hf.eventually (eventually_ge_atTop ((max b 0) ^ 2))] with n hn
  exact (le_max_left b 0).trans (Real.le_sqrt_of_sq_le hn)

theorem cutoff_fraction_identity {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (1 / Real.sqrt n) * (1 + a * Real.sqrt (Real.sqrt n)) =
      1 / Real.sqrt n + a / Real.sqrt (Real.sqrt n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  have hs2 := Real.sq_sqrt hs.le
  have hs4 := Real.sqrt_pos.mpr hs
  field_simp
  linear_combination a * Real.sqrt n * hs2

theorem cutoff_fourth_ratio_identity {n : ℕ} (hn : 1 ≤ n) (a : ℝ) :
    (a * Real.sqrt (Real.sqrt n)) ^ 4 / n = a ^ 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hs := Real.sqrt_pos.mpr hn0
  have he : (a * Real.sqrt (Real.sqrt n)) ^ 4 = a ^ 4 * n := by
    calc
      _ = a ^ 4 * (Real.sqrt (Real.sqrt n) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hs.le, Real.sq_sqrt hn0.le]
  rw [he]
  field_simp

/-- The cutoff hypotheses above are actual consequences of sufficiently
large `n`, uniformly in `m`. The fourth-order remainder tends to the
strictly subunit constant chosen by the absolute cutoff amplitude. -/
theorem eventually_rademacher_cutoff_conditions : ∀ᶠ n : ℕ in atTop,
    1 ≤ n ∧
    scalarBerryEsseenConstant / Real.sqrt n ≤ 1 - rademacherCDFCap ∧
    moderateTailSmallConstant * ((1 / Real.sqrt n) *
      (1 + rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n))) ≤ 1 ∧
    rademacherRelativeTailError n
      (rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n)) ≤ 1 := by
  have hs := tendsto_sqrt_atTop_of_tendsto tendsto_natCast_atTop_atTop
  have hq := tendsto_sqrt_atTop_of_tendsto hs
  have hi : Tendsto (fun n : ℕ => 1 / Real.sqrt n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hs
  have hiq : Tendsto (fun n : ℕ => rademacherCutoffAmplitude / Real.sqrt (Real.sqrt n)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hq
  have hfrac : Tendsto (fun n : ℕ => (1 / Real.sqrt n) *
      (1 + rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n))) atTop (𝓝 (0 : ℝ)) := by
    have hh := hi.add hiq
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact (cutoff_fraction_identity hn _).symm
  have hsmall := hfrac.const_mul moderateTailSmallConstant
  simp only [mul_zero] at hsmall
  have hBE : Tendsto (fun n : ℕ => scalarBerryEsseenConstant / Real.sqrt n) atTop (𝓝 (0 : ℝ)) :=
    tendsto_const_nhds.div_atTop hs
  have hE : Tendsto (fun n : ℕ => rademacherRelativeTailError n
      (rademacherCutoffAmplitude * Real.sqrt (Real.sqrt n))) atTop
      (𝓝 (moderateTailRemainderConstant * rademacherCutoffAmplitude ^ 4)) := by
    have hh := (hfrac.add (tendsto_const_nhds (x := rademacherCutoffAmplitude ^ 4))).const_mul
      moderateTailRemainderConstant
    simp only [zero_add] at hh
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    unfold rademacherRelativeTailError
    rw [cutoff_fourth_ratio_identity hn]
    ring
  filter_upwards [eventually_ge_atTop 1,
    hBE.eventually (eventually_lt_nhds (sub_pos.mpr rademacherCDFCap_bounds.2)),
    hsmall.eventually (eventually_lt_nhds (by norm_num : (0 : ℝ) < 1)),
    hE.eventually (eventually_lt_nhds rademacherCutoffAmplitude_bounds.2.2)] with n hn hb hs he
  exact ⟨hn, hb.le, hs.le, he.le⟩

/-- The exact uniform global Rademacher-maximum approximation printed as
`sym:eq:rademacher-max`: absolute constants, every threshold, and the
manuscript range `log(em) ≤ a₁ sqrt(n)` for all sufficiently large `n`. -/
theorem eventually_familyRademacherMaximum_global_error :
    ∀ᶠ n : ℕ in atTop, ∀ m : ℕ, (hm : 2 ≤ m) →
      letI : NeZero m := ⟨by omega⟩
      dimensionLog m ≤ rademacherGlobalSmallConstant * Real.sqrt n →
      ∀ x : ℝ, |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
        rademacherGlobalConstant * rademacherGlobalError n m := by
  filter_upwards [eventually_rademacher_cutoff_conditions] with n hn
  intro m hm
  letI : NeZero m := ⟨by omega⟩
  intro hL x
  exact familyRademacherMaximum_global_error_of_cutoff_conditions hn.1 hm hn.2.1 hn.2.2.1 hn.2.2.2 hL x

end
end RectangleCLT.Companion.SplitV4.Printed
