import RectangleCLTCompanion.SplitV4.RademacherCalibration
import RectangleCLTCompanion.SplitV4.GaussianExtremeCalibration

/-! Relative scalar tails control the actual Rademacher maximum near its Gaussian threshold. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem abs_exp_sub_one_le_exp_one_mul {a : ℝ} (ha : |a| ≤ 1) :
    |Real.exp a - 1| ≤ Real.exp 1 * |a| := by
  have hh := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun x (_ : x ∈ Icc (-1 : ℝ) 1) => (Real.hasDerivAt_exp x).hasDerivWithinAt)
    (fun x hx => by simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using Real.exp_le_exp.mpr hx.2)
    (convex_Icc (-1 : ℝ) 1) (show (0 : ℝ) ∈ Icc (-1 : ℝ) 1 by constructor <;> norm_num) (abs_le.mp ha)
  simpa only [Real.exp_zero, sub_zero, Real.norm_eq_abs] using hh

theorem probability_power_difference {a b : ℝ} (ha0 : 0 ≤ a) (ha1 : a ≤ 1)
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (m : ℕ) : |a ^ m - b ^ m| ≤ (m : ℝ) * |a - b| := by
  have hmax : max |a| |b| ≤ 1 := by rw [abs_of_nonneg ha0, abs_of_nonneg hb0]; exact max_le ha1 hb1
  have hpow : max |a| |b| ^ (m - 1) ≤ 1 := pow_le_one₀ (le_max_of_le_left (abs_nonneg _)) hmax
  have hh := (abs_pow_sub_pow_le a b m).trans
    (mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg _) (Nat.cast_nonneg _)))
  simpa only [mul_one, mul_comm] using hh

def rademacherRelativeTailError (n : ℕ) (x : ℝ) : ℝ :=
  moderateTailRemainderConstant * ((1 + x) / Real.sqrt n + x ^ 4 / n)

theorem familyRademacherMaximum_pointwise_error {n m : ℕ} [NeZero m] (hn : 1 ≤ n)
    {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1)
    (herror : rademacherRelativeTailError n x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      Real.exp 1 * ((m : ℝ) * standardNormalUpperTail x) * rademacherRelativeTailError n x := by
  have htail := familyRademacher_log_tail hn hx hsmall
  have hp := standardNormalUpperTail_pos x
  have hratio : 0 < familyRademacherUpperTail n x / standardNormalUpperTail x := div_pos htail.1 hp
  have hlog : |Real.log (familyRademacherUpperTail n x / standardNormalUpperTail x)| ≤ rademacherRelativeTailError n x := htail.2
  have hrel := (abs_exp_sub_one_le_exp_one_mul (hlog.trans herror)).trans
    (mul_le_mul_of_nonneg_left hlog (Real.exp_pos 1).le)
  rw [Real.exp_log hratio] at hrel
  have hscalar : |familyRademacherUpperTail n x - standardNormalUpperTail x| ≤
      Real.exp 1 * rademacherRelativeTailError n x * standardNormalUpperTail x := by
    have heq : (familyRademacherUpperTail n x / standardNormalUpperTail x - 1) * standardNormalUpperTail x =
        familyRademacherUpperTail n x - standardNormalUpperTail x := by field_simp
    calc
      _ = |(familyRademacherUpperTail n x / standardNormalUpperTail x - 1) * standardNormalUpperTail x| := by rw [heq]
      _ = |familyRademacherUpperTail n x / standardNormalUpperTail x - 1| * standardNormalUpperTail x := by rw [abs_mul, abs_of_pos hp]
      _ ≤ _ := mul_le_mul_of_nonneg_right hrel hp.le
  have ha0 : 0 ≤ familyRademacherCDF n x := measureReal_nonneg
  have ha1 : familyRademacherCDF n x ≤ 1 := (measureReal_mono (subset_univ _)).trans_eq measureReal_univ_eq_one
  have hh := probability_power_difference ha0 ha1 (standardNormalCDF_nonneg x) (standardNormalCDF_le_one x) m
  have hdiff : |familyRademacherCDF n x - standardNormalCDF x| =
      |familyRademacherUpperTail n x - standardNormalUpperTail x| := by
    rw [familyRademacherCDF_eq_one_sub, standardNormalUpperTail_eq_one_sub]
    rw [← abs_neg (familyRademacherUpperTail n x - (1 - standardNormalCDF x))]
    congr 1
    ring
  rw [familyRademacherMaximum_cdf, normalMaximumCDF]
  rw [hdiff] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg m)).trans_eq (by ring))


theorem local_standardNormalPDF_bound {u t L : ℝ} (hL : 1 ≤ L) (hu0 : 0 ≤ u)
    (hu : u ≤ 2 * Real.sqrt L) (ht : |t - u| ≤ 1 / Real.sqrt L) :
    standardNormalPDF t ≤ standardNormalPDF u * Real.exp 3 ∧ |t| ≤ 3 * Real.sqrt L := by
  let s := Real.sqrt L
  have hs : 1 ≤ s := Real.one_le_sqrt.mpr hL
  have hs0 : 0 < s := by linarith
  have hts : |t - u| * s ≤ 1 := (le_div_iff₀ hs0).mp ht
  have htm : |t - u| ≤ 1 := ht.trans ((div_le_one hs0).mpr hs)
  have htm' : |t| ≤ |t - u| + u := by simpa only [sub_add_cancel, abs_of_nonneg hu0] using abs_add (t-u) u
  constructor
  · rw [standardNormalPDF_shift_bound u t]
    apply mul_le_mul_of_nonneg_left _ (standardNormalPDF_nonneg u)
    apply Real.exp_le_exp.mpr
    have hus : u * |t - u| ≤ 2 := by nlinarith only [mul_le_mul_of_nonneg_right hu (abs_nonneg (t-u)), hts]
    have hh : u ^ 2 - t ^ 2 ≤ 2 * u * |t-u| := by
      nlinarith only [sq_nonneg (t-u), mul_le_mul_of_nonneg_left (neg_abs_le (t-u)) hu0]
    nlinarith only [hus, hh]
  · dsimp only [s] at hs
    nlinarith only [htm', htm, hs, hu]

theorem eventually_normalTail_local_mass_bound : ∀ᶠ m : ℕ in atTop, ∀ x : ℝ,
    |x - normalMaxThreshold m| ≤ 1 / Real.sqrt (Real.log (m : ℝ)) →
      0 ≤ x ∧ |x| ≤ 3 * Real.sqrt (Real.log (m : ℝ)) ∧
        (m : ℝ) * standardNormalUpperTail x ≤ 8 * Real.exp 3 := by
  have hlog : Tendsto (fun m : ℕ => Real.log (m : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hlog.eventually (eventually_ge_atTop 4),
    tendsto_normalMaxThreshold_atTop.eventually (eventually_gt_atTop (0 : ℝ)),
    tendsto_normalMaxThreshold_sq_div_log.eventually (eventually_gt_nhds (by norm_num : (1 : ℝ) < 2)),
    tendsto_normalMaxThreshold_sq_div_log.eventually (eventually_lt_nhds (by norm_num : (2 : ℝ) < 4)),
    tendsto_normalMax_mills_calibration.eventually (eventually_lt_nhds (by norm_num : (1 : ℝ) < 2))]
    with m hL hu hsqlo hsqhi hpdf
  intro x hx
  let L := Real.log (m : ℝ)
  let u := normalMaxThreshold m
  let s := Real.sqrt L
  have hLp : 0 < L := by dsimp only [L]; linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = L := Real.sq_sqrt hLp.le
  have hs : 2 ≤ s := Real.le_sqrt_of_sq_le (by dsimp only [L]; norm_num at hL ⊢; exact hL)
  have hu2hi : u ^ 2 < 4 * L := (div_lt_iff₀ hLp).mp hsqhi
  have hu2lo : L < u ^ 2 := by simpa only [one_mul] using (lt_div_iff₀ hLp).mp hsqlo
  have hus : u ≤ 2 * s := by nlinarith only [hu2hi, hs2, hs0, hu]
  have hsu : s ≤ u := by nlinarith only [hu2lo, hs2, hs0, hu]
  have hshift : |x-u| ≤ 1 := hx.trans ((div_le_one (by linarith : 0 < s)).mpr (by linarith))
  have hxlo : s / 2 ≤ x := by linarith [(abs_le.mp hshift).1]
  have hxpos : 0 < x := by linarith
  obtain ⟨hpt, hxabs⟩ := local_standardNormalPDF_bound (by dsimp only [L]; linarith) hu.le hus hx
  have hmpdf : (m : ℝ) * standardNormalPDF u ≤ 4 * s := by
    have hh : (m : ℝ) * standardNormalPDF u < 2 * u := (div_lt_iff₀ hu).mp hpdf
    linarith
  have hmpdfx : (m : ℝ) * standardNormalPDF x ≤ 4 * Real.exp 3 * s := by
    have hh := mul_le_mul_of_nonneg_left hpt (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hh' := mul_le_mul_of_nonneg_right hmpdf (Real.exp_pos 3).le
    nlinarith only [hh, hh']
  have htail := (le_div_iff₀ hxpos).mp (standardNormalUpperTail_le_mills hxpos)
  have hh := mul_le_mul_of_nonneg_left htail (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
  have hsbound := mul_le_mul_of_nonneg_left hxlo (by positivity : 0 ≤ 8 * Real.exp 3)
  have hmass : (m : ℝ) * standardNormalUpperTail x ≤ 8 * Real.exp 3 := by
    apply (mul_le_mul_right hxpos).mp
    nlinarith only [hh, hmpdfx, hsbound]
  exact ⟨hxpos.le, hxabs, hmass⟩

def rademacherLocalError (n m : ℕ) : ℝ := moderateTailRemainderConstant *
  (4 * Real.sqrt (Real.log (m : ℝ)) / Real.sqrt n + 81 * Real.log (m : ℝ) ^ 2 / n)

theorem familyRademacherMaximum_local_error {n m : ℕ} [NeZero m] (hn : 1 ≤ n)
    (hL : 1 ≤ Real.log (m : ℝ)) (hmass : ∀ x : ℝ,
      |x - normalMaxThreshold m| ≤ 1 / Real.sqrt (Real.log (m : ℝ)) →
      0 ≤ x ∧ |x| ≤ 3 * Real.sqrt (Real.log (m : ℝ)) ∧ (m : ℝ) * standardNormalUpperTail x ≤ 8 * Real.exp 3)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + 3 * Real.sqrt (Real.log (m : ℝ)))) ≤ 1)
    (herror : rademacherLocalError n m ≤ 1) {x : ℝ}
    (hx : |x - normalMaxThreshold m| ≤ 1 / Real.sqrt (Real.log (m : ℝ))) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      8 * Real.exp 4 * rademacherLocalError n m := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  obtain ⟨hx0, hxabs, hmassx⟩ := hmass x hx
  have hxhi : x ≤ 3 * Real.sqrt (Real.log (m : ℝ)) := (le_abs_self x).trans hxabs
  have hs1 : 1 ≤ Real.sqrt (Real.log (m : ℝ)) := Real.one_le_sqrt.mpr hL
  have hR : rademacherRelativeTailError n x ≤ rademacherLocalError n m := by
    have hx4 : x ^ 4 ≤ 81 * Real.log (m : ℝ) ^ 2 := by
      have hh := pow_le_pow_left₀ hx0 hxhi 4
      have hs2 := Real.sq_sqrt (by linarith : 0 ≤ Real.log (m : ℝ))
      calc
        _ ≤ (3 * Real.sqrt (Real.log (m : ℝ))) ^ 4 := hh
        _ = 81 * (Real.sqrt (Real.log (m : ℝ)) ^ 2) ^ 2 := by ring
        _ = _ := by rw [hs2]
    have h1 : (1 + x) / Real.sqrt n ≤ 4 * Real.sqrt (Real.log (m : ℝ)) / Real.sqrt n :=
      div_le_div_of_nonneg_right (by linarith) (Real.sqrt_nonneg _)
    have h2 := div_le_div_of_nonneg_right hx4 hn0.le
    exact mul_le_mul_of_nonneg_left (add_le_add h1 h2) moderateTailRemainderConstant_bounds.1.le
  have hδpoint : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (add_le_add_left hxhi 1) (by positivity))
      moderateTailSmallConstant_bounds.1.le).trans hsmall
  have hh := familyRademacherMaximum_pointwise_error (m := m) hn hx0 hδpoint (hR.trans herror)
  have hR0 : 0 ≤ rademacherRelativeTailError n x := by
    unfold rademacherRelativeTailError
    have hc := moderateTailRemainderConstant_bounds.1
    positivity
  have hprod := mul_le_mul hmassx hR hR0 (by positivity : 0 ≤ 8 * Real.exp 3)
  apply hh.trans
  have hmul := mul_le_mul_of_nonneg_left hprod (Real.exp_pos 1).le
  have hexp : Real.exp 1 * (8 * Real.exp 3 * rademacherLocalError n m) = 8 * Real.exp 4 * rademacherLocalError n m := by
    rw [show (4 : ℝ) = 1 + 3 by norm_num, Real.exp_add]
    ring
  simpa only [mul_assoc] using hmul.trans_eq hexp

end
end RectangleCLT.Companion.SplitV4
