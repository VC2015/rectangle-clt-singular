import RectangleCLTCompanion.SplitV4.RademacherLocalComparison
import RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum
import RectangleCLTCompanion.SplitV4.Printed.LowerModerateGeneral
import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness

/-! The all-threshold power comparison printed at manuscript lines
4053–4105. The scalar input is the existing genuine generic F.1 estimate
for centered independent signs, not a separate specialized tail estimate. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The actual sign-array specialization of the fully printed F.1 route,
including its tilted proof at small thresholds. The earlier specialization
through the result-certified F.1 proof is preserved. -/
theorem familyRademacher_log_tail_printed {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1) :
    0 < familyRademacherUpperTail n x ∧
    |Real.log (familyRademacherUpperTail n x / standardNormalUpperTail x)| ≤
      moderateTailRemainderConstant * ((1 + x) / Real.sqrt n + x ^ 4 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sqrt_pos.mpr hn0
  have hb (i : Fin n) : ∀ᵐ z ∂familySignLaw n, |rademacherIncrements i z| ≤ 1 / Real.sqrt n := by
    apply ae_of_all
    intro z
    simp only [rademacherIncrements, abs_mul, abs_familySign, mul_one, abs_of_pos (div_pos zero_lt_one hsqrt)]
    exact le_rfl
  have hind : iIndepFun (rademacherIncrements (n := n)) (familySignLaw n) :=
    (familyPi_iIndepFun (fun _ : Fin n => familyBernoulli familyHalf)).comp
      (fun _ b => (1 / Real.sqrt n) * familySign b) (fun _ => measurable_of_finite _)
  have hh := moderateScalarTail_bound_printed hn (fun _ => measurable_of_finite _) hind (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ))
    hb (rademacherIncrements_integral n) (rademacherIncrements_second hn) hx hsmall
  have hsum : moderateScalarSum (rademacherIncrements (n := n)) = familyRademacherScalarSum := by
    funext z
    simp only [moderateScalarSum, rademacherIncrements, familyRademacherScalarSum, Finset.mul_sum]
  rw [hsum, rademacherIncrements_gamma] at hh
  simpa only [familyRademacherUpperTail, zero_mul, zero_div, sub_zero,
    show (1 / Real.sqrt (n : ℝ)) * (1 + x) + (1 / Real.sqrt (n : ℝ)) ^ 2 * x ^ 4 =
      (1 + x) / Real.sqrt n + x ^ 4 / n by rw [div_pow, one_pow, Real.sq_sqrt hn0.le]; ring] using hh


theorem familyRademacher_scalar_berryEsseen {n : ℕ} (hn : 1 ≤ n) (x : ℝ) :
    |familyRademacherCDF n x - standardNormalCDF x| ≤
      scalarBerryEsseenConstant / Real.sqrt n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sqrt_pos.mpr hn0
  have hb (i : Fin n) : ∀ᵐ z ∂familySignLaw n,
      |rademacherIncrements i z| ≤ 1 / Real.sqrt n := by
    apply ae_of_all
    intro z
    simp only [rademacherIncrements, abs_mul, abs_familySign, mul_one,
      abs_of_pos (div_pos zero_lt_one hsqrt)]
    exact le_rfl
  have hind : iIndepFun (rademacherIncrements (n := n)) (familySignLaw n) :=
    (familyPi_iIndepFun (fun _ : Fin n => familyBernoulli familyHalf)).comp
      (fun _ b => (1 / Real.sqrt n) * familySign b) (fun _ => measurable_of_finite _)
  have hh := moderateScalarSum_berryEsseen hn (fun _ => measurable_of_finite _) hind
    (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ)) hb
    (rademacherIncrements_integral n) (rademacherIncrements_second hn) x
  have hsum : moderateScalarSum (rademacherIncrements (n := n)) = familyRademacherScalarSum := by
    funext z
    simp only [moderateScalarSum, rademacherIncrements, familyRademacherScalarSum, Finset.mul_sum]
  rw [hsum] at hh
  change |familyRademacherUpperTail n x - standardNormalUpperTail x| ≤ _ at hh
  rw [familyRademacherCDF_eq_one_sub]
  have he : |1 - familyRademacherUpperTail n x - standardNormalCDF x| =
      |familyRademacherUpperTail n x - (1 - standardNormalCDF x)| := by
    rw [show 1 - familyRademacherUpperTail n x - standardNormalCDF x =
      -(familyRademacherUpperTail n x - (1 - standardNormalCDF x)) by ring, abs_neg]
  rw [he]
  simpa only [standardNormalUpperTail_eq_one_sub, mul_one_div] using hh

theorem probability_power_difference_with_cap {a b r : ℝ}
    (ha0 : 0 ≤ a) (hb0 : 0 ≤ b) (ha : a ≤ r) (hb : b ≤ r) (m : ℕ) :
    |a ^ m - b ^ m| ≤ (m : ℝ) * |a - b| * r ^ (m - 1) := by
  have hmax : max |a| |b| ≤ r := by
    rw [abs_of_nonneg ha0, abs_of_nonneg hb0]
    exact max_le ha hb
  have hmax0 : 0 ≤ max |a| |b| := le_max_of_le_left (abs_nonneg _)
  have hpow := pow_le_pow_left₀ hmax0 hmax (m - 1)
  exact (abs_pow_sub_pow_le a b m).trans (by
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (abs_nonneg (a - b)) (Nat.cast_nonneg m)))

theorem probability_power_difference_with_tail_comparison {m : ℕ} (hm : 2 ≤ m)
    {u v c E : ℝ} (hu0 : 0 ≤ u) (hu1 : u ≤ 1) (hv0 : 0 ≤ v) (hv1 : v ≤ 1)
    (hc : 0 ≤ c) (hcv : c * v ≤ u) (hc1 : c ≤ 1)
    (hscalar : |u - v| ≤ E * v) :
    |(1 - u) ^ m - (1 - v) ^ m| ≤
      E * ((m : ℝ) * v) * Real.exp (-(c * ((m : ℝ) * v)) / 2) := by
  have hbaseu : 1 - u ≤ Real.exp (-(c * v)) := by
    have := Real.add_one_le_exp (-(c * v))
    linarith
  have hbasev : 1 - v ≤ Real.exp (-(c * v)) := by
    have := Real.add_one_le_exp (-(c * v))
    nlinarith
  have hpow := probability_power_difference_with_cap (sub_nonneg.mpr hu1)
    (sub_nonneg.mpr hv1) hbaseu hbasev m
  rw [← Real.exp_nat_mul] at hpow
  have he : Real.exp ((↑(m - 1) : ℝ) * -(c * v)) ≤
      Real.exp (-(c * ((m : ℝ) * v)) / 2) := by
    apply Real.exp_le_exp.mpr
    rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
    have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
    nlinarith [mul_nonneg hc hv0]
  have hdiff : |(1 - u) - (1 - v)| = |u - v| := by
    rw [sub_sub_sub_cancel_left, abs_sub_comm]
  rw [hdiff] at hpow
  exact hpow.trans (by
    have hs := mul_le_mul_of_nonneg_left hscalar (Nat.cast_nonneg m : (0 : ℝ) ≤ m)
    have hEv : 0 ≤ E * v := (abs_nonneg (u - v)).trans hscalar
    have hh := mul_le_mul hs he (Real.exp_pos _).le (by positivity : 0 ≤ (m : ℝ) * (E * v))
    convert hh using 1 <;> ring)

theorem familyRademacherMaximum_damped_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1)
    (herror : rademacherRelativeTailError n x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      Real.exp 1 * rademacherRelativeTailError n x * ((m : ℝ) * standardNormalUpperTail x) *
        Real.exp (-(Real.exp (-1) * ((m : ℝ) * standardNormalUpperTail x)) / 2) := by
  have ht := familyRademacher_log_tail_printed hn hx hsmall
  have hv := standardNormalUpperTail_pos x
  have hratio := div_pos ht.1 hv
  have hlog := ht.2
  change |Real.log (familyRademacherUpperTail n x / standardNormalUpperTail x)| ≤
    rademacherRelativeTailError n x at hlog
  have hlower : Real.exp (-1) * standardNormalUpperTail x ≤ familyRademacherUpperTail n x := by
    have hh := Real.exp_le_exp.mpr ((abs_le.mp (hlog.trans herror)).1)
    rw [Real.exp_log hratio] at hh
    exact (le_div_iff₀ hv).mp hh
  have hrel := (abs_exp_sub_one_le_exp_one_mul (hlog.trans herror)).trans
    (mul_le_mul_of_nonneg_left hlog (Real.exp_pos 1).le)
  rw [Real.exp_log hratio] at hrel
  have hscalar : |familyRademacherUpperTail n x - standardNormalUpperTail x| ≤
      (Real.exp 1 * rademacherRelativeTailError n x) * standardNormalUpperTail x := by
    have he : familyRademacherUpperTail n x - standardNormalUpperTail x =
        (familyRademacherUpperTail n x / standardNormalUpperTail x - 1) * standardNormalUpperTail x := by field_simp
    rw [he, abs_mul, abs_of_pos hv]
    exact mul_le_mul_of_nonneg_right hrel hv.le
  have hu1 : familyRademacherUpperTail n x ≤ 1 := measureReal_le_one
  have hv1 : standardNormalUpperTail x ≤ 1 := measureReal_le_one
  have hh := probability_power_difference_with_tail_comparison hm ht.1.le hu1 hv.le hv1
    (Real.exp_pos (-1)).le hlower (Real.exp_le_one_iff.mpr (by norm_num : (-1 : ℝ) ≤ 0)) hscalar
  rw [familyRademacherMaximum_cdf, familyRademacherCDF_eq_one_sub, normalMaximumCDF]
  have hCDF : 1 - standardNormalUpperTail x = standardNormalCDF x := by
    rw [standardNormalUpperTail_eq_one_sub]
    ring
  simpa only [hCDF] using hh

/-- The undamped consequence used in the far-moderate region, obtained
from the newly verified printed-F.1 power route. -/
theorem familyRademacherMaximum_pointwise_error_printed {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1)
    (herror : rademacherRelativeTailError n x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      Real.exp 1 * ((m : ℝ) * standardNormalUpperTail x) * rademacherRelativeTailError n x := by
  have hw : 0 ≤ (m : ℝ) * standardNormalUpperTail x :=
    mul_nonneg (Nat.cast_nonneg m) (standardNormalUpperTail_pos x).le
  have hE : 0 ≤ rademacherRelativeTailError n x :=
    (abs_nonneg _).trans (familyRademacher_log_tail_printed hn hx hsmall).2
  have he : Real.exp (-(Real.exp (-1) * ((m : ℝ) * standardNormalUpperTail x)) / 2) ≤ 1 :=
    Real.exp_le_one_iff.mpr (div_nonpos_of_nonpos_of_nonneg
      (neg_nonpos.mpr (mul_nonneg (Real.exp_pos _).le hw)) (by norm_num))
  exact (familyRademacherMaximum_damped_error hn hm hx hsmall herror).trans (by
    have hh := mul_le_of_le_one_right
      (by positivity : 0 ≤ Real.exp 1 * rademacherRelativeTailError n x * ((m : ℝ) * standardNormalUpperTail x)) he
    convert hh using 1 <;> ring)

def rademacherCDFCap : ℝ := (1 + standardNormalCDF 1) / 2

theorem rademacherCDFCap_bounds : 0 ≤ rademacherCDFCap ∧ rademacherCDFCap < 1 := by
  have h0 := standardNormalCDF_nonneg 1
  have h1 := standardNormalCDF_lt_one 1
  unfold rademacherCDFCap
  constructor <;> linarith

theorem damped_tail_mass_le {w c : ℝ} (hw : 0 ≤ w) (hc : 0 < c) :
    w * Real.exp (-(c * w) / 2) ≤ 2 / c := by
  have h := nonneg_mul_exp_neg_le (by positivity : 0 ≤ c * w / 2)
  apply (le_div_iff₀ hc).mpr
  have he : -(c * w / 2) = -(c * w) / 2 := by ring
  rw [he] at h
  nlinarith

theorem familyRademacherMaximum_low_error {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hm : 2 ≤ m)
    (hsmall : scalarBerryEsseenConstant / Real.sqrt n ≤ 1 - rademacherCDFCap)
    {x : ℝ} (hx : x ≤ 1) :
    |(familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} - normalMaximumCDF m x| ≤
      (2 * scalarBerryEsseenConstant / (1 - rademacherCDFCap)) / Real.sqrt n := by
  have hcap0 := rademacherCDFCap_bounds.1
  have hd : 0 < 1 - rademacherCDFCap := sub_pos.mpr rademacherCDFCap_bounds.2
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have hBE1 := (abs_le.mp (familyRademacher_scalar_berryEsseen hn 1)).2
  have hA1 : familyRademacherCDF n 1 ≤ rademacherCDFCap := by
    dsimp [rademacherCDFCap] at *
    linarith
  have hax : familyRademacherCDF n x ≤ rademacherCDFCap :=
    (measureReal_mono (fun z hz => (show familyRademacherScalarSum z ≤ x from hz).trans hx)).trans hA1
  have hbx : standardNormalCDF x ≤ rademacherCDFCap := by
    have hCDF1 := standardNormalCDF_le_one 1
    have hm := strictMono_standardNormalCDF.monotone hx
    dsimp [rademacherCDFCap]
    linarith
  have hcape : rademacherCDFCap ≤ Real.exp (-(1 - rademacherCDFCap)) := by
    have := Real.add_one_le_exp (-(1 - rademacherCDFCap))
    linarith
  have hpow : rademacherCDFCap ^ (m - 1) ≤
      Real.exp (-((1 - rademacherCDFCap) * (m : ℝ)) / 2) := by
    have hh := pow_le_pow_left₀ hcap0 hcape (m - 1)
    rw [← Real.exp_nat_mul] at hh
    exact hh.trans (Real.exp_le_exp.mpr (by
      rw [Nat.cast_sub (by omega : 1 ≤ m), Nat.cast_one]
      have hm2 : (2 : ℝ) ≤ m := by exact_mod_cast hm
      nlinarith))
  have hh := probability_power_difference_with_cap
    (show 0 ≤ familyRademacherCDF n x from measureReal_nonneg)
    (standardNormalCDF_nonneg x) hax hbx m
  have hBE := familyRademacher_scalar_berryEsseen hn x
  have hB0 : 0 ≤ scalarBerryEsseenConstant / Real.sqrt n := by
    have := scalarBerryEsseenConstant_pos
    positivity
  have hpow0 : 0 ≤ rademacherCDFCap ^ (m - 1) := pow_nonneg hcap0 _
  rw [familyRademacherMaximum_cdf, normalMaximumCDF]
  calc
    _ ≤ (m : ℝ) * |familyRademacherCDF n x - standardNormalCDF x| * rademacherCDFCap ^ (m - 1) := hh
    _ ≤ (m : ℝ) * (scalarBerryEsseenConstant / Real.sqrt n) *
        Real.exp (-((1 - rademacherCDFCap) * (m : ℝ)) / 2) := by gcongr
    _ = (scalarBerryEsseenConstant / Real.sqrt n) *
        ((m : ℝ) * Real.exp (-((1 - rademacherCDFCap) * (m : ℝ)) / 2)) := by ring
    _ ≤ (scalarBerryEsseenConstant / Real.sqrt n) * (2 / (1 - rademacherCDFCap)) :=
      mul_le_mul_of_nonneg_left (damped_tail_mass_le hm0 hd) hB0
    _ = _ := by ring

end
end RectangleCLT.Companion.SplitV4.Printed
