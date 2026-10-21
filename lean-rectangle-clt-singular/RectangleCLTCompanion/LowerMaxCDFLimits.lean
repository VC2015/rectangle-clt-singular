import RectangleCLTCompanion.NormalQuantileRate
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! Elementary extraction of maximum-CDF asymptotics from genuine
coordinate probabilities. The scalar tail estimates themselves are proved
separately from the actual tilted lower construction. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace RectangleCLT.Companion
noncomputable section

theorem normalUpperTail_tendsto_zero : Tendsto standardNormalUpperTail atTop (𝓝 0) := by
  have hh := (tendsto_const_nhds (x := (1:ℝ))).sub tendsto_standardNormalCDF_atTop
  simpa only [← standardNormalUpperTail_eq_one_sub, sub_self] using hh

private def logOneSubSlope : ℝ → ℝ :=
  Function.update (fun x : ℝ => Real.log (1-x)/x) 0 (-1)

private def expZeroSlope : ℝ → ℝ :=
  Function.update (fun x : ℝ => (Real.exp x-1)/x) 0 1

private theorem logOneSubSlope_continuousAt : ContinuousAt logOneSubSlope 0 := by
  have hd : HasDerivAt (fun x : ℝ => Real.log (1-x)) (-1) 0 := by
    convert (((hasDerivAt_const (0:ℝ) 1).sub (hasDerivAt_id 0)).log (by norm_num)) using 1 <;> norm_num
  simpa only [logOneSubSlope, Real.log_one, sub_zero] using hd.continuousAt_div

private theorem expZeroSlope_continuousAt : ContinuousAt expZeroSlope 0 := by
  simpa only [expZeroSlope, Real.exp_zero, sub_zero] using (Real.hasDerivAt_exp 0).continuousAt_div

private theorem log_one_sub_eq_mul_slope (x : ℝ) :
    Real.log (1-x)=x*logOneSubSlope x := by
  by_cases hx : x=0
  · subst x; simp [logOneSubSlope]
  · simp only [logOneSubSlope, Function.update_of_ne hx]
    field_simp

private theorem exp_sub_one_eq_mul_slope (x : ℝ) :
    Real.exp x-1=x*expZeroSlope x := by
  by_cases hx : x=0
  · subst x; simp [expZeroSlope]
  · simp only [expZeroSlope, Function.update_of_ne hx]
    field_simp

/-- The Poisson maximum limit for scalar coordinate exceedance
probabilities. Both hypotheses are ordinary scalar convergence statements. -/
theorem tendsto_one_sub_pow_of_tail
    {p : ℕ → ℕ} {q : ℕ → ℝ} {lam : ℝ}
    (hq : Tendsto q atTop (𝓝 0))
    (hpq : Tendsto (fun n => (p n : ℝ)*q n) atTop (𝓝 lam)) :
    Tendsto (fun n => (1-q n)^(p n)) atTop (𝓝 (Real.exp (-lam))) := by
  have hsl : Tendsto (fun n => logOneSubSlope (q n)) atTop (𝓝 (-1:ℝ)) := by
    simpa [logOneSubSlope] using logOneSubSlope_continuousAt.tendsto.comp hq
  have hexponent : Tendsto (fun n => (p n : ℝ)*Real.log (1-q n)) atTop (𝓝 (-lam)) := by
    have hh := hpq.mul hsl
    simpa only [log_one_sub_eq_mul_slope, mul_assoc, mul_neg_one] using hh
  have hout := Real.continuous_exp.continuousAt.tendsto.comp hexponent
  apply hout.congr'
  filter_upwards [hq.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
  change Real.exp ((p n:ℝ)*Real.log (1-q n)) = _
  rw [Real.exp_nat_mul, Real.exp_log (by linarith : 0<1-q n)]

/-- Critical coordinate-tail inflation gives the corresponding nonzero
maximum-CDF limit at the actual Gaussian maximum threshold. -/
theorem tendsto_maximum_CDF_of_normal_tail_ratio
    {p : ℕ → ℕ} {q : ℕ → ℝ} {a : ℝ}
    (hp : Tendsto p atTop atTop)
    (hqt : Tendsto (fun n => q n / standardNormalUpperTail (normalMaxThreshold (p n)))
      atTop (𝓝 a)) :
    Tendsto (fun n => (1-q n)^(p n)) atTop (𝓝 (Real.exp (-a))) := by
  let t := fun n => standardNormalUpperTail (normalMaxThreshold (p n))
  have ht : Tendsto t atTop (𝓝 0) :=
    normalUpperTail_tendsto_zero.comp (tendsto_normalMaxThreshold_atTop.comp hp)
  have hpt := tendsto_mul_standardNormalUpperTail_normalMaxThreshold.comp hp
  have hq : Tendsto q atTop (𝓝 0) := by
    have hh := hqt.mul ht
    simp only [mul_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n => by
      dsimp [t]
      field_simp [(standardNormalUpperTail_pos _).ne'])
  apply tendsto_one_sub_pow_of_tail hq
  have hh := hpt.mul hqt
  simp only [one_mul] at hh
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    dsimp [t]
    field_simp [(standardNormalUpperTail_pos _).ne']
    <;> ring)

/-- A first-order tail perturbation transfers with the exact derivative
`exp(-1)`. No unquantified error from replacing a binomial CDF by its
Poisson limit is introduced. -/
theorem tendsto_normal_maximum_CDF_firstOrder
    {p : ℕ → ℕ} {q r : ℕ → ℝ} {k : ℝ}
    (hp : Tendsto p atTop atTop)
    (hr : Tendsto r atTop (𝓝 0)) (hrne : ∀ᶠ n in atTop, r n ≠ 0)
    (hpert : Tendsto (fun n =>
      (q n / standardNormalUpperTail (normalMaxThreshold (p n))-1)/r n)
      atTop (𝓝 k)) :
    Tendsto (fun n =>
      (Real.exp (-1)-(1-q n)^(p n))/r n)
      atTop (𝓝 (Real.exp (-1)*k)) := by
  let t := fun n => standardNormalUpperTail (normalMaxThreshold (p n))
  let s := fun n => q n/t n-1
  let z := fun n => (q n-t n)/(1-t n)
  let A := fun n => (p n : ℝ)*(Real.log (1-q n)-Real.log (1-t n))
  have ht : Tendsto t atTop (𝓝 0) :=
    normalUpperTail_tendsto_zero.comp (tendsto_normalMaxThreshold_atTop.comp hp)
  have hpt := tendsto_mul_standardNormalUpperTail_normalMaxThreshold.comp hp
  have hs : Tendsto s atTop (𝓝 0) := by
    have hh := hpert.mul hr
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hrne] with n hn
    dsimp [s,t]
    exact div_mul_cancel₀ _ hn
  have hratio : Tendsto (fun n => q n/t n) atTop (𝓝 1) := by
    have hh := hs.add_const 1
    simpa only [s, sub_add_cancel, zero_add] using hh
  have hq : Tendsto q atTop (𝓝 0) := by
    have hh := hratio.mul ht
    simp only [mul_zero] at hh
    apply hh.congr'
    exact Eventually.of_forall (fun n => by
      dsimp [t]
      exact div_mul_cancel₀ _ (standardNormalUpperTail_pos _).ne')
  have hz : Tendsto z atTop (𝓝 0) := by
    simpa only [z, sub_self, sub_zero, zero_div] using
      (hq.sub ht).div (tendsto_const_nhds.sub ht) (by norm_num : (1:ℝ)-0≠0)
  have hsl : Tendsto (fun n => logOneSubSlope (z n)) atTop (𝓝 (-1:ℝ)) := by
    simpa [logOneSubSlope] using logOneSubSlope_continuousAt.tendsto.comp hz
  have hA : Tendsto (fun n => A n/r n) atTop (𝓝 (-k)) := by
    have hh := ((hpt.mul hpert).div (tendsto_const_nhds.sub ht) (by norm_num : (1:ℝ)-0≠0)).mul hsl
    simp only [one_mul, sub_zero, div_one, mul_neg_one] at hh
    apply hh.congr'
    filter_upwards [hrne,
      hq.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
      ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hrn hqn htn
    have htne : t n≠0 := (standardNormalUpperTail_pos _).ne'
    have ht1 : 1-t n≠0 := by linarith
    have hq1 : 1-q n≠0 := by linarith
    have hlogs : Real.log (1-q n)-Real.log (1-t n)=Real.log (1-z n) := by
      rw [← Real.log_div hq1 ht1]
      congr 1
      dsimp [z]
      field_simp <;> ring
    dsimp only [A]
    rw [hlogs, log_one_sub_eq_mul_slope]
    dsimp [z,t]
    field_simp [htne,ht1,hrn]
    <;> ring
  have hA0 : Tendsto A atTop (𝓝 0) := by
    have hh := hA.mul hr
    simp only [mul_zero] at hh
    apply hh.congr'
    filter_upwards [hrne] with n hn
    exact div_mul_cancel₀ _ hn
  have hexps : Tendsto (fun n => expZeroSlope (A n)) atTop (𝓝 1) := by
    simpa [expZeroSlope] using expZeroSlope_continuousAt.tendsto.comp hA0
  have hfinal := ((tendsto_const_nhds (x := -Real.exp (-1))).mul hexps).mul hA
  simp only [mul_one, neg_mul_neg] at hfinal
  apply hfinal.congr'
  filter_upwards [hp.eventually (eventually_ge_atTop 1), hrne,
    hq.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    ht.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hpn hrn hqn htn
  have hbase : (1-t n)^(p n)=Real.exp (-1) := by
    rw [show 1-t n=standardNormalCDF (normalMaxThreshold (p n)) by
      dsimp [t]; rw [standardNormalUpperTail_eq_one_sub]; ring]
    exact standardNormalCDF_normalMaxThreshold_pow hpn
  have hpower : (1-q n)^(p n)=Real.exp (-1)*Real.exp (A n) := by
    have hpowq : (1-q n)^(p n)=Real.exp ((p n:ℝ)*Real.log (1-q n)) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos (by linarith : 0<1-q n) _)]
    have hpowt : (1-t n)^(p n)=Real.exp ((p n:ℝ)*Real.log (1-t n)) := by
      rw [← Real.log_pow, Real.exp_log (pow_pos (by linarith : 0<1-t n) _)]
    rw [hpowq,←hbase,hpowt,←Real.exp_add]
    congr 1
    dsimp [A]
    ring
  rw [hpower]
  have hslope := exp_sub_one_eq_mul_slope (A n)
  rw [show Real.exp (-1)-Real.exp (-1)*Real.exp (A n) =
    -Real.exp (-1)*(Real.exp (A n)-1) by ring, hslope]
  ring


/-- Critical tail inflation gives the absolute maximum discrepancy. -/
theorem tendsto_normal_maximum_CDF_critical_gap
    {p : ℕ → ℕ} {q : ℕ → ℝ} {a : ℝ}
    (hp : Tendsto p atTop atTop)
    (hqt : Tendsto (fun n => q n/standardNormalUpperTail (normalMaxThreshold (p n)))
      atTop (𝓝 a)) :
    Tendsto (fun n => |Real.exp (-1)-(1-q n)^(p n)|)
      atTop (𝓝 |Real.exp (-1)-Real.exp (-a)|) :=
  (tendsto_const_nhds.sub (tendsto_maximum_CDF_of_normal_tail_ratio hp hqt)).abs

/-- The absolute first-order discrepancy, with positive normalization. -/
theorem tendsto_normal_maximum_CDF_firstOrder_abs
    {p : ℕ → ℕ} {q r : ℕ → ℝ} {k : ℝ}
    (hp : Tendsto p atTop atTop)
    (hr : Tendsto r atTop (𝓝 0)) (hrpos : ∀ᶠ n in atTop,0<r n)
    (hpert : Tendsto (fun n =>
      (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)/r n)
      atTop (𝓝 k)) :
    Tendsto (fun n => |Real.exp (-1)-(1-q n)^(p n)|/r n)
      atTop (𝓝 (Real.exp (-1)*|k|)) := by
  have hh := (tendsto_normal_maximum_CDF_firstOrder hp hr
    (hrpos.mono (fun _ hn => hn.ne')) hpert).abs
  rw [abs_mul,abs_of_pos (Real.exp_pos _)] at hh
  apply hh.congr'
  filter_upwards [hrpos] with n hn
  rw [abs_div,abs_of_pos hn]

/-- A universal derivative factor, useful when the normalized scalar-tail
perturbation has only a lower limit rather than a limit. -/
theorem tendsto_normal_maximum_CDF_relativePerturbation
    {p : ℕ → ℕ} {q : ℕ → ℝ}
    (hp : Tendsto p atTop atTop)
    (hpert : Tendsto (fun n => q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)
      atTop (𝓝 0))
    (hne : ∀ᶠ n in atTop,q n/standardNormalUpperTail (normalMaxThreshold (p n))-1≠0) :
    Tendsto (fun n => (Real.exp (-1)-(1-q n)^(p n))/
      (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1))
      atTop (𝓝 (Real.exp (-1))) := by
  have hone : Tendsto (fun n =>
      (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)/
        (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1))
      atTop (𝓝 (1:ℝ)) := by
    apply tendsto_const_nhds.congr'
    filter_upwards [hne] with n hn
    exact (div_self hn).symm
  simpa only [mul_one] using
    tendsto_normal_maximum_CDF_firstOrder hp hpert hne hone


/-- The exact first-order lower-limit multiplier, even when the normalized
coordinate-tail perturbation does not converge. -/
theorem normal_maximum_CDF_liminf_from_relativeTail
    {p : ℕ → ℕ} {q r : ℕ → ℝ} {K : ℝ}
    (hp : Tendsto p atTop atTop)
    (hpert : Tendsto (fun n => q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)
      atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop,0<q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)
    (hrpos : ∀ᶠ n in atTop,0<r n)
    (hupper : atTop.IsBoundedUnder (·≤·) (fun n =>
      (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)/r n))
    (hlower : K≤liminf (fun n =>
      (q n/standardNormalUpperTail (normalMaxThreshold (p n))-1)/r n) atTop) :
    Real.exp (-1)*K≤liminf (fun n => |Real.exp (-1)-(1-q n)^(p n)|/r n) atTop := by
  let s := fun n => q n/standardNormalUpperTail (normalMaxThreshold (p n))-1
  let f := fun n => |(Real.exp (-1)-(1-q n)^(p n))/s n|
  let v := fun n => s n/r n
  have hf : Tendsto f atTop (𝓝 (Real.exp (-1))) := by
    have hh := (tendsto_normal_maximum_CDF_relativePerturbation hp hpert
      (hpos.mono (fun _ hn => hn.ne'))).abs
    simpa only [abs_of_pos (Real.exp_pos _)] using hh
  have hv : ∀ᶠ n in atTop,0≤v n := by
    filter_upwards [hpos,hrpos] with n hs hr
    exact div_nonneg hs.le hr.le
  have hmul := le_liminf_mul
    (Eventually.of_forall (fun n => abs_nonneg ((Real.exp (-1)-(1-q n)^(p n))/s n)))
    hf.isBoundedUnder_le hv hupper.isCoboundedUnder_ge
  rw [hf.liminf_eq] at hmul
  have hout := (mul_le_mul_of_nonneg_left hlower (Real.exp_pos (-1)).le).trans hmul
  apply hout.trans_eq
  apply liminf_congr
  filter_upwards [hpos,hrpos] with n hs hr
  change |(Real.exp (-1)-(1-q n)^(p n))/s n| * (s n/r n)=_
  rw [abs_div,abs_of_pos hs]
  field_simp [hs.ne',hr.ne']
  simp only [s,mul_assoc]

end
end RectangleCLT.Companion
