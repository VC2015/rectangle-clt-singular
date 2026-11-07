import RectangleCLTCompanion.SplitV4.Printed.SkewLowerTail
import Mathlib.Topology.Instances.EReal.Lemmas

/-! The signed first-order product expansion and supremum passage in the
printed proof of Theorem 3, with its scalar input obtained from F.1. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Signed form of the product expansion, allowing a varying skewness
coefficient rather than assuming that coefficient converges. -/
theorem skew_signed_product_normalized_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      (Real.exp (-1)-(1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n))/
        lowerSkewRate (B n) (p n) n-Real.exp (-1)*lowerSkewCoefficient (B n))
      atTop (𝓝 0) := by
  let q := fun n => lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))
  let r := fun n => lowerSkewRate (B n) (p n) n
  let u := fun n => q n/standardNormalUpperTail (normalMaxThreshold (p n))-1
  let v := fun n => u n/r n
  let d := fun n => (Real.exp (-1)-(1-q n)^(p n))/u n
  have hs := skew_relative_tail_facts_from_F1 hB hp hr
  have hd : Tendsto d atTop (𝓝 (Real.exp (-1))) :=
    tendsto_normal_maximum_CDF_relativePerturbation hp hs.2.1
      (hs.2.2.1.mono (fun _ hn => hn.ne'))
  have hv0 : ∀ᶠ n in atTop,0≤v n := by
    filter_upwards [hs.2.2.1,lowerSkewRate_eventually_pos hB hp] with n hun hrn
    exact (div_pos hun hrn).le
  have hv1 : ∀ᶠ n in atTop,v n≤Real.sqrt 2/3+1 := by
    filter_upwards [hs.1.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))] with n hn
    have hκ := (lowerSkewCoefficient_bounds (hB n)).2
    change v n-lowerSkewCoefficient (B n)<1 at hn
    linarith
  have hd0 : Tendsto (fun n => d n-Real.exp (-1)) atTop (𝓝 0) := by
    simpa only [sub_self] using hd.sub_const (Real.exp (-1))
  have hz := (bdd_le_mul_tendsto_zero hv0 hv1 hd0).add
    (hs.1.const_mul (Real.exp (-1)))
  simp only [sub_self,mul_zero,zero_add] at hz
  apply hz.congr'
  filter_upwards [hs.2.2.1,lowerSkewRate_eventually_pos hB hp] with n hun hrn
  change 0<u n at hun
  change 0<r n at hrn
  change (u n/r n)*((Real.exp (-1)-(1-q n)^(p n))/u n-Real.exp (-1))+
    Real.exp (-1)*(u n/r n-lowerSkewCoefficient (B n))=
      (Real.exp (-1)-(1-q n)^(p n))/r n-Real.exp (-1)*lowerSkewCoefficient (B n)
  field_simp [hun.ne',hrn.ne']
  <;> ring

/-- The literal multiplicative asymptotic in (opt:exact-product-asymptotic).
The ratio is well defined eventually because the printed cubic term is
uniformly positive after division by the stated rate. -/
theorem skew_exact_product_asymptotic_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    Tendsto (fun n =>
      ((1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n)-Real.exp (-1))/
        (-(B n-(B n)⁻¹)*normalMaxThreshold (p n)^3/(6*Real.exp 1*Real.sqrt n)))
      atTop (𝓝 1) := by
  let r := fun n => lowerSkewRate (B n) (p n) n
  let s := fun n => (B n-(B n)⁻¹)*normalMaxThreshold (p n)^3/(6*Real.sqrt n)
  let g := fun n => Real.exp (-1)-(1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n)
  have hs : Tendsto (fun n => s n/r n-lowerSkewCoefficient (B n)) atTop (𝓝 0) :=
    lower_skew_cubic_coefficient_difference hB hp
  have he : Tendsto (fun n => g n/r n-Real.exp (-1)*(s n/r n)) atTop (𝓝 0) := by
    have hh := (skew_signed_product_normalized_from_F1 hB hp hr).sub (hs.const_mul (Real.exp (-1)))
    simp only [mul_zero,sub_self] at hh
    apply hh.congr
    intro n
    dsimp [g]
    ring
  have hspos : ∀ᶠ n in atTop,Real.sqrt 2/8≤s n/r n := by
    filter_upwards [hs.eventually (eventually_gt_nhds (by have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2); linarith : -(Real.sqrt 2/8)<(0:ℝ)))] with n hn
    have hκ := (lowerSkewCoefficient_bounds (hB n)).1
    linarith
  have hlow : ∀ᶠ n in atTop,0≤r n/s n := by
    filter_upwards [hspos,lowerSkewRate_eventually_pos hB hp] with n hsn hrn
    have hdiv : 0<s n/r n := (by positivity : (0:ℝ)<Real.sqrt 2/8).trans_le hsn
    have hsp : 0<s n := (div_pos_iff_of_pos_right hrn).mp hdiv
    exact (div_pos hrn hsp).le
  have hupp : ∀ᶠ n in atTop,r n/s n≤8/Real.sqrt 2 := by
    filter_upwards [hspos,lowerSkewRate_eventually_pos hB hp] with n hsn hrn
    have hdiv : 0<s n/r n := (by positivity : (0:ℝ)<Real.sqrt 2/8).trans_le hsn
    have hh := one_div_le_one_div_of_le (by positivity : (0:ℝ)<Real.sqrt 2/8) hsn
    simpa only [one_div,inv_div] using hh
  have hz := bdd_le_mul_tendsto_zero hlow hupp he
  have hf : Tendsto (fun n => g n/s n-Real.exp (-1)) atTop (𝓝 0) := by
    apply hz.congr'
    filter_upwards [hspos,lowerSkewRate_eventually_pos hB hp] with n hsn hrn
    have hsp : 0<s n := (div_pos_iff_of_pos_right hrn).mp
      ((by positivity : (0:ℝ)<Real.sqrt 2/8).trans_le hsn)
    field_simp [hsp.ne',hrn.ne']
    <;> ring
  have hh := (hf.add_const (Real.exp (-1))).div_const (Real.exp (-1))
  simp only [zero_add,div_self (Real.exp_ne_zero _)] at hh
  apply hh.congr
  intro n
  have hden : -(B n-(B n)⁻¹)*normalMaxThreshold (p n)^3/(6*Real.exp 1*Real.sqrt n) =
      -s n*Real.exp (-1) := by dsimp [s]; rw [Real.exp_neg]; ring
  rw [hden,show (1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n)-Real.exp (-1) = -g n by dsimp [g]; ring]
  simp only [sub_add_cancel,neg_mul,neg_div_neg_eq,div_mul_eq_div_div]

/-- Full rectangle distance inherits every strict lower constant below
the displayed one. This formulation requires no upper bound on the full
distance divided by a rate tending to zero. -/
theorem skew_full_distance_eventual_lower_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0))
    {c : ℝ} (hc : c<Real.sqrt 2/(4*Real.exp 1)) :
    ∀ᶠ n in atTop,c<lowerConstructionDistance (B n) n (p n)/lowerSkewRate (B n) (p n) n := by
  have he := skew_signed_product_normalized_from_F1 hB hp hr
  have hec : c-Real.sqrt 2/(4*Real.exp 1)<0 := by linarith
  filter_upwards [he.eventually (eventually_gt_nhds hec),
    lowerSkewRate_eventually_pos hB hp,hp.eventually (eventually_ge_atTop 1)] with n hen hrn hpn
  have hκ := mul_le_mul_of_nonneg_left (lowerSkewCoefficient_bounds (hB n)).1 (Real.exp_pos (-1)).le
  have hconst : Real.exp (-1)*(Real.sqrt 2/4)=Real.sqrt 2/(4*Real.exp 1) := by
    rw [Real.exp_neg]
    ring
  rw [hconst] at hκ
  have hgap : c<(Real.exp (-1)-(1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n))/
      lowerSkewRate (B n) (p n) n := by linarith
  have ha := lowerArrayLaw_partialMaximum_rectangleError (B n) n (le_rfl : p n≤p n)
    (normalMaxThreshold (p n))
  rw [standardNormalCDF_normalMaxThreshold_pow hpn,abs_sub_comm] at ha
  have habs := le_abs_self (Real.exp (-1)-(1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n))
  exact hgap.trans_le ((div_le_div_of_nonneg_right habs hrn.le).trans (by
    rw [←ha]
    exact div_le_div_of_nonneg_right (lower_rectangleError_le_distance _ _ _ _) hrn.le))

theorem skew_full_distance_ereal_liminf_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    ((Real.sqrt 2/(4*Real.exp 1) : ℝ) : EReal)≤liminf (fun n =>
      ((lowerConstructionDistance (B n) n (p n)/lowerSkewRate (B n) (p n) n : ℝ) : EReal)) atTop := by
  apply le_of_forall_lt
  intro c hc
  obtain ⟨b,hcb,hba⟩ := EReal.exists_between_coe_real hc
  have hb : b<Real.sqrt 2/(4*Real.exp 1) := by exact_mod_cast hba
  apply hcb.trans_le
  refine le_liminf_of_le (by isBoundedDefault) ?_
  filter_upwards [skew_full_distance_eventual_lower_from_F1 hB hp hr hb] with n hn
  exact_mod_cast hn.le

end
end RectangleCLT.Companion.SplitV4.Printed
