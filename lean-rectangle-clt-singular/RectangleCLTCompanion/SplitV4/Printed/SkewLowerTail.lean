import RectangleCLTCompanion.SplitV4.Printed.SkewLowerModerate
import RectangleCLTCompanion.LowerSkewExponential
import RectangleCLTCompanion.LowerMaxCDFActual
import RectangleCLTCompanion.LowerRectangleDistance

/-! The printed F.1 application and first-order product argument for
Theorem 3. The actual two-point tail is supplied by generic F.1, not by
the pre-existing specialized Cramer estimate or final lower bound. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem twoPoint_normalized_tail_from_F1 {B : ℝ} (hB : 1 ≤ B)
    {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant*((B/Real.sqrt n)*(1+x)) ≤ 1) :
    0 < lowerCoordinateUpperTail B n x ∧
    |Real.log (lowerCoordinateUpperTail B n x/standardNormalUpperTail x)-
      (B-B⁻¹)*x^3/(6*Real.sqrt n)| ≤
      moderateTailRemainderConstant*((B/Real.sqrt n)*(1+x)+(B/Real.sqrt n)^2*x^4) := by
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have ht := iid_normalized_moderate_tail (lowerTwoPointLaw B) hBp
    (lowerTwoPointLaw_envelope hB) (lowerTwoPointLaw_centered hBp.ne')
    (lowerTwoPointLaw_second hBp.ne') hn hx hsmall
  rw [lowerTwoPointLaw_third hBp.ne'] at ht
  have htail : (Measure.pi (fun _ : Fin n => lowerTwoPointLaw B)).real
      {z | x < (∑ i : Fin n,z i)/Real.sqrt n} = lowerCoordinateUpperTail B n x := by
    unfold lowerCoordinateUpperTail lowerScalarArrayLaw
    congr 1
  rw [htail] at ht
  exact ht

theorem skew_tail_from_F1_eventually {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    ∀ᶠ n in atTop, 0 < lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)) ∧
      |lowerSkewLogTail (B n) (p n) n-
        (B n-(B n)⁻¹)*normalMaxThreshold (p n)^3/(6*Real.sqrt n)| ≤
      (2*moderateTailRemainderConstant)*
        (B n*normalMaxThreshold (p n)/Real.sqrt n+(B n)^2*normalMaxThreshold (p n)^4/n) := by
  have hx := (tendsto_normalMaxThreshold_atTop.comp hp).eventually (eventually_ge_atTop 2)
  have hs := (lower_skew_linear_scale hp hr).const_mul (2*moderateTailSmallConstant)
  simp only [mul_zero] at hs
  have hsmall := hs.eventually (eventually_le_nhds (by norm_num : (0 : ℝ)<1))
  filter_upwards [hx,hsmall,eventually_ge_atTop 1] with n hxn hsn hn
  change 2 ≤ normalMaxThreshold (p n) at hxn
  have hnR : (0 : ℝ)<n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hsN : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hBn : 0 < B n := by linarith only [hB n]
  have hδ : 0 ≤ B n/Real.sqrt n := (div_pos hBn hsN).le
  have hlin : (B n/Real.sqrt n)*(1+normalMaxThreshold (p n)) ≤
      2*(B n*normalMaxThreshold (p n)/Real.sqrt n) := by
    calc
      _ ≤ (B n/Real.sqrt n)*(2*normalMaxThreshold (p n)) :=
        mul_le_mul_of_nonneg_left (by linarith only [hxn]) hδ
      _ = _ := by ring
  have hH : 0 ≤ moderateTailSmallConstant := moderateTailSmallConstant_bounds.1.le
  have hsmall' : moderateTailSmallConstant*((B n/Real.sqrt n)*(1+normalMaxThreshold (p n))) ≤ 1 := by
    exact (mul_le_mul_of_nonneg_left hlin hH).trans (by convert hsn using 1 <;> ring)
  have ht := twoPoint_normalized_tail_from_F1 (by linarith only [hB n]) hn (by linarith only [hxn]) hsmall'
  refine ⟨ht.1,ht.2.trans ?_⟩
  have hfourth : (B n/Real.sqrt n)^2*normalMaxThreshold (p n)^4 =
      (B n)^2*normalMaxThreshold (p n)^4/n := by rw [div_pow,Real.sq_sqrt hnR.le];ring
  rw [hfourth]
  have hC := moderateTailRemainderConstant_bounds.1.le
  have hfourth0 : 0 ≤ (B n)^2*normalMaxThreshold (p n)^4/(n : ℝ) := by positivity
  have hm := mul_le_mul_of_nonneg_left hlin hC
  nlinarith only [hm,mul_nonneg hC hfourth0]

theorem skew_log_tail_remainder_ratio_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => (lowerSkewLogTail (B n) (p n) n-
      (B n-(B n)⁻¹)*normalMaxThreshold (p n)^3/(6*Real.sqrt n))/
        lowerSkewRate (B n) (p n) n) atTop (𝓝 0) := by
  have hz := ((lower_skew_linear_remainder_ratio hB hp).add
    (lower_skew_quartic_remainder_ratio hB hp hr)).const_mul (2*moderateTailRemainderConstant)
  simp only [zero_add,mul_zero] at hz
  apply squeeze_zero_norm' _ hz
  filter_upwards [skew_tail_from_F1_eventually hB hp hr,lowerSkewRate_eventually_pos hB hp] with n hn hnr
  rw [Real.norm_eq_abs,abs_div,abs_of_pos hnr]
  exact (div_le_div_of_nonneg_right hn.2 hnr.le).trans_eq (by ring)

theorem skew_log_tail_normalized_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ} {r₀ : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 r₀)) :
    Tendsto (fun n => lowerSkewLogTail (B n) (p n) n/lowerSkewRate (B n) (p n) n-
      lowerSkewCoefficient (B n)) atTop (𝓝 0) := by
  have hh := (skew_log_tail_remainder_ratio_from_F1 hB hp hr).add
    (lower_skew_cubic_coefficient_difference hB hp)
  simp only [zero_add] at hh
  apply hh.congr
  intro n
  unfold lowerSkewCoefficient
  ring

theorem skew_relative_tail_facts_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    Tendsto (fun n => (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n))-1)/lowerSkewRate (B n) (p n) n-
      lowerSkewCoefficient (B n)) atTop (𝓝 0) ∧
    Tendsto (fun n => lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n))-1) atTop (𝓝 0) ∧
    (∀ᶠ n in atTop,0<lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n))-1) ∧
    atTop.IsBoundedUnder (·≤·) (fun n => (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n))-1)/lowerSkewRate (B n) (p n) n) ∧
    Real.sqrt 2/4≤liminf (fun n => (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n))-1)/lowerSkewRate (B n) (p n) n) atTop := by
  have hR : ∀ᶠ n in atTop,0<lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n)) := by
    filter_upwards [skew_tail_from_F1_eventually hB hp hr] with n hn
    exact div_pos hn.1 (standardNormalUpperTail_pos _)
  exact lower_log_relative_tail_to_relative_tail (by positivity : 0<Real.sqrt 2/4)
    (Eventually.of_forall (fun n => lowerSkewCoefficient_bounds (hB n))) hr
    (lowerSkewRate_eventually_pos hB hp) hR (skew_log_tail_normalized_from_F1 hB hp hr)

theorem skew_detecting_rectangle_liminf_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n, 2 ≤ B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    Real.sqrt 2/(4*Real.exp 1)≤liminf (fun n =>
      rectangleError (lowerArrayLaw (B n) n (p n))
        (sumVector (lowerNormalizedRows (n:=n) (p:=p n))) 1
        (partialMaximumRectangle (p n) (p n) (normalMaxThreshold (p n)))/
          lowerSkewRate (B n) (p n) n) atTop := by
  have hs := skew_relative_tail_facts_from_F1 hB hp hr
  have hh := lowerMaximum_rectangleError_liminf hp
    (Eventually.of_forall (fun n => (le_rfl : p n≤p n))) hs.2.1 hs.2.2.1
    (lowerSkewRate_eventually_pos hB hp) hs.2.2.2.1 hs.2.2.2.2
  apply le_trans _ hh
  rw [Real.exp_neg]
  simp only [div_eq_mul_inv,mul_inv]
  ring_nf
  exact le_rfl

/-- The explicit `O(r_n^2)` exponentiation error printed after the F.1
application. This proves the stronger quadratic assertion, in addition
to the first-order relative-tail limit used by the lower bound. -/
theorem skew_exponentiation_quadratic_error_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀n,2≤B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      |lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
        standardNormalUpperTail (normalMaxThreshold (p n))-1-lowerSkewLogTail (B n) (p n) n|≤
      (Real.sqrt 2/3+1)^2*(lowerSkewRate (B n) (p n) n)^2 := by
  let M : ℝ := Real.sqrt 2/3+1
  have hM : 0<M := by dsimp [M]; positivity
  have hlog := skew_log_tail_normalized_from_F1 hB hp hr
  have hMr := hr.const_mul M
  simp only [mul_zero] at hMr
  filter_upwards [hlog.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1)),
    hlog.eventually (eventually_gt_nhds (by have := Real.sqrt_pos.mpr (by norm_num : (0:ℝ)<2); linarith : -(Real.sqrt 2/8)<(0:ℝ))),
    hMr.eventually (eventually_le_nhds (by norm_num : (0:ℝ)<1)),lowerSkewRate_eventually_pos hB hp,
    skew_tail_from_F1_eventually hB hp hr] with n hu hl hm hrn ht
  have hκ := lowerSkewCoefficient_bounds (hB n)
  have hupper : lowerSkewLogTail (B n) (p n) n/lowerSkewRate (B n) (p n) n≤M := by
    dsimp [M]
    linarith only [hu,hκ.2]
  have hlower : 0<lowerSkewLogTail (B n) (p n) n/lowerSkewRate (B n) (p n) n := by
    have hs : 0<Real.sqrt 2/8 := by positivity
    linarith only [hl,hκ.1,hs]
  have hlogpos : 0<lowerSkewLogTail (B n) (p n) n := (div_pos_iff_of_pos_right hrn).mp hlower
  have hlogupper : lowerSkewLogTail (B n) (p n) n≤M*lowerSkewRate (B n) (p n) n :=
    (div_le_iff₀ hrn).mp hupper
  have hsmall : |lowerSkewLogTail (B n) (p n) n|≤1 := by rw [abs_of_pos hlogpos]; exact hlogupper.trans hm
  have he := Real.abs_exp_sub_one_sub_id_le hsmall
  have hR : 0<lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
      standardNormalUpperTail (normalMaxThreshold (p n)) := div_pos ht.1 (standardNormalUpperTail_pos _)
  change |Real.exp (Real.log (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
    standardNormalUpperTail (normalMaxThreshold (p n))))-1-lowerSkewLogTail (B n) (p n) n|≤_ at he
  rw [Real.exp_log hR] at he
  apply he.trans
  have hh := (sq_le_sq₀ hlogpos.le (mul_pos hM hrn).le).mpr hlogupper
  simpa only [mul_pow,M] using hh

end
end RectangleCLT.Companion.SplitV4.Printed
