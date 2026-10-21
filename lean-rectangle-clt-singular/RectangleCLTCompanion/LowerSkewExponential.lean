import RectangleCLTCompanion.LowerMaxCDFLimits

/-! Relative-tail transfer from a proved logarithmic expansion. The
coefficient may vary throughout a fixed positive compact interval; no
convergence of the skewness coefficient is assumed. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion
noncomputable section

private def lowerExpSlope : ℝ → ℝ :=
  Function.update (fun x : ℝ => (Real.exp x-1)/x) 0 1

private theorem lowerExpSlope_continuousAt : ContinuousAt lowerExpSlope 0 := by
  simpa only [lowerExpSlope,Real.exp_zero,sub_zero] using
    (Real.hasDerivAt_exp 0).continuousAt_div

private theorem lower_exp_sub_one (x : ℝ) : Real.exp x-1=x*lowerExpSlope x := by
  by_cases hx : x=0
  · subst x; simp [lowerExpSlope]
  · simp only [lowerExpSlope,Function.update_of_ne hx]
    field_simp

/-- The first-order exponential transfer, its positivity, boundedness,
and exact lower limit. `R` is the actual coordinate-tail ratio when this
scalar result is instantiated in the lower construction. -/
theorem lower_log_relative_tail_to_relative_tail
    {R r a : ℕ → ℝ} {a₀ a₁ : ℝ}
    (ha₀ : 0<a₀) (ha : ∀ᶠ n in atTop,a₀≤a n ∧ a n≤a₁)
    (hr : Tendsto r atTop (𝓝 0)) (hrpos : ∀ᶠ n in atTop,0<r n)
    (hRpos : ∀ᶠ n in atTop,0<R n)
    (hlog : Tendsto (fun n => Real.log (R n)/r n-a n) atTop (𝓝 0)) :
    Tendsto (fun n => (R n-1)/r n-a n) atTop (𝓝 0) ∧
      Tendsto (fun n => R n-1) atTop (𝓝 0) ∧
      (∀ᶠ n in atTop,0<R n-1) ∧
      atTop.IsBoundedUnder (·≤·) (fun n => (R n-1)/r n) ∧
      a₀≤liminf (fun n => (R n-1)/r n) atTop := by
  let l := fun n => Real.log (R n)/r n
  have hlower : ∀ᶠ n in atTop,a₀/2≤l n := by
    filter_upwards [ha,hlog.eventually (eventually_gt_nhds (by linarith : -a₀/2<0))]
      with n han hen
    dsimp [l]
    linarith [han.1]
  have hupper : ∀ᶠ n in atTop,l n≤a₁+1 := by
    filter_upwards [ha,hlog.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with n han hen
    dsimp [l]
    linarith [han.2]
  have hlog0 : Tendsto (fun n => Real.log (R n)) atTop (𝓝 0) := by
    have hh := bdd_le_mul_tendsto_zero hlower hupper hr
    apply hh.congr'
    filter_upwards [hrpos] with n hn
    exact div_mul_cancel₀ _ hn.ne'
  have hR0 : Tendsto (fun n => R n-1) atTop (𝓝 0) := by
    have hh := (Real.continuous_exp.continuousAt.tendsto.comp hlog0).sub_const 1
    simp only [Real.exp_zero,sub_self] at hh
    apply hh.congr'
    filter_upwards [hRpos] with n hn
    rw [Function.comp_apply,Real.exp_log hn]
  have hslope : Tendsto (fun n => lowerExpSlope (Real.log (R n))-1) atTop (𝓝 0) := by
    have hh := (lowerExpSlope_continuousAt.tendsto.comp hlog0).sub_const 1
    simpa only [lowerExpSlope,Function.update_self,sub_self] using hh
  have hproduct := bdd_le_mul_tendsto_zero hlower hupper hslope
  have htransfer : Tendsto (fun n => (R n-1)/r n-a n) atTop (𝓝 0) := by
    have hh := hproduct.add hlog
    simp only [add_zero] at hh
    apply hh.congr'
    filter_upwards [hRpos] with n hn
    have he : R n-1=Real.log (R n)*lowerExpSlope (Real.log (R n)) := by
      simpa only [Real.exp_log hn] using lower_exp_sub_one (Real.log (R n))
    rw [he]
    dsimp [l]
    ring
  have hpositive : ∀ᶠ n in atTop,0<R n-1 := by
    filter_upwards [hlower,hrpos,hRpos] with n hln hrn hRn
    have hlpos : 0<Real.log (R n)/r n := (half_pos ha₀).trans_le hln
    have hlogpos : 0<Real.log (R n) := (div_pos_iff_of_pos_right hrn).mp hlpos
    have he := Real.one_lt_exp_iff.mpr hlogpos
    rw [Real.exp_log hRn] at he
    linarith
  have huupper : ∀ᶠ n in atTop,(R n-1)/r n≤a₁+1 := by
    filter_upwards [ha,htransfer.eventually (eventually_lt_nhds (by norm_num : (0:ℝ)<1))]
      with n han hen
    linarith [han.2]
  have hubounded : atTop.IsBoundedUnder (·≤·) (fun n => (R n-1)/r n) :=
    isBoundedUnder_of_eventually_le huupper
  have hunonneg : ∀ᶠ n in atTop,0≤(R n-1)/r n := by
    filter_upwards [hpositive,hrpos] with n hpn hrn
    exact (div_pos hpn hrn).le
  have hliminf : a₀≤liminf (fun n => (R n-1)/r n) atTop := by
    apply (le_liminf_iff hubounded.isCoboundedUnder_ge
      (isBoundedUnder_of_eventually_ge hunonneg)).mpr
    intro b hb
    filter_upwards [ha,htransfer.eventually (eventually_gt_nhds (by linarith : b-a₀<0))]
      with n han hen
    linarith [han.1]
  exact ⟨htransfer,hR0,hpositive,hubounded,hliminf⟩

end
end RectangleCLT.Companion
