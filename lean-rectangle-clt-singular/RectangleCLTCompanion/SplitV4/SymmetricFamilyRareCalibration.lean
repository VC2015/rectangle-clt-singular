import RectangleCLTCompanion.SplitV4.SymmetricFamilyUnmasked

/-! Actual masked-maximum calibration for sparse activations. The only
asymptotic inputs are explicit numerical functions of the primitive mask parameters. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyMasked_failure_bound (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (hk : 0 < (n : ℝ)*P.theta) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z} ≤
      1/((n : ℝ)*P.theta) + Real.exp (-(m : ℝ)*(P.pi/2)^Nat.ceil (2*((n : ℝ)*P.theta))) := by
  let k := (n : ℝ)*P.theta
  let b := Nat.ceil (2*k)
  change 0 < k at hk
  have hb : 2*k ≤ (b : ℝ) := Nat.le_ceil _
  have hkb : k < b := by linarith
  have htail := familyActivationCount_upper_tail P n m hkb
  have hden : 0 < (b : ℝ)-k := by linarith
  have hfrac : k/((b : ℝ)-k)^2 ≤ 1/k := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hden) hk).mpr
    nlinarith only [hb, sq_nonneg ((b : ℝ)-2*k)]
  exact (familyMaskedSignMaximum_all_active_bound P n m b).trans
    (add_le_add_right (htail.trans hfrac) _)

theorem tendsto_familyMasked_maximum_mean_ratio (P : ℕ → SymmetricFamilyParameters) (m : ℕ → ℕ)
    [∀ n, NeZero (m n)]
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop) :
    Tendsto (fun n : ℕ => (∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw (P n) n (m n)) /
      ((n : ℝ)*(P n).theta)) atTop (𝓝 1) := by
  let bad := fun n => (familyRestArrayLaw (P n) n (m n)).real
    {z | familyMaskedSignMaximum z ≠ familyActivationCount z}
  have hInv : Tendsto (fun n : ℕ => 1/((n : ℝ)*(P n).theta)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hk
  have hExp := Real.tendsto_exp_atBot.comp (tendsto_neg_atTop_atBot.comp hcover)
  have hUp := hInv.add hExp
  simp only [add_zero, Function.comp_apply, neg_mul] at hUp
  have hBad : Tendsto bad atTop (𝓝 0) := by
    apply squeeze_zero' (Eventually.of_forall (fun _ => measureReal_nonneg)) _ hUp
    filter_upwards [hk.eventually (eventually_gt_atTop 0)] with n hn
    simpa only [neg_mul] using familyMasked_failure_bound (P n) n (m n) hn
  have hroot := (Real.continuous_sqrt.continuousAt.tendsto.comp hBad).const_mul 3
  simp only [Real.sqrt_zero, mul_zero] at hroot
  have herr : ∀ᶠ n : ℕ in atTop,
      |(∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw (P n) n (m n))/((n : ℝ)*(P n).theta)-1| ≤
        3*Real.sqrt (bad n) := by
    filter_upwards [hk.eventually (eventually_ge_atTop 1)] with n hn
    exact familyMaskedSignMaximum_mean_ratio_error (P n) n (m n) hn
  have habs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) herr hroot
  exact tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [Real.norm_eq_abs] using habs)

end
end RectangleCLT.Companion.SplitV4
