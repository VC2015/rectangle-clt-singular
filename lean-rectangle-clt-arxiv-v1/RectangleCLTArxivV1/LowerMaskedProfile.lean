import RectangleCLTArxivV1.LowerMaskedDetection

/-! The prescribed Gaussian width for the actual masked model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem tendsto_lowerFamilyRare_shiftScale {P : ℕ → SymmetricFamilyParameters} {r : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n)
    (hsmall : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0)) :
    Tendsto (fun n => familyRareShiftScale (P n) n) atTop (𝓝 0) := by
  let c := Real.sqrt (2/Real.pi)
  have hc : 0 < c := by dsimp [c]; positivity
  have hbound : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)/c) atTop (𝓝 0) := by
    simpa only [zero_div] using hsmall.div_const c
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop 1] with n hn
    exact (familyRareShiftScale_pos (P n) hn).le
  · filter_upwards [eventually_ge_atTop 1] with n hn
    apply (le_div_iff₀ hc).mpr
    exact mul_le_mul_of_nonneg_left (independentAbsGaussianMean_lower (hr n))
      (familyRareShiftScale_pos (P n) hn).le

theorem tendsto_lowerFamilyMasked_rare_width
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))/
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (P n).variance*independentAbsGaussianMean (m n)) atTop (𝓝 0) := by
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hprod := hcoef.mul (tendsto_lowerFamilyRare_shiftScale hr hsmall)
  have hprod' : Tendsto (fun n => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))) atTop (𝓝 0) := by
    have hh : Tendsto (fun n => (Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))/
        familyRareShiftScale (P n) n)*familyRareShiftScale (P n) n) atTop (𝓝 0) := by
      simpa only [mul_zero] using hprod
    apply hh.congr'
    filter_upwards [eventually_ge_atTop 1] with n hn
    exact div_mul_cancel₀ _ (familyRareShiftScale_pos (P n) hn).ne'
  have hbound : Tendsto (fun n => 2*(Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)))) atTop (𝓝 0) := by
    simpa only [mul_zero] using hprod'.const_mul 2
  apply squeeze_zero' _ _ hbound
  · exact Eventually.of_forall (fun n => mul_nonneg (Real.sqrt_nonneg _) (independentAbsGaussianMean_nonneg _))
  · filter_upwards [hlog.eventually (eventually_ge_atTop 1)] with n hnL
    have hm1 : 1 ≤ m n := by have := hm n; omega
    have hG := independentAbsGaussianMean_upper hm1
    have hdim : dimensionLog (m n) ≤ 2*Real.log (m n : ℝ) := by
      rw [dimensionLog_eq_one_add_log hm1]
      linarith
    have hGS := hG.trans (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hdim) (by norm_num : (0 : ℝ) ≤ 2))
    have hh := mul_le_mul_of_nonneg_left hGS (Real.sqrt_nonneg (P n).variance)
    convert hh using 1 <;> ring

theorem lowerFamilyMasked_width_profile
    {P : ℕ → SymmetricFamilyParameters} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hsmall : Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))/
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))/
      independentAbsGaussianMean (r n)) atTop (𝓝 1) :=
  lowerFamilyGaussianMaximumMean_width_profile hr (fun n => by have := hm n; omega) hv
    (tendsto_lowerFamilyMasked_rare_width hr hm hmTop hsmall hcoef)

end
end RectangleCLTArxivV1
