import RectangleCLTCompanion.SplitV4.RareFamilyShifts
import RectangleCLTCompanion.SplitV4.SymmetricBoundedRademacher

/-! Actual local comparison for sparse masked common families. All input
limits concern explicit scalar parameter functions, never probabilities or desired estimates. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem rare_moment_cost_identity {K ell a s N k v C d : ℝ}
    (hN : 0 < N) (hv : 0 ≤ v) (hs : s ≠ 0) (hd : d ≠ 0) :
    (K*ell)*((a/(s*Real.sqrt N))^2*(k^2+k)+(Real.sqrt v/s)^2*(C*(1+ell)))/d =
      K/s^2*(ell*a^2*(k^2+k)/N/d+C*(ell*v*(1+ell)/d)) := by
  rw [div_pow, mul_pow, Real.sq_sqrt hN.le, div_pow, Real.sq_sqrt hv]
  field_simp
  ring

theorem tendsto_familyRare_local_remainder {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ}
    [∀ n, NeZero (m n)] (C : ℝ) (hC : 0 ≤ C) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hU : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(P n).amplitude^2*
      (((n : ℝ)*(P n).theta)^2+(n : ℝ)*(P n).theta)/n/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0))
    (hV : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(P n).variance*(1+Real.log (m n : ℝ)) /
      familyRareLowerScale (P n) n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => localShiftComparisonCost (C*Real.log (m n : ℝ))
      (1/Real.sqrt (Real.log (m n : ℝ))) (normalMaximumDensity (m n) (normalMaxThreshold (m n))) *
      familyShiftSecondMoments (P n) n (m n)/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0) := by
  let K := boundedLocalShiftCostConstant C
  have hK : 0 ≤ K := boundedLocalShiftCostConstant_nonneg hC
  have hs := familyScale_tendsto_one hv
  have hcoef := (tendsto_const_nhds (x := K)).div (hs.pow 2) (by norm_num : (1 : ℝ)^2 ≠ 0)
  have hupper := hcoef.mul (hU.add (hV.const_mul (Real.exp (11/2))))
  norm_num only [mul_zero, add_zero] at hupper
  apply squeeze_zero' _ _ hupper
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
    have hCost : 0 ≤ localShiftComparisonCost (C*Real.log (m n : ℝ))
        (1/Real.sqrt (Real.log (m n : ℝ))) (normalMaximumDensity (m n) (normalMaxThreshold (m n))) := by
      unfold localShiftComparisonCost
      positivity
    exact div_nonneg (mul_nonneg hCost (familyShiftSecondMoments_nonneg _ _ _))
      (familyRareLowerScale_pos (P n) hn (hm n)).le
  · filter_upwards [hmTop.eventually (eventually_localShiftComparisonCost_le_log C),
      eventually_ge_atTop 1] with n hnCost hn
    have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hMom := add_le_add (familyObservationShift_sq_integral_le (P n) n (m n))
      (familyGaussianShift_sq_integral_le (P n) (m n))
    rw [dimensionLog_eq_one_add_log (by have := hm n; omega)] at hMom
    have hprod := mul_le_mul hnCost hMom (familyShiftSecondMoments_nonneg _ _ _) (mul_nonneg hK hL.le)
    have hdiv := div_le_div_of_nonneg_right hprod (familyRareLowerScale_pos (P n) hn (hm n)).le
    exact hdiv.trans_eq (rare_moment_cost_identity hN (P n).variance_pos.le (P n).scale_pos.ne'
      (familyRareLowerScale_pos (P n) hn (hm n)).ne')

theorem tendsto_familyRare_rademacher_error {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0))
    (hScale : Tendsto (fun n : ℕ => familyRareLowerScale (P n) n (m n)/boundedLowerScale n (m n)) atTop atTop) :
    Tendsto (fun n : ℕ => rademacherLocalError n (m n)/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0) := by
  have hh := (tendsto_rademacherLocalError_div_boundedLowerScale hmTop hsmall).mul
    (tendsto_inv_atTop_zero.comp hScale)
  simp only [mul_zero] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop 1, eventually_boundedLowerScale_pos hmTop] with n hn hd
  dsimp only [Function.comp_apply]
  field_simp [hd.ne', (familyRareLowerScale_pos (P n) hn (hm n)).ne']

theorem tendsto_familyRare_discrepancy_div_scale {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ}
    [∀ n, NeZero (m n)] (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ)) /
      familyRareShiftScale (P n) n) atTop (𝓝 0))
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0))
    (hScale : Tendsto (fun n : ℕ => familyRareLowerScale (P n) n (m n)/boundedLowerScale n (m n)) atTop atTop)
    (hU : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(P n).amplitude^2*
      (((n : ℝ)*(P n).theta)^2+(n : ℝ)*(P n).theta)/n/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0))
    (hV : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(P n).variance*(1+Real.log (m n : ℝ)) /
      familyRareLowerScale (P n) n (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n)) /
      familyRareLowerScale (P n) n (m n)) atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  obtain ⟨C, hC, hCB⟩ := eventually_normalMaximumDensity_local_derivative_bound
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  let disc := fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))
  let lead := fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n))*familyShiftMeanDifference (P n) n (m n)
  have hlead := tendsto_familyRare_leading_comparison_ratio hm hmTop hk hcover hv hcoef
  have hE := (tendsto_familyRare_rademacher_error hm hmTop hsmall hScale).const_mul (8*Real.exp 4)
  have hR := tendsto_familyRare_local_remainder C hC.le hm hmTop hv hU hV
  have hupper := hE.add hR
  simp only [mul_zero, zero_add] at hupper
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(disc n-lead n)/familyRareLowerScale (P n) n (m n)| ≤
      8*Real.exp 4*(rademacherLocalError n (m n)/familyRareLowerScale (P n) n (m n)) +
        localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
          (normalMaximumDensity (m n) (normalMaxThreshold (m n)))*familyShiftSecondMoments (P n) n (m n) /
            familyRareLowerScale (P n) n (m n) := by
    filter_upwards [hmTop.eventually hCB, hmTop.eventually eventually_normalTail_local_mass_bound,
      eventually_boundedFamily_rademacher_conditions hmTop hsmall, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1] with n hnB hnMass hnRad hnL hn1
    have hh := familyLocal_master_comparison (P n) hn1 hnL hnMass hnRad.1 hnRad.2
      (mul_nonneg hC.le (by linarith)) hnB
    have hd := familyRareLowerScale_pos (P n) hn1 (hm n)
    have hdiv := div_le_div_of_nonneg_right hh hd.le
    rw [abs_div, abs_of_pos hd]
    convert hdiv using 1
    ring
  have habs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hupper
  have herr : Tendsto (fun n => (disc n-lead n)/familyRareLowerScale (P n) n (m n)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using habs)
  have hh := hlead.add herr
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  dsimp only [disc, lead]
  ring

end
end RectangleCLT.Companion.SplitV4
