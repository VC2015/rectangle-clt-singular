import RectangleCLTArxivV1.LowerMaskedWidthRegime

/-! Signed detecting orthants for the actual masked model. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem tendsto_lowerFamilyMasked_reverse_mean_ratio
    {P : ℕ → SymmetricFamilyParameters} {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hk : Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop)
    (hcover : Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop)
    (hv : Tendsto (fun n => (P n).variance) atTop (𝓝 0))
    (hcoef : Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))/
      familyRareShiftScale (P n) n) atTop (𝓝 0)) :
    Tendsto (fun n => -familyShiftMeanDifference (P n) n (m n)/familyRareShiftScale (P n) n)
      atTop (𝓝 1) := by
  have hh := (tendsto_familyRare_observation_mean_ratio hk hcover hv).sub
    (Printed.tendsto_familyRare_gaussian_mean_ratio_printed_ui hm hmTop hv hcoef)
  simpa only [sub_zero,familyShiftMeanDifference,neg_sub,sub_div] using hh

theorem exists_lowerFamily_masked_width_detection_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (P : ℕ → SymmetricFamilyParameters) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      (∀ᶠ n in atTop, 1 ≤ lowerFamilyEffectiveAmplitude (P n) n (m n)) →
      Tendsto (fun n : ℕ => (n : ℝ)*(P n).theta) atTop atTop →
      (∀ᶠ n : ℕ in atTop, (P n).pi*Real.log (m n : ℝ) ≤ (n : ℝ)*(P n).theta) →
      Tendsto (fun n : ℕ => (m n : ℝ)*((P n).pi/2)^Nat.ceil (2*((n : ℝ)*(P n).theta))) atTop atTop →
      Tendsto (fun n => (P n).variance) atTop (𝓝 0) →
      Tendsto (fun n : ℕ => Real.sqrt (P n).variance*Real.sqrt (2*Real.log (m n : ℝ))/
        familyRareShiftScale (P n) n) atTop (𝓝 0) →
      Tendsto (fun n => lowerFamilyRareWidthScale (P n) n (r n)) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop,
        c*lowerFamilyRareWidthScale (P n) n (r n) ≤
          -lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerFamilyRareWidthScale (P n) n (r n) ≤ lowerFamilyComparisonDistance (P n) n (r n) (m n) := by
  obtain ⟨c,hc,hD⟩ := exists_leadingDensity_width_lower
  refine ⟨c/4,by positivity,?_⟩
  intro P r m _ _ hr hm hrm hmTop ha hk hpi hcover hv hcoef hsmall
  have hMean := (tendsto_lowerFamilyMasked_reverse_mean_ratio hm hmTop hk hcover hv hcoef).eventually
    (eventually_ge_nhds (by norm_num : (1/2 : ℝ) < 1))
  have hRem := tendsto_lowerFamilyMaskedMasterRemainder_div_width hr hm hrm hmTop ha
    (hk.eventually (eventually_ge_atTop 1)) hpi hsmall
  have hErr := hRem.eventually (eventually_le_nhds (show (0 : ℝ) < c/4 by positivity))
  have hRange := eventually_lowerFamily_masked_leading_range hr hm hrm hmTop ha hsmall
  filter_upwards [hMean,hErr,hRange,eventually_lowerFamily_master_comparison,eventually_ge_atTop 1]
    with n hnMean hnErr hnRange hnMaster hn
  have hbase := familyRareShiftScale_pos (P n) hn
  have hgap := (le_div_iff₀ hbase).mp hnMean
  have hgap0 : 0 ≤ -familyShiftMeanDifference (P n) n (m n) :=
    (mul_nonneg (by norm_num : (0 : ℝ) ≤ 1/2) hbase.le).trans hgap
  have hwidth := lowerFamilyRareWidthScale_pos (P n) hn (hr n)
  have herr := (div_le_iff₀ hwidth).mp hnErr
  have hd := hD (r n) (hr n)
  have hprod := mul_le_mul_of_nonneg_right hd hgap0
  have hprod2 := mul_le_mul_of_nonneg_left hgap
    (mul_nonneg hc.le (independentAbsGaussianMean_nonneg (r n)))
  have hid : (c*independentAbsGaussianMean (r n))*(1/2*familyRareShiftScale (P n) n) =
      (c/2)*lowerFamilyRareWidthScale (P n) n (r n) := by
    unfold lowerFamilyRareWidthScale
    ring
  have hmain : c/2*lowerFamilyRareWidthScale (P n) n (r n) ≤
      normalMaximumDensity (r n) (lowerLeadingThreshold (r n))*(-familyShiftMeanDifference (P n) n (m n)) := by
    rw [← hid]
    exact hprod2.trans hprod
  have hmaster := hnMaster (P n) (r n) (m n) (hr n) (by have := hm n; omega)
    hnRange (lowerLeadingThreshold (r n))
  change |lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n))-
    normalMaximumDensity (r n) (lowerLeadingThreshold (r n))*familyShiftMeanDifference (P n) n (m n)| ≤
      lowerFamilyMasterRemainder (P n) n (r n) (m n) at hmaster
  have hhi := (abs_le.mp hmaster).2
  have hdet : c/4*lowerFamilyRareWidthScale (P n) n (r n) ≤
      -lowerFamilyShiftedCDFDifference (P n) n (r n) (m n) (lowerLeadingThreshold (r n)) := by linarith
  refine ⟨hdet,hdet.trans ((neg_le_abs _).trans ?_)⟩
  exact abs_lowerFamilyShiftedCDFDifference_le_distance (P n) n (r n) (m n) (lowerLeadingThreshold (r n))

end
end RectangleCLTArxivV1
