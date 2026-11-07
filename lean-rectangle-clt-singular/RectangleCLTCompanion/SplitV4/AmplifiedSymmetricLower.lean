import RectangleCLTCompanion.SplitV4.SymmetricFamilyAmplification

/-! Actual orthant comparison for arbitrary unmasked amplitudes, obtained by
exact amplitude transport from the bounded family's genuine scalar shifts. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def amplifiedSymmetricLowerScale (P : SymmetricFamilyParameters) (n m : ℕ) : ℝ :=
  familyShiftAmplification P (boundedFamilyParameters n m) * boundedLowerScale n m

theorem amplifiedSymmetricLowerScale_pos (P : SymmetricFamilyParameters) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 2 ≤ m) : 0 < amplifiedSymmetricLowerScale P n m := by
  unfold amplifiedSymmetricLowerScale boundedLowerScale
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  exact mul_pos (familyShiftAmplification_pos _ _)
    (div_pos (Real.rpow_pos_of_pos hL _) (by positivity))

theorem eventually_amplified_local_remainder_bound {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)] (C : ℝ) (hC : 0 ≤ C)
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0))
    (hθ : ∀ᶠ n : ℕ in atTop, (P n).theta = (boundedFamilyParameters n (m n)).theta)
    (hπ : ∀ᶠ n : ℕ in atTop, (P n).pi = (boundedFamilyParameters n (m n)).pi) :
    ∀ᶠ n : ℕ in atTop,
      localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
        (normalMaximumDensity (m n) (normalMaxThreshold (m n))) * familyShiftSecondMoments (P n) n (m n) /
          amplifiedSymmetricLowerScale (P n) n (m n) ≤
      (2*boundedLocalShiftCostConstant C*(3+4*Real.exp (11/2))) *
        (familyShiftAmplification (P n) (boundedFamilyParameters n (m n)) *
          Real.sqrt (Real.log (m n : ℝ)^3/n)) := by
  let K := boundedLocalShiftCostConstant C
  let M := 3+4*Real.exp (11/2)
  have hK : 0 ≤ K := boundedLocalShiftCostConstant_nonneg hC
  filter_upwards [hmTop.eventually (eventually_localShiftComparisonCost_le_log C),
    eventually_boundedFamily_shift_second_moment_budget hm hmTop hsmall, hθ, hπ,
    eventually_ge_atTop 1] with n hcost hmoment hnθ hnπ hn
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hm n)
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hd : 0 < boundedLowerScale n (m n) := by unfold boundedLowerScale; positivity
  have hk := familyShiftAmplification_pos (P n) (boundedFamilyParameters n (m n))
  have hprod := mul_le_mul hcost hmoment (familyShiftSecondMoments_nonneg _ _ _)
    (mul_nonneg hK hL.le)
  have hbase := mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right hprod hd.le) hk.le
  rw [familyShiftSecondMoments_amplification _ _ hnθ hnπ]
  unfold amplifiedSymmetricLowerScale
  calc
    _ = familyShiftAmplification (P n) (boundedFamilyParameters n (m n)) *
        (localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
          (normalMaximumDensity (m n) (normalMaxThreshold (m n))) *
            familyShiftSecondMoments (boundedFamilyParameters n (m n)) n (m n) / boundedLowerScale n (m n)) := by
      field_simp [hd.ne', hk.ne']
      ring
    _ ≤ familyShiftAmplification (P n) (boundedFamilyParameters n (m n)) *
        ((K*Real.log (m n : ℝ))*(M*Real.log (m n : ℝ)^2/n)/boundedLowerScale n (m n)) := hbase
    _ = _ := by
      rw [show (K*Real.log (m n : ℝ))*(M*Real.log (m n : ℝ)^2/n)/boundedLowerScale n (m n) =
        K*M*((Real.log (m n : ℝ)^3/n)/(Real.log (m n : ℝ)^(3/2 : ℝ)/(2*Real.sqrt n))) by
          unfold boundedLowerScale; ring]
      rw [lower_cubic_remainder_ratio_identity hL hN]
      dsimp only [K, M]
      ring

/-- Genuine orthant discrepancy limit under primitive amplitude/probability
conditions; the probability comparison itself is proved from F.1 and F.2. -/
theorem tendsto_amplifiedFamily_discrepancy_div_scale {P : ℕ → SymmetricFamilyParameters}
    {m : ℕ → ℕ} [∀ n, NeZero (m n)]
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0))
    (hθ : ∀ᶠ n : ℕ in atTop, (P n).theta = (boundedFamilyParameters n (m n)).theta)
    (hπ : ∀ᶠ n : ℕ in atTop, (P n).pi = (boundedFamilyParameters n (m n)).pi)
    (hk : ∀ᶠ n : ℕ in atTop, 1 ≤ familyShiftAmplification (P n) (boundedFamilyParameters n (m n)))
    (hksmall : Tendsto (fun n : ℕ => familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*
      Real.sqrt (Real.log (m n : ℝ)^3/n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n)) /
      amplifiedSymmetricLowerScale (P n) n (m n)) atTop (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
  obtain ⟨C, hC, hCB⟩ := eventually_normalMaximumDensity_local_derivative_bound
  have hlog : Tendsto (fun n : ℕ => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  let disc := fun n => familyShiftedCDFDifference (P n) n (m n) (normalMaxThreshold (m n))
  let lead := fun n => normalMaximumDensity (m n) (normalMaxThreshold (m n)) *
    familyShiftMeanDifference (P n) n (m n)
  have hlead : Tendsto (fun n => lead n / amplifiedSymmetricLowerScale (P n) n (m n)) atTop
      (𝓝 (Real.sqrt 2*Real.exp (-1))) := by
    apply (tendsto_boundedFamily_leading_comparison_ratio hm hmTop hsmall).congr'
    filter_upwards [hθ, hπ, eventually_boundedLowerScale_pos hmTop] with n hnθ hnπ hd
    dsimp only [lead]
    rw [familyShiftMeanDifference_amplification _ _ hnθ hnπ]
    unfold amplifiedSymmetricLowerScale
    field_simp [hd.ne', (familyShiftAmplification_pos (P n) (boundedFamilyParameters n (m n))).ne']
    ring
  have hE := (tendsto_rademacherLocalError_div_boundedLowerScale hmTop hsmall).const_mul (8*Real.exp 4)
  have hR := hksmall.const_mul (2*boundedLocalShiftCostConstant C*(3+4*Real.exp (11/2)))
  have hupper := hE.add hR
  simp only [mul_zero, zero_add] at hupper
  have hbound : ∀ᶠ n : ℕ in atTop,
      |(disc n-lead n)/amplifiedSymmetricLowerScale (P n) n (m n)| ≤
      8*Real.exp 4*(rademacherLocalError n (m n)/boundedLowerScale n (m n)) +
        (2*boundedLocalShiftCostConstant C*(3+4*Real.exp (11/2))) *
          (familyShiftAmplification (P n) (boundedFamilyParameters n (m n))*Real.sqrt (Real.log (m n : ℝ)^3/n)) := by
    filter_upwards [hmTop.eventually hCB, hmTop.eventually eventually_normalTail_local_mass_bound,
      eventually_boundedFamily_rademacher_conditions hmTop hsmall, hlog.eventually (eventually_ge_atTop 1),
      eventually_ge_atTop 1, eventually_amplified_local_remainder_bound C hC.le hm hmTop hsmall hθ hπ,
      hk, eventually_boundedLowerScale_pos hmTop] with n hnB hnMass hnRad hnL hn1 hnR hnk hnd
    have hd := amplifiedSymmetricLowerScale_pos (P n) hn1 (hm n)
    have hh := familyLocal_master_comparison (P n) hn1 hnL hnMass hnRad.1 hnRad.2
      (mul_nonneg hC.le (by linarith)) hnB
    have hdiv := div_le_div_of_nonneg_right hh hd.le
    have hE0 : 0 ≤ 8*Real.exp 4*rademacherLocalError n (m n) := by
      unfold rademacherLocalError
      have := moderateTailRemainderConstant_bounds.1
      positivity
    have hden : boundedLowerScale n (m n) ≤ amplifiedSymmetricLowerScale (P n) n (m n) := by
      unfold amplifiedSymmetricLowerScale
      nlinarith only [mul_nonneg (sub_nonneg.mpr hnk) hnd.le]
    have he := div_le_div_of_nonneg_left hE0 hnd hden
    rw [abs_div, abs_of_pos hd]
    calc
      _ ≤ (8*Real.exp 4*rademacherLocalError n (m n) +
        localShiftComparisonCost (C*Real.log (m n : ℝ)) (1/Real.sqrt (Real.log (m n : ℝ)))
          (normalMaximumDensity (m n) (normalMaxThreshold (m n))) * familyShiftSecondMoments (P n) n (m n)) /
          amplifiedSymmetricLowerScale (P n) n (m n) := hdiv
      _ = _ := add_div _ _ _
      _ ≤ _ := (add_le_add he hnR).trans_eq (by ring)
  have habs := squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) hbound hupper
  have herr : Tendsto (fun n => (disc n-lead n)/amplifiedSymmetricLowerScale (P n) n (m n)) atTop (𝓝 0) :=
    tendsto_iff_norm_sub_tendsto_zero.mpr (by simpa only [sub_zero, Real.norm_eq_abs] using habs)
  have hh := hlead.add herr
  simp only [add_zero] at hh
  convert hh using 1
  funext n
  dsimp only [disc, lead]
  ring

end
end RectangleCLT.Companion.SplitV4
