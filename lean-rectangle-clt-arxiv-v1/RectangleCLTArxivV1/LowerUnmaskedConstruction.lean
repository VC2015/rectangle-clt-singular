import RectangleCLTArxivV1.LowerUnmaskedSequenceCalibration

/-! Actual construction and detection, before choosing a moment envelope. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem eventually_lowerUnmaskedSequence_count {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop, (n : ℝ)*(lowerUnmaskedSequence a m n).theta = Real.log (m n : ℝ)/2 := by
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall,eventually_ge_atTop 1]
    with n hnFields hn
  rw [hnFields.1]
  exact lowerUnmasked_count_identity hn

theorem lowerUnmaskedSequence_width_profile {a : ℕ → ℝ} {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean (r n)) n) atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerUnmaskedSequence a m n) (r n) (m n))/
      independentAbsGaussianMean (r n)) atTop (𝓝 1) :=
  lowerFamilyGaussianMaximumMean_width_profile hr (fun n => by have := hm n; omega)
    (tendsto_lowerUnmaskedSequence_variance hr hm hmTop ha hsmall)
    (tendsto_lowerUnmaskedSequence_rare_width hr hm hmTop ha hsmall)

theorem lowerUnmaskedSequence_one_width_tendsto {a : ℕ → ℝ} {m : ℕ → ℕ}
    (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (ha : ∀ᶠ n in atTop, 1 ≤ a n)
    (hsmall : Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
      (independentAbsGaussianMean 1) n) atTop (𝓝 0)) :
    Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerUnmaskedSequence a m n) 1 (m n)))
      atTop (𝓝 (Real.sqrt (2/Real.pi))) :=
  lowerFamilyGaussianMaximumMean_one_tendsto (fun n => by have := hm n; omega)
    (tendsto_lowerUnmaskedSequence_variance (r := fun _ => 1) (fun _ => by norm_num) hm hmTop ha hsmall)
    (tendsto_lowerUnmaskedSequence_rare_width (r := fun _ => 1) (fun _ => by norm_num) hm hmTop ha hsmall)

theorem eventually_lowerUnmaskedSequence_properties (a : ℕ → ℝ) {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) :
    ∀ᶠ n : ℕ in atTop, LowerRectangularFamilyProperties (lowerUnmaskedSequence a m n) n (r n) (m n) := by
  filter_upwards [eventually_ge_atTop 1] with n hn
  exact lemma_lower_family_properties _ hn (hr n) (hm n)

/-- One constant detects all unmasked moment calibrations, for the actual
constructed observations and their actual Gaussian covariance factors. -/
theorem exists_lowerUnmaskedSequence_detection_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ (a : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      (∀ᶠ n in atTop, 1 ≤ a n) →
      Tendsto (fun n : ℕ => lowerWidthScale (a n) (Real.log (m n : ℝ))
        (independentAbsGaussianMean (r n)) n) atTop (𝓝 0) →
      ∀ᶠ n : ℕ in atTop,
        c*lowerWidthScale (a n) (Real.log (m n : ℝ)) (independentAbsGaussianMean (r n)) n ≤
          lowerFamilyShiftedCDFDifference (lowerUnmaskedSequence a m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c*lowerWidthScale (a n) (Real.log (m n : ℝ)) (independentAbsGaussianMean (r n)) n ≤
          lowerFamilyComparisonDistance (lowerUnmaskedSequence a m n) n (r n) (m n) := by
  obtain ⟨c,hc,hDetect⟩ := exists_lowerFamily_unmasked_width_detection_constant
  refine ⟨c,hc,?_⟩
  intro a r m _ _ hr hm hrm hmTop ha hsmall
  have haP : ∀ᶠ n in atTop, 1 ≤ (lowerUnmaskedSequence a m n).amplitude := by
    filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall,ha] with n hn hna
    rwa [hn.2.1]
  have hh := hDetect (lowerUnmaskedSequence a m) r m hr hm hrm hmTop haP
    (eventually_lowerUnmaskedSequence_count hr hm hmTop ha hsmall)
    (Eventually.of_forall (lowerUnmaskedSequence_pi a m))
    (tendsto_lowerUnmaskedSequence_variance hr hm hmTop ha hsmall)
    (tendsto_lowerUnmaskedSequence_widthScale hr hm hmTop ha hsmall)
  filter_upwards [hh,eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hsmall] with n hn hnFields
  simpa only [lowerFamilyWidthScale,lowerWidthScale,hnFields.2.1] using hn

end
end RectangleCLTArxivV1
