import RectangleCLTArxivV1.LowerBoundedCalibration
import RectangleCLTArxivV1.LowerUnmaskedConstruction

/-! Theorem 4: actual bounded symmetric observations with the prescribed
Gaussian-width profile, including one leading coordinate. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerBoundedSequence (B : ℕ → ℝ) (m : ℕ → ℕ) : ℕ → SymmetricFamilyParameters :=
  lowerUnmaskedSequence (fun n => B n-1) m

theorem theorem4_bounded_symmetric_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) →
      (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      Tendsto (fun n : ℕ => B n*independentAbsGaussianMean (r n)*dimensionLog (r n*m n)/Real.sqrt n)
        atTop (𝓝 0) →
      ∃ P : ℕ → SymmetricFamilyParameters,
        P = lowerBoundedSequence B m ∧
        Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))/
          independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
        ∀ᶠ n : ℕ in atTop,
          LowerRectangularFamilyProperties (P n) n (r n) (m n) ∧
          (∀ i : Fin n, ∀ z : Fin n → LowerFamilySeed (r n) (m n),
            ‖lowerFamilyRawObservations (P n) i z‖ ≤ B n) ∧
          c*(B n*gaussianMaximumMean (lowerFamilyGaussianFactor (P n) (r n) (m n))*
            dimensionLog (r n*m n)/Real.sqrt n) ≤ lowerFamilyComparisonDistance (P n) n (r n) (m n) := by
  obtain ⟨c,hc,hDetect⟩ := exists_lowerUnmaskedSequence_detection_constant
  refine ⟨c/12,by positivity,?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hsmall
  let a : ℕ → ℝ := fun n => B n-1
  have ha : ∀ᶠ n in atTop, 1 ≤ a n := Eventually.of_forall (fun n => by dsimp [a]; linarith [hB n])
  have hraw := tendsto_lower_bounded_raw_width_scale hB hr hm hsmall
  have hprofile := lowerUnmaskedSequence_width_profile hr hm hmTop ha hraw
  have hupper := hprofile.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2))
  have hdet := hDetect a r m hr hm hrm hmTop ha hraw
  have hlog : Tendsto (fun n => Real.log (m n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  refine ⟨lowerUnmaskedSequence a m,rfl,hprofile,?_⟩
  filter_upwards [eventually_lowerUnmaskedSequence_properties a hr hm,hdet,hupper,
    eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hraw,
    hlog.eventually (eventually_ge_atTop 1)] with n hnProps hnDetect hnUpper hnFields hnL
  have hgpos : 0 < independentAbsGaussianMean (r n) :=
    (by positivity : 0 < Real.sqrt (2/Real.pi)).trans_le (independentAbsGaussianMean_lower (hr n))
  have hG := (div_le_iff₀ hgpos).mp hnUpper
  have hTarget := lower_bounded_target_le_twelve_scale (N := (n : ℝ)) (hB n)
    (gaussianMaximumMean_nonneg _) (independentAbsGaussianMean_nonneg _) hG
    (show 0 ≤ Real.log (m n : ℝ) by linarith) (zero_le_one.trans
      (log_exp_mul_nat_ge_one (by nlinarith [hr n,hm n] : 1 ≤ r n*m n)))
    (lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL)
  refine ⟨hnProps,?_,?_⟩
  · intro i z
    have hh := lowerFamilyObservation_envelope (lowerUnmaskedSequence a m n) (z i)
    change ‖lowerFamilyObservation (lowerUnmaskedSequence a m n) (z i)‖ ≤ B n
    apply hh.trans
    rw [hnFields.2.1]
    have hs := familyScale_le_one (lowerUnmaskedSequence a m n)
    dsimp [a]
    linarith
  · have hh := mul_le_mul_of_nonneg_left hTarget (show 0 ≤ c/12 by positivity)
    have he : (c/12)*(12*lowerWidthScale (B n-1) (Real.log (m n : ℝ))
        (independentAbsGaussianMean (r n)) n) =
        c*lowerWidthScale (a n) (Real.log (m n : ℝ)) (independentAbsGaussianMean (r n)) n := by
      dsimp [a]
      ring
    exact (hh.trans_eq he).trans hnDetect.2

end
end RectangleCLTArxivV1
