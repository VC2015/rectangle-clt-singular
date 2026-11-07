import RectangleCLTCompanion.SplitV4.FourthMomentLower
import RectangleCLTCompanion.SplitV4.SymmetricPolynomialUniform

/-! Theorem 5, including both fixed-envelope supremum consequences.
Both suprema are over actual probability models, and the lower model has
independent identically distributed centrally symmetric observations. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyNormalizedObservations_sum_eq_normalizedObservationSum
    (P : SymmetricFamilyParameters) (n m : ℕ) :
    sumVector (familyNormalizedObservations P (n := n) (m := m)) =
      normalizedObservationSum (familyRawObservations P) := by
  have h : familyNormalizedObservations P (n := n) (m := m) =
      normalizedSummands (familyRawObservations P) := by
    funext i z
    simp only [familyNormalizedObservations, normalizedSummands, one_div]
  rw [h, sumVector_normalizedSummands]

theorem eventually_fourthFamily_distance_le_symmetricWorstDistance {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0))
    {B : ℝ} (hB : 2 ≤ B) :
    ∀ᶠ n : ℕ in atTop,
      familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n := by
  have h := fourthMomentLower hmTop hrate
  filter_upwards [h.properties, h.polynomialClass, h.matchingGaussianCovariance] with n hnProps hnClass hnCov
  let P := fourthFamilyParameters n (m n)
  have hdata := hnClass.mono_envelope (by norm_num : (0 : ℝ) ≤ 4) (by norm_num : (0 : ℝ) ≤ 2) hB
  have hA : familyGaussianSquareFactor P (m n)*(familyGaussianSquareFactor P (m n)).transpose =
      covariance (familyArrayLaw P n (m n)) (normalizedObservationSum (familyRawObservations P)) := by
    rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum]
    exact hnCov
  have hh := rectangleDistance_le_polynomialSymmetricWorstDistance (familyArrayLaw P n (m n))
    (familyRawObservations P) (familyGaussianSquareFactor P (m n)) hdata hnProps.centrallySymmetric hA
  rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum] at hh
  exact hh

/-- Two-sided optimality, simultaneously for the full polynomial class
and the class restricted to centrally symmetric observations. -/
theorem fourthMoment_fixedEnvelope_optimal {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0))
    {B : ℝ} (hB : 2 ≤ B) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
      c*fourthMomentLowerRate n (m n) ≤ polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ≤ polynomialWorstDistance.{0} 4 B (m n*m n) n ∧
      polynomialWorstDistance.{0} 4 B (m n*m n) n ≤ C*fourthMomentLowerRate n (m n) := by
  let c : ℝ := 1/(4*Real.sqrt 2*Real.exp 1)
  have hc : 0 < c := by dsimp only [c]; positivity
  have hcLim : c < 1/(2*Real.sqrt 2*Real.exp 1) := by
    dsimp only [c]
    exact one_div_lt_one_div_of_lt (by positivity) (by
      have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
      have he := Real.exp_pos 1
      nlinarith)
  have h := fourthMomentLower hmTop hrate
  refine ⟨c, polynomialFourthUniformConstant B, hc,
    polynomialFourthUniformConstant_pos (by linarith), ?_⟩
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds hcLim),
    eventually_fourthFamily_distance_le_symmetricWorstDistance hmTop hrate hB,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with n hnOrth hnModel hnm hnn
  have hr := fourthMomentLowerRate_pos hnn hnm
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
    (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
    (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
    (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*normalMaxThreshold (m n)))
  have hmodel : c*fourthMomentLowerRate n (m n) ≤
      familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) := by
    apply (le_div_iff₀ hr).mp
    exact hnOrth.trans (div_le_div_of_nonneg_right hrect hr.le)
  refine ⟨hmodel.trans hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hu := polynomialWorstDistance_four_le.{0} hp hnn (by linarith : 1 ≤ B)
  exact hu.trans_eq (by unfold fourthMomentLowerRate; ring)

/-- Full Theorem 5 (`opt:q4-lower`), with the literal actual-law lower
construction and the two fixed-B optimality consequences. -/
theorem fourthMomentOptimal {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction m ∧ ∀ B : ℝ, 2 ≤ B →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        c*fourthMomentLowerRate n (m n) ≤ polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ≤ polynomialWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialWorstDistance.{0} 4 B (m n*m n) n ≤ C*fourthMomentLowerRate n (m n) := by
  exact ⟨fourthMomentLower hmTop hrate, fun _ hB => fourthMoment_fixedEnvelope_optimal hmTop hrate hB⟩

end
end RectangleCLT.Companion.SplitV4
