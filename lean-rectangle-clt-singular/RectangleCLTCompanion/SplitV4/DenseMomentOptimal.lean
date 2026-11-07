import RectangleCLTCompanion.SplitV4.DenseMomentLower
import RectangleCLTCompanion.SplitV4.FourthMomentOptimal

/-! Theorem 7: genuine fixed-B q>4 lower models and the stated uniform comparison. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem polynomialWorstDistance_envelope_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B) :
    polynomialWorstDistance.{0} q B p n ≤
      polynomialUniversalConstant q * polynomialEnvelopeV n p B q * dimensionLog n^(1/2-1/q) := by
  have hU : 0 ≤ polynomialUniversalConstant q := zero_le_one.trans (one_le_polynomialUniversalConstant q)
  have hh := polynomialMomentWorstDistanceCLT.{0} hp hn hq hB
  calc
    _ ≤ polynomialUniversalConstant q*min 1 (polynomialCombinedRate n p B q) := hh
    _ ≤ polynomialUniversalConstant q*polynomialEnvelopeTransferRate n p B q :=
      mul_le_mul_of_nonneg_left ((min_le_right _ _).trans (min_le_right _ _)) hU
    _ = _ := by unfold polynomialEnvelopeTransferRate; ring

theorem eventually_denseFamily_distance_le_symmetricWorstDistance {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q B (m n*m n) n := by
  have h := denseMomentLower hq hB hmTop hrate
  filter_upwards [h.properties, h.polynomialClass, h.matchingGaussianCovariance] with n hnProps hnClass hnCov
  let P := denseFamilyParameters q B n (m n)
  have hA : familyGaussianSquareFactor P (m n)*(familyGaussianSquareFactor P (m n)).transpose =
      covariance (familyArrayLaw P n (m n)) (normalizedObservationSum (familyRawObservations P)) := by
    rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum]
    exact hnCov
  have hh := rectangleDistance_le_polynomialSymmetricWorstDistance (familyArrayLaw P n (m n))
    (familyRawObservations P) (familyGaussianSquareFactor P (m n)) hnClass hnProps.centrallySymmetric hA
  rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum] at hh
  exact hh

theorem denseMoment_uniform_comparison {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4 < q) (hB : 2 ≤ B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*denseMomentLowerRate n (m n) q B ≤ polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ≤ polynomialWorstDistance.{0} q B (m n*m n) n ∧
      polynomialWorstDistance.{0} q B (m n*m n) n ≤
        polynomialUniversalConstant q*denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  let c := denseLowerConstant q B/2
  have h := denseMomentLower hq hB hmTop hrate
  have hc : 0 < c := half_pos h.positiveConstant
  have hcLim : c < denseLowerConstant q B := half_lt_self h.positiveConstant
  refine ⟨c, hc, ?_⟩
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds hcLim),
    eventually_denseFamily_distance_le_symmetricWorstDistance hq hB hmTop hrate,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hnOrth hnModel hnm hnn
  have hr := denseMomentLowerRate_pos (q := q) hnn hnm hB
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
    (sumVector (familyNormalizedObservations (denseFamilyParameters q B n (m n))))
    (familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n))
    (familyOrthant (m n*m n) ((denseFamilyParameters q B n (m n)).scale*normalMaxThreshold (m n)))
  have hmodel : c*denseMomentLowerRate n (m n) q B ≤
      familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) := by
    apply (le_div_iff₀ hr).mp
    exact hnOrth.trans (div_le_div_of_nonneg_right hrect hr.le)
  refine ⟨hmodel.trans hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hu := polynomialWorstDistance_envelope_le hp hnn (by linarith : 2 < q) (by linarith : 1 ≤ B)
  exact hu

/-- Full Theorem 7 (`lower:dense`). The upper coefficient depends only on q;
the positive lower coefficient depends only on q and B. -/
theorem denseMomentOptimal {m : ℕ → ℕ} {q B : ℝ} (hq : 4 < q) (hB : 2 ≤ B)
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    DenseMomentLowerConstruction q B m ∧
    (0 : EReal) < liminf (fun n : ℕ =>
      ((familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) /
        denseMomentLowerRate n (m n) q B : ℝ) : EReal)) atTop ∧
    0 < polynomialUniversalConstant q ∧ ∃ c : ℝ, 0 < c ∧ ∀ᶠ n : ℕ in atTop,
      c*denseMomentLowerRate n (m n) q B ≤ polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ≤ polynomialWorstDistance.{0} q B (m n*m n) n ∧
      polynomialWorstDistance.{0} q B (m n*m n) n ≤
        polynomialUniversalConstant q*denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  have h := denseMomentLower hq hB hmTop hrate
  refine ⟨h, ?_, zero_lt_one.trans_le (one_le_polynomialUniversalConstant q),
    denseMoment_uniform_comparison hq hB hmTop hrate⟩
  exact (show (0 : EReal) < (denseLowerConstant q B : EReal) by exact_mod_cast h.positiveConstant).trans_le h.distanceLiminf

end
end RectangleCLT.Companion.SplitV4
