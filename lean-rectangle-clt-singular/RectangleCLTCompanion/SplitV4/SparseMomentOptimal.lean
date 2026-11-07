import RectangleCLTCompanion.SplitV4.SparseMomentLower
import RectangleCLTCompanion.SplitV4.FourthMomentOptimal

/-! Full Theorem 8: actual sparse lower observations and both matching suprema. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseMomentLowerCoefficient (q : ℝ) : ℝ := sparseMomentLowerConstant q/2
def sparseMomentUpperCoefficient (q : ℝ) : ℝ := 2*polynomialUniversalConstant q

theorem sparseMomentLowerCoefficient_pos (q : ℝ) : 0 < sparseMomentLowerCoefficient q :=
  half_pos (sparseMomentLowerConstant_pos q)

theorem sparseMomentUpperCoefficient_pos (q : ℝ) : 0 < sparseMomentUpperCoefficient q :=
  mul_pos (by norm_num) (zero_lt_one.trans_le (one_le_polynomialUniversalConstant q))

theorem eventually_sparse_coordinate_le_rate {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop) :
    ∀ᶠ n : ℕ in atTop,
      polynomialCoordinateRate n (m n*m n) (B n) ≤ sparseMomentLowerRate n (m n) q (B n) := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hK' : Tendsto (fun n => sparseLowerK n (ell n) q (B n)) atTop atTop := by
    apply hK.congr'
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    exact sparseMomentK_eq n (m n) hn q (B n)
  have hUR : Tendsto (fun n => polynomialCoordinateRate n (m n*m n) (B n)/
      sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0) := by
    apply (tendsto_sparseLower_coordinate_div_rate ell B q he hK').congr'
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2)] with n hn
    rw [sparseMomentLowerRate_eq _ _ hn]
    unfold polynomialCoordinateRate
    rw [dimensionLog_square _ (by omega)]
  filter_upwards [hUR.eventually (eventually_le_nhds (by norm_num : (0 : ℝ) < 1)),
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hn hnM hn1
  exact (div_le_one (sparseMomentLowerRate_pos hn1 hnM (hB n))).mp hn

theorem eventually_sparseFamily_distance_le_symmetricWorstDistance {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n := by
  have h := sparseMomentLower hq hB hmTop hK hLog hRate
  filter_upwards [h.properties, h.polynomialClass, h.matchingGaussianCovariance] with n hnProps hnClass hnCov
  let P := sparseFamilyParameters q n (m n) (B n)
  have hA : familyGaussianSquareFactor P (m n)*(familyGaussianSquareFactor P (m n)).transpose =
      covariance (familyArrayLaw P n (m n)) (normalizedObservationSum (familyRawObservations P)) := by
    rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum]
    exact hnCov
  have hh := rectangleDistance_le_polynomialSymmetricWorstDistance (familyArrayLaw P n (m n))
    (familyRawObservations P) (familyGaussianSquareFactor P (m n)) hnClass hnProps.centrallySymmetric hA
  rw [← familyNormalizedObservations_sum_eq_normalizedObservationSum] at hh
  exact hh

theorem sparseMoment_uniform_comparison {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      sparseMomentLowerCoefficient q*sparseMomentLowerRate n (m n) q (B n) ≤
        familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ∧
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ≤ polynomialWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialWorstDistance.{0} q (B n) (m n*m n) n ≤
        sparseMomentUpperCoefficient q*sparseMomentLowerRate n (m n) q (B n) := by
  have h := sparseMomentLower hq hB hmTop hK hLog hRate
  have hc : sparseMomentLowerCoefficient q < sparseMomentLowerConstant q := half_lt_self h.positiveConstant
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds hc),
    eventually_sparseFamily_distance_le_symmetricWorstDistance hq hB hmTop hK hLog hRate,
    eventually_sparse_coordinate_le_rate hB hmTop hK,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with n hnOrth hnModel hnCoordinate hnM hn1
  have hr := sparseMomentLowerRate_pos (q := q) hn1 hnM (hB n)
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
    (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
    (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
    (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*normalMaxThreshold (m n)))
  have hmodel : sparseMomentLowerCoefficient q*sparseMomentLowerRate n (m n) q (B n) ≤
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) := by
    apply (le_div_iff₀ hr).mp
    exact hnOrth.trans (div_le_div_of_nonneg_right hrect hr.le)
  refine ⟨hmodel, hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact polynomialWorstDistance_sparse_le hp hn1 hq (by have := hB n; linarith) hnCoordinate

/-- Full Theorem 8 (`lower:sparse`). Both positive comparison coefficients
are fixed functions of q before all dimensions, envelope and sample sequences. -/
theorem sparseMomentOptimal {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction q B m ∧
    0 < sparseMomentLowerCoefficient q ∧ 0 < sparseMomentUpperCoefficient q ∧ ∀ᶠ n : ℕ in atTop,
      sparseMomentLowerCoefficient q*sparseMomentLowerRate n (m n) q (B n) ≤
        familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ∧
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ≤ polynomialWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialWorstDistance.{0} q (B n) (m n*m n) n ≤
        sparseMomentUpperCoefficient q*sparseMomentLowerRate n (m n) q (B n) := by
  exact ⟨sparseMomentLower hq hB hmTop hK hLog hRate,
    sparseMomentLowerCoefficient_pos q, sparseMomentUpperCoefficient_pos q,
    sparseMoment_uniform_comparison hq hB hmTop hK hLog hRate⟩

end
end RectangleCLT.Companion.SplitV4
