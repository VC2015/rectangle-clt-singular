import RectangleCLTCompanion.SplitV4.Printed.LowerConstruction
import RectangleCLTCompanion.SplitV4.FourthMomentOptimal
import RectangleCLTCompanion.SplitV4.SparseMomentOptimal

/-! Full T5 and T8 optimality assemblies using the literal lower model
and detecting threshold. Uniform upper estimates are the separately
certified polynomial comparison statements. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem eventually_fourthFamily_distance_le_symmetricWorstDistance_printed {m : ℕ → ℕ}
    (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0))
    {B : ℝ} (hB : 2 ≤ B) :
    ∀ᶠ n : ℕ in atTop,
      familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n := by
  have h := fourthMomentLower_printed hmTop hrate
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
theorem fourthMoment_fixedEnvelope_optimal_printed {m : ℕ → ℕ}
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
  have h := fourthMomentLower_printed hmTop hrate
  refine ⟨c, polynomialFourthUniformConstant B, hc,
    polynomialFourthUniformConstant_pos (by linarith), ?_⟩
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds hcLim),
    eventually_fourthFamily_distance_le_symmetricWorstDistance_printed hmTop hrate hB,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with n hnOrth hnModel hnm hnn
  have hr := fourthMomentLowerRate_pos hnn hnm
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
    (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
    (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
    (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*printedNormalMaxThreshold (m n)))
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
theorem fourthMomentOptimal_printed {m : ℕ → ℕ} (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0)) :
    FourthMomentLowerConstruction_printed m ∧ ∀ B : ℝ, 2 ≤ B →
      ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ᶠ n : ℕ in atTop,
        c*fourthMomentLowerRate n (m n) ≤ polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ≤ polynomialWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialWorstDistance.{0} 4 B (m n*m n) n ≤ C*fourthMomentLowerRate n (m n) := by
  exact ⟨fourthMomentLower_printed hmTop hrate, fun _ hB => fourthMoment_fixedEnvelope_optimal_printed hmTop hrate hB⟩

theorem eventually_sparseFamily_distance_le_symmetricWorstDistance_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n := by
  have h := sparseMomentLower_printed hq hB hmTop hK hLog hRate
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

theorem sparseMoment_uniform_comparison_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
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
  have h := sparseMomentLower_printed hq hB hmTop hK hLog hRate
  have hc : sparseMomentLowerCoefficient q < sparseMomentLowerConstant q := half_lt_self h.positiveConstant
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds hc),
    eventually_sparseFamily_distance_le_symmetricWorstDistance_printed hq hB hmTop hK hLog hRate,
    eventually_sparse_coordinate_le_rate hB hmTop hK,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1]
    with n hnOrth hnModel hnCoordinate hnM hn1
  have hr := sparseMomentLowerRate_pos (q := q) hn1 hnM (hB n)
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
    (sumVector (familyNormalizedObservations (sparseFamilyParameters q n (m n) (B n))))
    (familyGaussianSquareFactor (sparseFamilyParameters q n (m n) (B n)) (m n))
    (familyOrthant (m n*m n) ((sparseFamilyParameters q n (m n) (B n)).scale*printedNormalMaxThreshold (m n)))
  have hmodel : sparseMomentLowerCoefficient q*sparseMomentLowerRate n (m n) q (B n) ≤
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) := by
    apply (le_div_iff₀ hr).mp
    exact hnOrth.trans (div_le_div_of_nonneg_right hrect hr.le)
  refine ⟨hmodel, hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact polynomialWorstDistance_sparse_le hp hn1 hq (by have := hB n; linarith) hnCoordinate

/-- Full Theorem 8 (`lower:sparse`). Both positive comparison coefficients
are fixed functions of q before all dimensions, envelope and sample sequences. -/
theorem sparseMomentOptimal_printed {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop)
    (hLog : Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0))
    (hRate : Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0)) :
    SparseMomentLowerConstruction_printed q B m ∧
    0 < sparseMomentLowerCoefficient q ∧ 0 < sparseMomentUpperCoefficient q ∧ ∀ᶠ n : ℕ in atTop,
      sparseMomentLowerCoefficient q*sparseMomentLowerRate n (m n) q (B n) ≤
        familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ∧
      familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ≤ polynomialWorstDistance.{0} q (B n) (m n*m n) n ∧
      polynomialWorstDistance.{0} q (B n) (m n*m n) n ≤
        sparseMomentUpperCoefficient q*sparseMomentLowerRate n (m n) q (B n) := by
  exact ⟨sparseMomentLower_printed hq hB hmTop hK hLog hRate,
    sparseMomentLowerCoefficient_pos q, sparseMomentUpperCoefficient_pos q,
    sparseMoment_uniform_comparison_printed hq hB hmTop hK hLog hRate⟩

end
end RectangleCLT.Companion.SplitV4.Printed
