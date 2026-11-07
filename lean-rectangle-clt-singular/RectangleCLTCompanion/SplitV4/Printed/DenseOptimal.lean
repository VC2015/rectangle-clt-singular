import RectangleCLTCompanion.SplitV4.Printed.DenseLower
import RectangleCLTCompanion.SplitV4.Printed.Polynomial
import RectangleCLTCompanion.SplitV4.FourthMomentOptimal

/-! Full Theorem 7 from the literal B/2 model, global printed lower
comparison and current printed conditional-transfer upper bound. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem printed_dense_uniform_upper {p n : ℕ} (hp : 1≤p) (hn : 1≤n)
    {q B : ℝ} (hq : 2<q) (hB : 1≤B) :
    polynomialWorstDistance.{0} q B p n≤polynomialEnvelopeTransferConstant*
      polynomialEnvelopeV n p B q*dimensionLog n^(1/2-1/q) := by
  have hC : 0≤polynomialEnvelopeTransferConstant := zero_le_one.trans one_le_polynomialEnvelopeTransferConstant
  have hR : 0≤polynomialEnvelopeTransferRate n p B q :=
    polynomialEnvelopeTransferRate_nonneg hn hp (zero_le_one.trans hB) q
  have hh : polynomialWorstDistance.{0} q B p n≤
      polynomialEnvelopeTransferConstant*polynomialEnvelopeTransferRate n p B q := by
    apply (polynomialWorstDistance_le_iff_modelBound q B p n (mul_nonneg hC hR)).mpr
    intro Ω mΩ μ hprob X A hdata hA
    exact (polynomialEnvelopeTransfer μ X hdata.measurable hdata.independent hp hn hB hq
      hdata.envelope_integrable hdata.envelope_moment hdata.centered hdata.average_second A hA).trans
        (mul_le_mul_of_nonneg_left (min_le_right _ _) hC)
  exact hh.trans_eq (by unfold polynomialEnvelopeTransferRate; ring)

theorem eventually_printedDense_distance_le_symmetricWorstDistance {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n)≤
      polynomialSymmetricWorstDistance.{0} q B (m n*m n) n := by
  have h := printedDenseLower hq hB hmTop hrate
  filter_upwards [h.properties,h.polynomialClass,h.matchingGaussianCovariance] with n hp hc hcov
  let P := printedDenseParameters q B n (m n)
  have hA : familyGaussianSquareFactor P (m n)*(familyGaussianSquareFactor P (m n)).transpose=
      covariance (familyArrayLaw P n (m n)) (normalizedObservationSum (familyRawObservations P)) := by
    rw [←familyNormalizedObservations_sum_eq_normalizedObservationSum]
    exact hcov
  have hh := rectangleDistance_le_polynomialSymmetricWorstDistance (familyArrayLaw P n (m n))
    (familyRawObservations P) (familyGaussianSquareFactor P (m n)) hc hp.centrallySymmetric hA
  rw [←familyNormalizedObservations_sum_eq_normalizedObservationSum] at hh
  exact hh

theorem printedDense_uniform_comparison {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    ∀ᶠ n in atTop,
      (printedDenseConstant q/2)*denseMomentLowerRate n (m n) q B≤
        polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q B (m n*m n) n≤polynomialWorstDistance.{0} q B (m n*m n) n ∧
      polynomialWorstDistance.{0} q B (m n*m n) n≤polynomialEnvelopeTransferConstant*
        denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  have h := printedDenseLower hq hB hmTop hrate
  filter_upwards [h.orthantLimit.eventually (eventually_ge_nhds (half_lt_self h.positiveConstant)),
    eventually_printedDense_distance_le_symmetricWorstDistance hq hB hmTop hrate,
    hmTop.eventually (eventually_ge_atTop 2),eventually_ge_atTop 1] with n hnOrth hnModel hmn hn
  have hr := printed_dense_rate_pos (q:=q) hn hmn hB
  have hrect := rectangleError_le_rectangleDistance
    (familyArrayLaw (printedDenseParameters q B n (m n)) n (m n))
    (sumVector (familyNormalizedObservations (printedDenseParameters q B n (m n))))
    (familyGaussianSquareFactor (printedDenseParameters q B n (m n)) (m n))
    (familyOrthant (m n*m n) ((printedDenseParameters q B n (m n)).scale*printedNormalMaxThreshold (m n)))
  have hlo : (printedDenseConstant q/2)*denseMomentLowerRate n (m n) q B≤
      familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n) := by
    apply (le_div_iff₀ hr).mp
    exact hnOrth.trans (div_le_div_of_nonneg_right hrect hr.le)
  refine ⟨hlo.trans hnModel,polynomialSymmetricWorstDistance_le _ _ _ _,?_⟩
  exact printed_dense_uniform_upper
    (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))) hn
    (by linarith : 2<q) (by linarith : 1≤B)

/-- Full literal dense statement, including the supremum consequences.
The displayed coefficients are fixed before the dimension sequence. -/
theorem printedDenseOptimal {m : ℕ → ℕ} {q B : ℝ}
    (hq : 4<q) (hB : 2≤B) (hmTop : Tendsto m atTop atTop)
    (hrate : Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0)) :
    PrintedDenseLowerConstruction q B m ∧
    (0:EReal)<liminf (fun n => ((familyComparisonDistance (printedDenseParameters q B n (m n)) n (m n)/
      denseMomentLowerRate n (m n) q B : ℝ):EReal)) atTop ∧
    0<printedDenseConstant q/2 ∧ 0<polynomialEnvelopeTransferConstant ∧
    ∀ᶠ n in atTop,
      (printedDenseConstant q/2)*denseMomentLowerRate n (m n) q B≤polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
      polynomialSymmetricWorstDistance.{0} q B (m n*m n) n≤polynomialWorstDistance.{0} q B (m n*m n) n ∧
      polynomialWorstDistance.{0} q B (m n*m n) n≤polynomialEnvelopeTransferConstant*
        denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  have h := printedDenseLower hq hB hmTop hrate
  refine ⟨h,?_,half_pos h.positiveConstant,zero_lt_one.trans_le one_le_polynomialEnvelopeTransferConstant,
    printedDense_uniform_comparison hq hB hmTop hrate⟩
  exact (show (0:EReal)<(printedDenseConstant q:EReal) by exact_mod_cast h.positiveConstant).trans_le h.distanceLiminf

theorem printedDenseOptimal_constant_first (q : ℝ) (hq : 4<q) :
    ∃ C : ℝ,0<C ∧ ∀ B : ℝ,2≤B → ∃ c : ℝ,0<c ∧ ∀ m : ℕ → ℕ,
      Tendsto m atTop atTop →
      Tendsto (fun n => denseMomentLowerRate n (m n) q B) atTop (𝓝 0) →
      ∀ᶠ n in atTop,
        c*denseMomentLowerRate n (m n) q B≤polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} q B (m n*m n) n≤polynomialWorstDistance.{0} q B (m n*m n) n ∧
        polynomialWorstDistance.{0} q B (m n*m n) n≤C*denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  refine ⟨polynomialEnvelopeTransferConstant,zero_lt_one.trans_le one_le_polynomialEnvelopeTransferConstant,?_⟩
  intro B hB
  refine ⟨printedDenseConstant q/2,half_pos (printedDenseConstant_pos q),?_⟩
  intro m hm hr
  exact printedDense_uniform_comparison hq hB hm hr

end
end RectangleCLT.Companion.SplitV4.Printed
