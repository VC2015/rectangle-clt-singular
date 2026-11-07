import RectangleCLTCompanion.SplitV4.FourthMomentOptimal
import RectangleCLTCompanion.SplitV4.DenseMomentOptimal
import RectangleCLTCompanion.SplitV4.SparseMomentOptimal

/-! Public lower comparison constants chosen before every dimension sequence.
The previously frozen endpoints remain unchanged. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem eventually_mul_rate_le_of_quotient {e d r : ℕ → ℝ} {c C : ℝ}
    (hlim : Tendsto (fun n => e n/r n) atTop (𝓝 C)) (hc : c < C)
    (hdom : ∀ᶠ n : ℕ in atTop, e n ≤ d n) (hr : ∀ᶠ n : ℕ in atTop, 0 < r n) :
    ∀ᶠ n : ℕ in atTop, c*r n ≤ d n := by
  filter_upwards [hlim.eventually (eventually_ge_nhds hc), hdom, hr] with n hn he hrn
  exact (le_div_iff₀ hrn).mp (hn.trans (div_le_div_of_nonneg_right he hrn.le))

def fourthMomentLowerCoefficient : ℝ := 1/(4*Real.sqrt 2*Real.exp 1)

theorem fourthMomentLowerCoefficient_pos : 0 < fourthMomentLowerCoefficient := by
  unfold fourthMomentLowerCoefficient
  positivity

theorem fourthMomentLowerCoefficient_lt : fourthMomentLowerCoefficient < 1/(2*Real.sqrt 2*Real.exp 1) := by
  unfold fourthMomentLowerCoefficient
  apply one_div_lt_one_div_of_lt (by positivity)
  have hs := Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)
  have he := Real.exp_pos 1
  nlinarith

/-- Theorem 5 with an absolute positive lower coefficient and a B-dependent
upper coefficient, both chosen before all sample/dimension sequences. -/
theorem fourthMoment_uniform_constants :
    ∃ c : ℝ, 0 < c ∧ ∀ B : ℝ, 2 ≤ B → ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ → ℕ,
      Tendsto m atTop atTop →
      Tendsto (fun n : ℕ => fourthMomentLowerRate n (m n)) atTop (𝓝 0) →
      FourthMomentLowerConstruction m ∧ ∀ᶠ n : ℕ in atTop,
        c*fourthMomentLowerRate n (m n) ≤ familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) ∧
        familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) ≤ polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} 4 B (m n*m n) n ≤ polynomialWorstDistance.{0} 4 B (m n*m n) n ∧
        polynomialWorstDistance.{0} 4 B (m n*m n) n ≤ C*fourthMomentLowerRate n (m n) := by
  refine ⟨fourthMomentLowerCoefficient, fourthMomentLowerCoefficient_pos, ?_⟩
  intro B hB
  refine ⟨polynomialFourthUniformConstant B, polynomialFourthUniformConstant_pos (by linarith), ?_⟩
  intro m hmTop hRate
  have h := fourthMomentLower hmTop hRate
  have hr : ∀ᶠ n : ℕ in atTop, 0 < fourthMomentLowerRate n (m n) := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hnM hn
    exact fourthMomentLowerRate_pos hn hnM
  have hdom : ∀ᶠ n : ℕ in atTop,
      rectangleError (familyArrayLaw (fourthFamilyParameters n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (fourthFamilyParameters n (m n))))
        (familyGaussianSquareFactor (fourthFamilyParameters n (m n)) (m n))
        (familyOrthant (m n*m n) ((fourthFamilyParameters n (m n)).scale*normalMaxThreshold (m n))) ≤
      familyComparisonDistance (fourthFamilyParameters n (m n)) n (m n) :=
    Eventually.of_forall (fun _ => rectangleError_le_rectangleDistance _ _ _ _)
  have hlo := eventually_mul_rate_le_of_quotient h.orthantLimit fourthMomentLowerCoefficient_lt hdom hr
  refine ⟨h, ?_⟩
  filter_upwards [hlo, eventually_fourthFamily_distance_le_symmetricWorstDistance hmTop hRate hB,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hnL hnModel hnM hn
  refine ⟨hnL, hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hu := polynomialWorstDistance_four_le.{0} hp hn (by linarith : 1 ≤ B)
  exact hu.trans_eq (by unfold fourthMomentLowerRate; ring)

/-- Theorem 7: C_q is chosen before B; c_{q,B} is chosen before every
sample/dimension sequence and every actual model. -/
theorem denseMoment_uniform_constants (q : ℝ) (hq : 4 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 2 ≤ B → ∃ c : ℝ, 0 < c ∧ ∀ m : ℕ → ℕ,
      Tendsto m atTop atTop →
      Tendsto (fun n : ℕ => denseMomentLowerRate n (m n) q B) atTop (𝓝 0) →
      DenseMomentLowerConstruction q B m ∧ ∀ᶠ n : ℕ in atTop,
        c*denseMomentLowerRate n (m n) q B ≤ familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) ∧
        familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) ≤ polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} q B (m n*m n) n ≤ polynomialWorstDistance.{0} q B (m n*m n) n ∧
        polynomialWorstDistance.{0} q B (m n*m n) n ≤ C*denseMomentLowerRate n (m n) q B*dimensionLog n^(1/2-1/q) := by
  refine ⟨polynomialUniversalConstant q, zero_lt_one.trans_le (one_le_polynomialUniversalConstant q), ?_⟩
  intro B hB
  refine ⟨denseLowerConstant q B/2, half_pos (denseLowerConstant_pos hB), ?_⟩
  intro m hmTop hRate
  have h := denseMomentLower hq hB hmTop hRate
  have hr : ∀ᶠ n : ℕ in atTop, 0 < denseMomentLowerRate n (m n) q B := by
    filter_upwards [hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hnM hn
    exact denseMomentLowerRate_pos hn hnM hB
  have hdom : ∀ᶠ n : ℕ in atTop,
      rectangleError (familyArrayLaw (denseFamilyParameters q B n (m n)) n (m n))
        (sumVector (familyNormalizedObservations (denseFamilyParameters q B n (m n))))
        (familyGaussianSquareFactor (denseFamilyParameters q B n (m n)) (m n))
        (familyOrthant (m n*m n) ((denseFamilyParameters q B n (m n)).scale*normalMaxThreshold (m n))) ≤
      familyComparisonDistance (denseFamilyParameters q B n (m n)) n (m n) :=
    Eventually.of_forall (fun _ => rectangleError_le_rectangleDistance _ _ _ _)
  have hlo := eventually_mul_rate_le_of_quotient h.orthantLimit (half_lt_self h.positiveConstant) hdom hr
  refine ⟨h, ?_⟩
  filter_upwards [hlo, eventually_denseFamily_distance_le_symmetricWorstDistance hq hB hmTop hRate,
    hmTop.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hnL hnModel hnM hn
  refine ⟨hnL, hnModel, polynomialSymmetricWorstDistance_le _ _ _ _, ?_⟩
  have hp : 1 ≤ m n*m n := Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  exact polynomialWorstDistance_envelope_le hp hn (by linarith : 2 < q) (by linarith : 1 ≤ B)

/-- Theorem 8: both positive q-dependent constants precede the envelope,
dimension and sample sequences and the full actual polynomial classes. -/
theorem sparseMoment_uniform_constants (q : ℝ) (hq : 2 < q) :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (B : ℕ → ℝ) (m : ℕ → ℕ),
      (∀ n, 2 ≤ B n) → Tendsto m atTop atTop →
      Tendsto (fun n => sparseMomentK n (m n) q (B n)) atTop atTop →
      Tendsto (fun n => Real.log (sparseMomentK n (m n) q (B n))/dimensionLog (m n*m n)) atTop (𝓝 0) →
      Tendsto (fun n => sparseMomentLowerRate n (m n) q (B n)) atTop (𝓝 0) →
      SparseMomentLowerConstruction q B m ∧ ∀ᶠ n : ℕ in atTop,
        c*sparseMomentLowerRate n (m n) q (B n) ≤ familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ∧
        familyComparisonDistance (sparseFamilyParameters q n (m n) (B n)) n (m n) ≤ polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ∧
        polynomialSymmetricWorstDistance.{0} q (B n) (m n*m n) n ≤ polynomialWorstDistance.{0} q (B n) (m n*m n) n ∧
        polynomialWorstDistance.{0} q (B n) (m n*m n) n ≤ C*sparseMomentLowerRate n (m n) q (B n) := by
  refine ⟨sparseMomentLowerCoefficient q, sparseMomentUpperCoefficient q,
    sparseMomentLowerCoefficient_pos q, sparseMomentUpperCoefficient_pos q, ?_⟩
  intro B m hB hmTop hK hLog hRate
  have h := sparseMomentOptimal hq hB hmTop hK hLog hRate
  exact ⟨h.1, h.2.2.2⟩

end
end RectangleCLT.Companion.SplitV4
