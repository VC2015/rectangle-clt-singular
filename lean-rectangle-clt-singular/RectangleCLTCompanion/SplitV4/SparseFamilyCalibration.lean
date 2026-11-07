import RectangleCLTCompanion.SplitV4.SparseFamily
import RectangleCLTCompanion.SplitV4.SparseLowerCalibrationLimits
import RectangleCLTCompanion.SplitV4.RareFamilyComparison

/-! Actual-law instantiation of the sparse polynomial primitive limits. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem eventually_sparseFamily_parameters {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      (sparseFamilyParameters q n (m n) (B n)).theta = sparseLowerTheta n (Real.log (m n : ℝ)) q (B n) ∧
      (sparseFamilyParameters q n (m n) (B n)).pi = sparseLowerPi n (Real.log (m n : ℝ)) q (B n) ∧
      (sparseFamilyParameters q n (m n) (B n)).amplitude = sparseLowerAmplitude n (Real.log (m n : ℝ)) q (B n) := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  filter_upwards [eventually_sparseLower_probabilities ell B hq he hB hK hd,
    eventually_ge_atTop 1, he.eventually (eventually_gt_atTop 0), hK.eventually (eventually_ge_atTop 2)]
    with n hn hn1 hnL hnK
  exact sparseFamilyParameters_of_good q _ _ _
    ⟨hn.1, hn.2.1.le, hn.2.2.1, hn.2.2.2.1.le, sparseLowerAmplitude_pos (by omega) hnL (by have := hB n; linarith) hnK, hn.2.2.2.2.2⟩

theorem eventually_sparseFamily_polynomialIndependent {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hd : Tendsto (fun n => sparseLowerScale n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0)) :
    ∀ᶠ n : ℕ in atTop,
      PolynomialIndependentHypotheses (familyArrayLaw (sparseFamilyParameters q n (m n) (B n)) n (m n))
        (familyRawObservations (sparseFamilyParameters q n (m n) (B n))) q (B n) := by
  filter_upwards [eventually_sparseFamily_parameters hq hB hmTop hK hd, eventually_ge_atTop 1,
    hmTop.eventually (eventually_ge_atTop 2), hK.eventually (eventually_ge_atTop 2)] with n hn hn1 hnM hnK
  have hn0 : 0 < n := by omega
  have hL : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast hnM)
  let P := sparseFamilyParameters q n (m n) (B n)
  apply family_polynomialIndependent_of_rare_parameters P hn1 hq (hB n)
  · have ha : P.amplitude*P.theta^(1/q) = B n/2 := by
      change (sparseFamilyParameters q n (m n) (B n)).amplitude*
        (sparseFamilyParameters q n (m n) (B n)).theta^(1/q) = _
      rw [hn.1, hn.2.2]
      exact sparseLower_envelope_identity hn0 hL hnK
    exact ha.le
  · change (sparseFamilyParameters q n (m n) (B n)).theta*
      (sparseFamilyParameters q n (m n) (B n)).pi*
      (sparseFamilyParameters q n (m n) (B n)).amplitude^4 ≤ _
    rw [hn.1, hn.2.1, hn.2.2]
    exact (sparseLower_fourth_identity hn0 hL (by have := hB n; linarith) hnK).le

structure SparseFamilyCalibration (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) : Prop where
  count : Tendsto (fun n : ℕ => (n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).theta) atTop atTop
  cover : Tendsto (fun n : ℕ => (m n : ℝ)*((sparseFamilyParameters q n (m n) (B n)).pi/2)^
    Nat.ceil (2*((n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).theta))) atTop atTop
  variance : Tendsto (fun n => (sparseFamilyParameters q n (m n) (B n)).variance) atTop (𝓝 0)
  coefficient : Tendsto (fun n : ℕ => Real.sqrt (sparseFamilyParameters q n (m n) (B n)).variance*
    Real.sqrt (2*Real.log (m n : ℝ))/familyRareShiftScale (sparseFamilyParameters q n (m n) (B n)) n) atTop (𝓝 0)
  small : Tendsto (fun n : ℕ => Real.log (m n : ℝ)^3/n) atTop (𝓝 0)
  scale : Tendsto (fun n : ℕ => familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n)/
    boundedLowerScale n (m n)) atTop atTop
  countCost : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).amplitude^2*
    (((n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).theta)^2+(n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).theta)/n/
      familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n)) atTop (𝓝 0)
  gaussianCost : Tendsto (fun n : ℕ => Real.log (m n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).variance*
    (1+Real.log (m n : ℝ))/familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n)) atTop (𝓝 0)

theorem sparseFamilyCalibration {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hd : Tendsto (fun n => sparseLowerScale n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0)) :
    SparseFamilyCalibration q B m := by
  let ell := fun n : ℕ => Real.log (m n : ℝ)
  have he : Tendsto ell atTop atTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hgood := eventually_sparseFamily_parameters hq hB hmTop hK hd
  have hIDs : ∀ᶠ n : ℕ in atTop,
      (sparseFamilyParameters q n (m n) (B n)).variance = sparseLowerVariance n (ell n) q (B n) ∧
      (n : ℝ)*(sparseFamilyParameters q n (m n) (B n)).theta = sparseLowerCount n (ell n) q (B n) ∧
      familyRareShiftScale (sparseFamilyParameters q n (m n) (B n)) n =
        sparseLowerAmplitude n (ell n) q (B n)*sparseLowerCount n (ell n) q (B n)/Real.sqrt n ∧
      familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n) = sparseLowerScale n (ell n) q (B n) := by
    filter_upwards [hgood, eventually_ge_atTop 1] with n hn hn1
    exact sparseFamily_identities hn1 hn
  refine ⟨?_, ?_, ?_, ?_, tendsto_sparseLower_cube_div ell B q he hB hK hd, ?_, ?_, ?_⟩
  · apply (tendsto_sparseLowerCount ell B q he hK hΛ).congr'
    filter_upwards [hIDs] with n hn
    exact hn.2.1.symm
  · apply (tendsto_sparseLower_coverage ell B q he hB hK hΛ).congr'
    filter_upwards [hIDs, hgood, eventually_ge_atTop 1] with n hn hnG hn1
    rw [hn.2.1, hnG.2.1]
    dsimp only [ell, sparseLowerCutoff]
    rw [Real.exp_log (show (0 : ℝ) < m n by exact_mod_cast (show 0 < m n by have := hm n; omega)),
      sparseLowerTheta_count (by omega : 0 < n)]

  · apply (tendsto_sparseLowerVariance ell B hq he hB hK hd).congr'
    filter_upwards [hIDs] with n hn
    exact hn.1.symm
  · apply (tendsto_sparseLower_gaussian_coefficient ell B q he hB hK).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1, hn.2.2.1]
  · apply (tendsto_sparseLower_scale_bounded_ratio ell B q he hB hK hd).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.2.2.2]
    rfl
  · apply (tendsto_sparseLower_count_cost ell B q he hB hK hΛ hd).congr'
    filter_upwards [hIDs, hgood] with n hn hnG
    rw [hn.2.1, hn.2.2.2, hnG.2.2]
  · apply (tendsto_sparseLower_gaussian_cost ell B q he hB hK hd).congr'
    filter_upwards [hIDs] with n hn
    rw [hn.1, hn.2.2.2]

/-- Genuine signed orthant discrepancy at the native sparse scale. -/
theorem tendsto_sparseFamily_discrepancy_div_nativeScale
    {B : ℕ → ℝ} {m : ℕ → ℕ} {q : ℝ} [∀ n, NeZero (m n)]
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hK : Tendsto (fun n => sparseLowerKhat n (Real.log (m n : ℝ)) q (B n)) atTop atTop)
    (hΛ : Tendsto (fun n => sparseLowerLog n (Real.log (m n : ℝ)) q (B n)/Real.log (m n : ℝ)) atTop (𝓝 0))
    (hd : Tendsto (fun n => sparseLowerScale n (Real.log (m n : ℝ)) q (B n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => familyShiftedCDFDifference (sparseFamilyParameters q n (m n) (B n)) n (m n)
      (normalMaxThreshold (m n))/familyRareLowerScale (sparseFamilyParameters q n (m n) (B n)) n (m n))
      atTop (𝓝 (-Real.sqrt 2*Real.exp (-1))) := by
  have h := sparseFamilyCalibration hq hB hm hmTop hK hΛ hd
  exact tendsto_familyRare_discrepancy_div_scale hm hmTop h.count h.cover h.variance h.coefficient
    h.small h.scale h.countCost h.gaussianCost

end
end RectangleCLT.Companion.SplitV4
