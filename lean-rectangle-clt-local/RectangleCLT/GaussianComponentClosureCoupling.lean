import RectangleCLT.GaussianComponentClosureLaw
import RectangleCLT.GaussianMarginalCoupling

/-! Quantitative coupling in the raw Gaussian product experiment. The
small covariance-restoring columns are bounded almost surely; no
continuity assumption on the original bounded sum is needed. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem rectangleError_eq_of_map_eq
    {Ω Ω' : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω'] {p : ℕ}
    (μ : Measure Ω) (ν : Measure Ω') (W : Ω → Vector p) (V : Ω' → Vector p)
    (hW : Measurable W) (hV : Measurable V) (h : μ.map W = ν.map V)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError μ W A R = rectangleError ν V A R := by
  have hreal := congrArg (fun η : Measure (Vector p) => η.real R.carrier) h
  simp only [Measure.real, Measure.map_apply hW R.measurableSet_carrier,
    Measure.map_apply hV R.measurableSet_carrier] at hreal
  unfold rectangleError
  simp only [Measure.real]
  rw [hreal]

theorem gaussianComponentRaw_correction_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    ∀ᵐ z ∂Measure.pi (gaussianComponentRawMarginal μ ξ B k),
      ∀ r : Fin p, ‖z (.inr (.inr r))‖ ≤
        Real.sqrt (gaussianComponentRestorationError B k) := by
  let ν := gaussianComponentRawMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRawMarginal_isProbability μ ξ hξ B k i
  apply ae_all_iff.mpr
  intro r
  have hnorm : ∀ᵐ x ∂(Measure.pi ν).map (fun z => z (.inr (.inr r))),
      ‖x‖ ≤ Real.sqrt (gaussianComponentRestorationError B k) := by
    rw [gaussianComponentPi_map_eval ν]
    exact symmetricColumnLaw_bounded
      (factor_column_norm_le_sqrt_diagonal_bound _
        (gaussianComponentRestorationError_nonneg B k)
        (gaussianComponentRestoredFactor_diagonal_le hp B hk) r)
  exact (ae_map_iff (measurable_pi_apply _).aemeasurable
    (measurableSet_le measurable_norm measurable_const)).mp hnorm

/-- An actual norm coupling, with failure probability `M₄/k²` and
deterministic radius `p*sqrt(M₄/k⁴)`. -/
theorem gaussianComponentRaw_norm_coupling
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    (Measure.pi (gaussianComponentRawMarginal μ ξ B k)).real
      {z | p * Real.sqrt (gaussianComponentRestorationError B k) <
        ‖gaussianComponentRawOriginalSum (p := p) (n := n) k z -
          gaussianComponentRawRestoredSum k z‖} ≤
            gaussianComponentFourthMoment B / (k : ℝ) ^ 2 := by
  let ν := gaussianComponentRawMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRawMarginal_isProbability μ ξ hξ B k i
  let νraw := Measure.pi ν
  let Z : Fin (k ^ 6) → (Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) → Vector p :=
    fun i z => z (.inr (.inl i))
  have hZ (i : Fin (k ^ 6)) : Measurable (Z i) := measurable_pi_apply _
  have hZlaw (i : Fin (k ^ 6)) : νraw.map (Z i) = gaussianLaw B :=
    gaussianComponentPi_map_eval ν (.inr (.inl i))
  have htail := gaussianComponent_any_cutoff_probability_le hp B hk Z hZ hZlaw
  have hcor := gaussianComponentRaw_correction_bound μ ξ hξ hp B hk
  have hsub :
      {z | p * Real.sqrt (gaussianComponentRestorationError B k) <
          ‖gaussianComponentRawOriginalSum (p := p) (n := n) k z -
            gaussianComponentRawRestoredSum k z‖} ≤ᵐ[νraw]
        {z | ∃ i : Fin (k ^ 6), (k : ℝ) ^ 2 < ‖Z i z‖} := by
    filter_upwards [hcor] with z hz
    intro hbad
    by_contra hnot
    have hgood (i : Fin (k ^ 6)) : ‖Z i z‖ ≤ (k : ℝ) ^ 2 := by
      by_contra hi
      exact hnot ⟨i, lt_of_not_ge hi⟩
    have hmiddle : (∑ i : Fin (k ^ 6), gaussianComponentIncrement k (Z i z)) =
        ((k : ℝ) ^ 3)⁻¹ • ∑ i : Fin (k ^ 6), Z i z := by
      simp only [gaussianComponentIncrement, truncateVector, if_pos (hgood _)]
      simp only [Finset.smul_sum]
    have hdiff : gaussianComponentRawOriginalSum (p := p) (n := n) k z -
        gaussianComponentRawRestoredSum k z = -∑ r : Fin p, z (.inr (.inr r)) := by
      rw [gaussianComponentRawRestoredSum, sumVector_gaussianComponentRestoredArray]
      change ((∑ i : Fin n, z (.inl i)) +
          ((k : ℝ) ^ 3)⁻¹ • ∑ i : Fin (k ^ 6), Z i z) -
        (((∑ i : Fin n, z (.inl i)) +
          ∑ i : Fin (k ^ 6), gaussianComponentIncrement k (Z i z)) +
            ∑ r : Fin p, z (.inr (.inr r))) = _
      rw [hmiddle, sub_add_eq_sub_sub, sub_self, zero_sub]
    have hnorm : ‖gaussianComponentRawOriginalSum (p := p) (n := n) k z -
        gaussianComponentRawRestoredSum k z‖ ≤
          p * Real.sqrt (gaussianComponentRestorationError B k) := by
      rw [hdiff, norm_neg]
      calc
        _ ≤ ∑ r : Fin p, ‖z (.inr (.inr r))‖ := norm_sum_le _ _
        _ ≤ ∑ _r : Fin p, Real.sqrt (gaussianComponentRestorationError B k) :=
          Finset.sum_le_sum fun r _ => hz r
        _ = _ := by simp [nsmul_eq_mul]
    exact not_le_of_gt hbad hnorm
  exact (ENNReal.toReal_mono (measure_ne_top νraw _)
    (measure_mono_ae hsub)).trans htail

/-- A rectangle approximation for the restored bounded array transfers
to the original Gaussian-convolved vector with an explicit vanishing cost. -/
theorem gaussianComponentRaw_rectangle_transfer
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) {δ : ℝ}
    (hp : 1 ≤ p) (B : Matrix (Fin p) (Fin p) ℝ)
    (h : ProxyHypotheses μ ξ G δ B) {k : ℕ} (hk : k ≠ 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {E : ℝ}
    (hbase : ∀ lo hi : Vector p,
      rectangleError (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k))
        (sumVector (gaussianComponentRestoredArray (p := p) (n := n) k)) A
        (Rect.closedBox lo hi) ≤ E) (R : Rect p) :
    rectangleError μ (sumWithGaussian ξ G) A R ≤
      E + gaussianComponentFourthMoment B / (k : ℝ) ^ 2 +
        4 * p * (p * Real.sqrt (gaussianComponentRestorationError B k)) := by
  let ν := gaussianComponentRawMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentRawMarginal_isProbability μ ξ h.boundedIndependent.measurable B k i
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
      IsProbabilityMeasure (gaussianComponentRestoredMarginal μ ξ B k i) :=
    gaussianComponentRestoredMarginal_isProbability μ ξ h.boundedIndependent.measurable B k i
  have hbaseRaw (lo hi : Vector p) :
      rectangleError (Measure.pi ν)
        (gaussianComponentRawRestoredSum (p := p) (n := n) k) A
        (Rect.closedBox lo hi) ≤ E := by
    rw [rectangleError_eq_of_map_eq (Measure.pi ν)
      (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)) _ _
      (measurable_gaussianComponentRawRestoredSum k)
      (by unfold sumVector gaussianComponentRestoredArray; fun_prop)
      (gaussianComponentRawRestoredSum_law μ ξ h.boundedIndependent.measurable B k)]
    exact hbase lo hi
  have hcouple := rectangleError_le_of_gaussian_norm_coupling (Measure.pi ν) hp
    (gaussianComponentRawOriginalSum (p := p) (n := n) k)
    (gaussianComponentRawRestoredSum (p := p) (n := n) k)
    (measurable_gaussianComponentRawOriginalSum k) A hdiag
    (by positivity : 0 ≤ (p : ℝ) * Real.sqrt (gaussianComponentRestorationError B k))
    (gaussianComponentRaw_norm_coupling μ ξ h.boundedIndependent.measurable hp B hk)
    hbaseRaw R
  rw [rectangleError_eq_of_map_eq (Measure.pi ν) μ _ _
    (measurable_gaussianComponentRawOriginalSum k) h.measurable_sumWithGaussian
    (gaussianComponentRawOriginalSum_law_eq μ ξ G B h hk)] at hcouple
  exact hcouple

end

end RectangleCLT
