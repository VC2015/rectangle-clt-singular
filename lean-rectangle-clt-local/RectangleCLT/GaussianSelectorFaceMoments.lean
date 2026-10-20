import RectangleCLT.NormalizedThinnedHypotheses
import RectangleCLT.GaussianFourthFaceBounds
import RectangleCLT.InterpolationLaw

/-! Localized face moments under the actual normalized Bernoulli retained
array. Both the covariance `(1-t)/t` and envelope `2δ/sqrt t` are derived
from the given observations. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

theorem integrable_faceMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (k : ℕ) :
    Integrable (fun ω => faceMoment S s A (V ω) k) μ := by
  unfold faceMoment
  exact ((integrable_softFace_projectionPolynomial_shift S s A V hV hp k).integral_prod_right).const_mul _

theorem integral_ordered_faceMoment_eq_shifted
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p) (q k : ℕ) :
    (∫ ω, ∑ S : OrderedFaceTuples s.faces q, faceMoment S.val s A (V ω) k ∂μ) =
      ∑ S : OrderedFaceTuples s.faces q, shiftedFaceMoment μ S.val s A V k := by
  classical
  rw [integral_finset_sum Finset.univ (fun S _ => integrable_faceMoment_comp μ S.val s A V hV hp k)]
  exact Finset.sum_congr rfl (fun S _ => integral_faceMoment_shift_eq S.val s A V hV hp k)

def normalizedThinnedShift {p n : ℕ} (t : ℝ) (b : Fin n → Vector p) : Vector p :=
  (Real.sqrt t)⁻¹ • arraySum b

theorem sumVector_normalizedThinned {p n : ℕ} (t : ℝ) :
    sumVector (fun i (b : Fin n → Vector p) => (Real.sqrt t)⁻¹ • b i) =
      normalizedThinnedShift t := by
  funext b
  unfold sumVector normalizedThinnedShift arraySum
  exact (Finset.smul_sum).symm

def normalizedThinnedFaceMomentSum
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (q k : ℕ) : ℝ :=
  ∑ S : OrderedFaceTuples s.faces q,
    shiftedFaceMoment (bernoulliArrayLaw μ ξ t) S.val s A (normalizedThinnedShift t) k

/-- The fourth-order localized face estimate specialized to the actual
normalized retained-array law. It uses no lower bound on the full covariance
matrix, and its Gaussian Gram assumptions involve at most four coordinates. -/
theorem normalizedThinnedFaceMomentSum_le
    {Ω : Type*} [MeasurableSpace Ω] {p n q k : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {t a₄ : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hq0 : 0 < q) (hq : q ≤ 4)
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hA : ∀ j, (A * A.transpose) j j = 1) (hqk : q + k = 4) :
    normalizedThinnedFaceMomentSum μ ξ s A t q k ≤
      fourthFaceConstant * 1073741824 * (dimensionLog p) ^ 2 *
        (1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t) := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  have hv : 0 < (1 - t) / t := div_pos (sub_pos.mpr ht1) ht
  have hh := sum_ordered_fourth_shiftedFaceMoment_le
    (h.normalized_thinned t ht ht1.le) hp hv
    (h.normalized_thinned_sum_unit_diagonal hunit t ht ht1.le) s A
    hq0 hq hQ ha₄ hA k hqk
  rw [sumVector_normalizedThinned] at hh
  exact hh

theorem integrable_normalizedThinnedFaceMoments
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (hp : 1 ≤ p)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (q k : ℕ) :
    Integrable (fun b => ∑ S : OrderedFaceTuples s.faces q,
      faceMoment S.val s A (normalizedThinnedShift t b) k) (bernoulliArrayLaw μ ξ t) := by
  classical
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  exact integrable_finset_sum Finset.univ (fun S _ =>
    integrable_faceMoment_comp (bernoulliArrayLaw μ ξ t) S.val s A (normalizedThinnedShift t)
      (measurable_const.smul (measurable_arraySum p n)) hp k)

/-- The localized fourth-order face estimate as an ordinary expectation
under the retained-array law, ready for comparison with an actual derivative
envelope at the same full interpolation point. -/
theorem integral_normalizedThinnedFaceMoments_le
    {Ω : Type*} [MeasurableSpace Ω] {p n q k : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {t a₄ : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (hq0 : 0 < q) (hq : q ≤ 4)
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hA : ∀ j, (A * A.transpose) j j = 1) (hqk : q + k = 4) :
    (∫ b, ∑ S : OrderedFaceTuples s.faces q,
      faceMoment S.val s A (normalizedThinnedShift t b) k ∂bernoulliArrayLaw μ ξ t) ≤
      fourthFaceConstant * 1073741824 * (dimensionLog p) ^ 2 *
        (1 + (2 * δ / Real.sqrt t) * Real.sqrt (dimensionLog p)) /
          Real.sqrt ((1 - t) / t) := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.le ht1.le
  rw [integral_ordered_faceMoment_eq_shifted (bernoulliArrayLaw μ ξ t) s A (normalizedThinnedShift t)
    (measurable_const.smul (measurable_arraySum p n)) hp q k]
  exact normalizedThinnedFaceMomentSum_le h hp hunit s A ht ht1 hq0 hq hQ ha₄ hA hqk

end
end RectangleCLT.GaussianTube
