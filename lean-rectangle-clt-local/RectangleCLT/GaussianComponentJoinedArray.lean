import RectangleCLT.GaussianComponentApproximation
import Mathlib.Algebra.BigOperators.Fin

/-!
# A genuine bounded array containing the original observations

The sample law is the product of the original observation marginals and
the small truncated Gaussian marginals. Thus independence is proved from
the actual product construction. Reindexing gives the `Fin (n + k^6)`
array required by the bounded proxy theorem.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem gaussianComponentPi_map_eval {ι : Type*} [Fintype ι] {p : ℕ}
    (ν : ι → Measure (Vector p)) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun z => z i) = ν i := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs,
    ← Set.univ_pi_update_univ, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem gaussianComponentPi_iIndepFun {ι : Type*} [Fintype ι] {p : ℕ}
    (ν : ι → Measure (Vector p)) [∀ i, IsProbabilityMeasure (ν i)] :
    iIndepFun (fun i (z : ι → Vector p) => z i) (Measure.pi ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp_rw [gaussianComponentPi_map_eval ν]
  exact Measure.map_id

/-- Generic product-law construction from actual centered bounded
observation marginals. There are no analytic-estimate hypotheses. -/
theorem gaussianComponentPi_boundedIndependent {ι : Type*} [Fintype ι]
    {p n : ℕ} (e : Fin n ≃ ι) (ν : ι → Measure (Vector p))
    [∀ i, IsProbabilityMeasure (ν i)] {δ : ℝ} (hδ : 0 ≤ δ)
    (hcenter : ∀ i j, (∫ x, x j ∂ν i) = 0)
    (hbound : ∀ i, ∀ᵐ x ∂ν i, ‖x‖ ≤ δ) :
    BoundedIndependentHypotheses (Measure.pi ν)
      (fun i z => z (e i)) δ := by
  refine ⟨fun i => measurable_pi_apply (e i),
    (gaussianComponentPi_iIndepFun ν).precomp e.injective, ?_, ?_, hδ⟩
  · intro i j
    have hm := integral_map (μ := Measure.pi ν)
      (measurable_pi_apply (e i)).aemeasurable
      (measurable_pi_apply j).aestronglyMeasurable
    rw [gaussianComponentPi_map_eval ν] at hm
    exact hm.symm.trans (hcenter (e i) j)
  · intro i
    have hs : MeasurableSet {x : Vector p | ‖x‖ ≤ δ} :=
      measurableSet_le measurable_norm measurable_const
    have hb : ∀ᵐ x ∂(Measure.pi ν).map (fun z => z (e i)), ‖x‖ ≤ δ := by
      rw [gaussianComponentPi_map_eval ν]
      exact hbound (e i)
    exact (ae_map_iff (measurable_pi_apply (e i)).aemeasurable hs).mp hb

def gaussianComponentJoinedMarginal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Fin n ⊕ Fin (k ^ 6) → Measure (Vector p) :=
  Sum.elim (fun i => μ.map (ξ i))
    (fun _ => (gaussianLaw B).map (gaussianComponentIncrement k))

def gaussianComponentJoinedArray {p n : ℕ} (k : ℕ)
    (i : Fin (n + k ^ 6)) (z : Fin n ⊕ Fin (k ^ 6) → Vector p) : Vector p :=
  z (finSumFinEquiv.symm i)

theorem gaussianComponentJoinedMarginal_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (i : Fin n ⊕ Fin (k ^ 6)) :
    IsProbabilityMeasure (gaussianComponentJoinedMarginal μ ξ B k i) := by
  cases i with
  | inl i => exact isProbabilityMeasure_map (hξ i).aemeasurable
  | inr i => exact isProbabilityMeasure_map
      (measurable_gaussianComponentIncrement k).aemeasurable

/-- The original and Gaussian increment observations are all genuine
independent bounded observations in one finite product experiment. -/
theorem gaussianComponentJoinedArray_boundedIndependent
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    BoundedIndependentHypotheses
      (Measure.pi (gaussianComponentJoinedMarginal μ ξ B k))
      (gaussianComponentJoinedArray (p := p) (n := n) k)
      (max δ (k : ℝ)⁻¹) := by
  let ν := gaussianComponentJoinedMarginal μ ξ B k
  letI (i : Fin n ⊕ Fin (k ^ 6)) : IsProbabilityMeasure (ν i) :=
    gaussianComponentJoinedMarginal_isProbability μ ξ h.measurable B k i
  apply gaussianComponentPi_boundedIndependent finSumFinEquiv.symm ν
    (h.delta_nonneg.trans (le_max_left _ _))
  · intro i j
    cases i with
    | inl i =>
        change (∫ x, x j ∂μ.map (ξ i)) = 0
        rw [integral_map (h.measurable i).aemeasurable
          (measurable_pi_apply j).aestronglyMeasurable]
        exact h.centered i j
    | inr i =>
        change (∫ x, x j ∂(gaussianLaw B).map (gaussianComponentIncrement k)) = 0
        rw [integral_map (measurable_gaussianComponentIncrement k).aemeasurable
          (measurable_pi_apply j).aestronglyMeasurable]
        exact gaussianComponentIncrement_integral_zero B k j
  · intro i
    have hs : MeasurableSet {x : Vector p | ‖x‖ ≤ max δ (k : ℝ)⁻¹} :=
      measurableSet_le measurable_norm measurable_const
    cases i with
    | inl i =>
        change ∀ᵐ x ∂μ.map (ξ i), ‖x‖ ≤ max δ (k : ℝ)⁻¹
        apply (ae_map_iff (h.measurable i).aemeasurable hs).mpr
        filter_upwards [h.bounded i] with ω hω
        exact hω.trans (le_max_left _ _)
    | inr i =>
        change ∀ᵐ x ∂(gaussianLaw B).map (gaussianComponentIncrement k),
          ‖x‖ ≤ max δ (k : ℝ)⁻¹
        apply (ae_map_iff (measurable_gaussianComponentIncrement k).aemeasurable hs).mpr
        exact ae_of_all _ fun x =>
          (norm_gaussianComponentIncrement_le hk x).trans (le_max_right _ _)

theorem sumVector_gaussianComponentJoinedArray {p n : ℕ} (k : ℕ)
    (z : Fin n ⊕ Fin (k ^ 6) → Vector p) :
    sumVector (gaussianComponentJoinedArray (p := p) (n := n) k) z =
      (∑ i : Fin n, z (.inl i)) + ∑ i : Fin (k ^ 6), z (.inr i) := by
  unfold sumVector gaussianComponentJoinedArray
  rw [finSumFinEquiv.symm.sum_comp]
  exact Fintype.sum_sum_type z

end

end RectangleCLT
