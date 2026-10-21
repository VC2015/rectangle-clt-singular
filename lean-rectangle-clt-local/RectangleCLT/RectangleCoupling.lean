import RectangleCLT.RectangleExtension

/-!
# Transferring a rectangle bound through an actual coupling

The coupling event and the reference-law boundary estimates are explicit.
This module is an elementary probability bridge, not a CLT assertion.
The eventual truncation applications supply each of its hypotheses from
the actual random vectors and Gaussian coordinate laws.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def boxCollar {p : ℕ} (lo hi : Vector p) (r : ℝ) : Set (Vector p) :=
  (⋃ j, {x | lo j - r ≤ x j ∧ x j ≤ lo j + r}) ∪
    ⋃ j, {x | hi j - r ≤ x j ∧ x j ≤ hi j + r}

theorem expanded_box_subset_union_collar {p : ℕ}
    (lo hi : Vector p) {r : ℝ} (hr : 0 ≤ r) :
    (Rect.closedBox (fun j => lo j - r) (fun j => hi j + r)).carrier ⊆
      (Rect.closedBox lo hi).carrier ∪ boxCollar lo hi r := by
  classical
  intro x hx
  by_cases hinside : x ∈ (Rect.closedBox lo hi).carrier
  · exact Or.inl hinside
  · right
    have hfail : ∃ j, ¬ (lo j ≤ x j ∧ x j ≤ hi j) := by
      simpa only [Rect.carrier, Rect.closedBox, mem_pi, mem_univ,
        forall_true_left, mem_Icc, not_forall] using hinside
    obtain ⟨j, hj⟩ := hfail
    have hbounds := hx j (mem_univ j)
    change lo j - r ≤ x j ∧ x j ≤ hi j + r at hbounds
    by_cases hlow : x j < lo j
    · exact Or.inl (mem_iUnion.mpr ⟨j, hbounds.1, by linarith⟩)
    · have hupper : hi j < x j :=
        lt_of_not_ge (fun hhi => hj ⟨le_of_not_gt hlow, hhi⟩)
      exact Or.inr (mem_iUnion.mpr ⟨j, by constructor <;> linarith⟩)

theorem box_subset_shrunken_union_collar {p : ℕ}
    (lo hi : Vector p) {r : ℝ} (hr : 0 ≤ r) :
    (Rect.closedBox lo hi).carrier ⊆
      (Rect.closedBox (fun j => lo j + r) (fun j => hi j - r)).carrier ∪
        boxCollar lo hi r := by
  classical
  intro x hx
  by_cases hinside : x ∈
      (Rect.closedBox (fun j => lo j + r) (fun j => hi j - r)).carrier
  · exact Or.inl hinside
  · right
    have hfail : ∃ j, ¬ (lo j + r ≤ x j ∧ x j ≤ hi j - r) := by
      simpa only [Rect.carrier, Rect.closedBox, mem_pi, mem_univ,
        forall_true_left, mem_Icc, not_forall] using hinside
    obtain ⟨j, hj⟩ := hfail
    have hbounds := hx j (mem_univ j)
    change lo j ≤ x j ∧ x j ≤ hi j at hbounds
    by_cases hlow : x j < lo j + r
    · exact Or.inl (mem_iUnion.mpr ⟨j, by constructor <;> linarith⟩)
    · have hupper : hi j - r < x j :=
        lt_of_not_ge (fun hhi => hj ⟨le_of_not_gt hlow, hhi⟩)
      exact Or.inr (mem_iUnion.mpr ⟨j, by constructor <;> linarith⟩)

/-- A coarse marginal strip estimate suffices when the coupling error
vanishes faster than any dimensional factor in a truncation argument. -/
theorem measureReal_boxCollar_le {p : ℕ} (ν : Measure (Vector p))
    [IsFiniteMeasure ν] (lo hi : Vector p) {r K : ℝ} (hr : 0 ≤ r)
    (hstrip : ∀ (j : Fin p) (a b : ℝ), a ≤ b →
      ν.real {x | a ≤ x j ∧ x j ≤ b} ≤ K * (b - a)) :
    ν.real (boxCollar lo hi r) ≤ 4 * p * K * r := by
  have hlo : ν.real (⋃ j, {x | lo j - r ≤ x j ∧ x j ≤ lo j + r}) ≤
      ∑ _j : Fin p, K * (2 * r) := by
    apply (measureReal_iUnion_fintype_le _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [show lo j + r - (lo j - r) = 2 * r by ring] using
      hstrip j (lo j - r) (lo j + r) (by linarith)
  have hhi : ν.real (⋃ j, {x | hi j - r ≤ x j ∧ x j ≤ hi j + r}) ≤
      ∑ _j : Fin p, K * (2 * r) := by
    apply (measureReal_iUnion_fintype_le _).trans
    apply Finset.sum_le_sum
    intro j _
    simpa only [show hi j + r - (hi j - r) = 2 * r by ring] using
      hstrip j (hi j - r) (hi j + r) (by linarith)
  calc
    ν.real (boxCollar lo hi r) ≤
        ν.real (⋃ j, {x | lo j - r ≤ x j ∧ x j ≤ lo j + r}) +
          ν.real (⋃ j, {x | hi j - r ≤ x j ∧ x j ≤ hi j + r}) :=
      measureReal_union_le _ _
    _ ≤ (∑ _j : Fin p, K * (2 * r)) + ∑ _j : Fin p, K * (2 * r) :=
      add_le_add hlo hhi
    _ = 4 * p * K * r := by simp only [Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]; ring

theorem coupled_box_probability_le {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V : Ω → Vector p) (lo hi : Vector p) {r : ℝ} (hr : 0 ≤ r) :
    μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) ≤
      μ.real (V ⁻¹' (Rect.closedBox (fun j => lo j - r)
        (fun j => hi j + r)).carrier) + μ.real {ω | r < ‖W ω - V ω‖} := by
  have hsub : W ⁻¹' (Rect.closedBox lo hi).carrier ⊆
      V ⁻¹' (Rect.closedBox (fun j => lo j - r) (fun j => hi j + r)).carrier ∪
        {ω | r < ‖W ω - V ω‖} := by
    intro ω hω
    by_cases hbad : r < ‖W ω - V ω‖
    · exact Or.inr hbad
    · left
      have hnorm : ‖W ω - V ω‖ ≤ r := le_of_not_gt hbad
      intro j _
      have hcoord : |W ω j - V ω j| ≤ r := by
        simpa only [Pi.sub_apply, Real.norm_eq_abs] using
          (norm_le_pi_norm (W ω - V ω) j).trans hnorm
      have hb := hω j (mem_univ j)
      change lo j ≤ W ω j ∧ W ω j ≤ hi j at hb
      change lo j - r ≤ V ω j ∧ V ω j ≤ hi j + r
      constructor <;> linarith [(abs_le.mp hcoord).1, (abs_le.mp hcoord).2]
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-- Transfer a bound from the coupled vector `V` to `W`.  The law of `W`
may have atoms.  Only the reference law needs the stated marginal cap. -/
theorem rectangleError_le_of_norm_coupling {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (hp : 1 ≤ p) (W V : Ω → Vector p) (hW : Measurable W)
    (A : Matrix (Fin p) (Fin p) ℝ) {r q E K : ℝ} (hr : 0 ≤ r)
    (hbad : μ.real {ω | r < ‖W ω - V ω‖} ≤ q)
    (hbase : ∀ lo hi : Vector p, rectangleError μ V A (Rect.closedBox lo hi) ≤ E)
    (hstrip : ∀ (j : Fin p) (a b : ℝ), a ≤ b →
      (gaussianLaw A).real {x | a ≤ x j ∧ x j ≤ b} ≤ K * (b - a))
    (R : Rect p) : rectangleError μ W A R ≤ E + q + 4 * p * K * r := by
  apply rectangleError_le_of_closedBox hp μ W hW A
  intro lo hi
  let loOut : Vector p := fun j => lo j - r
  let hiOut : Vector p := fun j => hi j + r
  let loIn : Vector p := fun j => lo j + r
  let hiIn : Vector p := fun j => hi j - r
  have hcollar := measureReal_boxCollar_le (gaussianLaw A) lo hi hr hstrip
  have hout : (gaussianLaw A).real (Rect.closedBox loOut hiOut).carrier ≤
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier + 4 * p * K * r := by
    exact ((measureReal_mono (expanded_box_subset_union_collar lo hi hr)).trans
      (measureReal_union_le _ _)).trans (add_le_add_left hcollar _)
  have hin : (gaussianLaw A).real (Rect.closedBox lo hi).carrier ≤
      (gaussianLaw A).real (Rect.closedBox loIn hiIn).carrier + 4 * p * K * r := by
    exact ((measureReal_mono (box_subset_shrunken_union_collar lo hi hr)).trans
      (measureReal_union_le _ _)).trans (add_le_add_left hcollar _)
  have hupper := coupled_box_probability_le μ W V lo hi hr
  have hlower := coupled_box_probability_le μ V W loIn hiIn hr
  have hreverse : {ω | r < ‖V ω - W ω‖} = {ω | r < ‖W ω - V ω‖} := by
    ext ω
    simp only [mem_setOf_eq, norm_sub_rev]
  rw [hreverse] at hlower
  have hlo : (fun j => loIn j - r) = lo := by funext j; dsimp [loIn]; ring
  have hhi : (fun j => hiIn j + r) = hi := by funext j; dsimp [hiIn]; ring
  rw [hlo, hhi] at hlower
  have hbOut := abs_le.mp (hbase loOut hiOut)
  have hbIn := abs_le.mp (hbase loIn hiIn)
  change |μ.real (W ⁻¹' (Rect.closedBox lo hi).carrier) -
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
  change -E ≤ μ.real (V ⁻¹' (Rect.closedBox loOut hiOut).carrier) -
      (gaussianLaw A).real (Rect.closedBox loOut hiOut).carrier ∧ _ at hbOut
  change -E ≤ μ.real (V ⁻¹' (Rect.closedBox loIn hiIn).carrier) -
      (gaussianLaw A).real (Rect.closedBox loIn hiIn).carrier ∧ _ at hbIn
  exact abs_le.mpr ⟨by linarith [hbIn.1], by linarith [hbOut.2]⟩

end

end RectangleCLT
