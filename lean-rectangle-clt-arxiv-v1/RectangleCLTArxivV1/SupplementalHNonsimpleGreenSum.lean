import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry

/-! Finite incidence bookkeeping for the printed ridge Green identity.
Actual ridges have two original facet labels, hence exactly two ordered
descriptions. Codimension-three faces retain their complete active sets. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section

def nonsimpleOrderedFacetPairs {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) : Finset (α × α) :=
  Finset.univ.filter (fun p => p.1 ≠ p.2 ∧ ({p.1,p.2} : Finset α) = S)

theorem nonsimpleOrderedFacetPairs_pair {α : Type*} [Fintype α] [DecidableEq α]
    (a b : α) (hab : a ≠ b) :
    nonsimpleOrderedFacetPairs ({a,b} : Finset α) = {(a,b),(b,a)} := by
  ext p
  simp only [nonsimpleOrderedFacetPairs, Finset.mem_filter, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hne,he⟩
    have h1 : p.1 = a ∨ p.1 = b := by
      have hm : p.1 ∈ ({a,b} : Finset α) := by rw [← he]; simp
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
    have h2 : p.2 = a ∨ p.2 = b := by
      have hm : p.2 ∈ ({a,b} : Finset α) := by rw [← he]; simp
      simpa only [Finset.mem_insert,Finset.mem_singleton] using hm
    rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
    · exact False.elim (hne (h1.trans h2.symm))
    · exact Or.inl (Prod.ext h1 h2)
    · exact Or.inr (Prod.ext h1 h2)
    · exact False.elim (hne (h1.trans h2.symm))
  · rintro (rfl | rfl)
    · exact ⟨hab,rfl⟩
    · exact ⟨hab.symm,Finset.pair_comm _ _⟩

theorem nonsimpleOrderedFacetPairs_card {α : Type*} [Fintype α] [DecidableEq α]
    (S : Finset α) (hS : S.card = 2) : (nonsimpleOrderedFacetPairs S).card = 2 := by
  obtain ⟨a,b,hab,rfl⟩ := Finset.card_eq_two.mp hS
  rw [nonsimpleOrderedFacetPairs_pair a b hab]
  simp [hab]

/-- The factor one half removes only the two orders of the actual
ridge's two facets; it does not count triples at a nonsimple face. -/
theorem half_ordered_pair_sum_eq_actual_ridge_sum {α R : Type*}
    [Fintype α] [DecidableEq α] [Fintype R]
    (S : R → Finset α) (hS : ∀ e,(S e).card = 2) (c : R → ℝ) :
    (1/2 : ℝ) * (∑ p : α × α, ∑ e : R,
      if p ∈ nonsimpleOrderedFacetPairs (S e) then c e else 0) = ∑ e : R,c e := by
  classical
  rw [Finset.sum_comm, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro e _
  have hs : (∑ p : α × α, if p ∈ nonsimpleOrderedFacetPairs (S e) then c e else 0) =
      2 * c e := by
    rw [← Finset.sum_filter]
    simp only [Finset.filter_mem_eq_inter, Finset.univ_inter, Finset.sum_const,
      nonsimpleOrderedFacetPairs_card (S e) (hS e), nsmul_eq_mul, Nat.cast_ofNat]
  rw [hs]
  ring

/-- Signed boundary contributions are grouped by the actual
codimension-three face before taking any absolute value. -/
theorem nonsimple_signed_incidence_grouping {R H E : Type*}
    [Fintype R] [Fintype H] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (incident : R → H → Prop) [DecidableRel incident] (angle : R → ℝ) (mass : H → ℝ)
    (point : H → E) (normal : R → H → E) :
    (∑ e : R, ∑ h ∈ Finset.univ.filter (incident e),
      angle e * (⟪point h,normal e h⟫_ℝ * mass h)) =
    ∑ h : H, ⟪point h,
      ∑ e ∈ Finset.univ.filter (fun e => incident e h), angle e • normal e h⟫_ℝ * mass h := by
  classical
  simp only [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro h _
  rw [inner_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro e _
  by_cases he : incident e h
  · simp only [he,if_true,inner_smul_right]
    ring
  · simp [he]

end
end RectangleCLTArxivV1
