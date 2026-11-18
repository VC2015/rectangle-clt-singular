import RectangleCLTArxivV1.SupplementalHRidgeTripleGrouping

/-! Genuine finite reindexing from ordered cube sums to the actual
independent normal triples; low-rank empty families are retained. -/
namespace RectangleCLTArxivV1
open RectangleCLT
open scoped BigOperators
noncomputable section

def tripleArrowEquivProd (m : ℕ) : (Fin 3 → Fin m) ≃ Fin m × Fin m × Fin m where
  toFun f := (f 0,f 1,f 2)
  invFun p := ![p.1,p.2.1,p.2.2]
  left_inv f := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a,b,c⟩; rfl

theorem sum_cube_eq_sum_triple_functions {m : ℕ} (B : Fin m → Fin m → Fin m → ℝ) :
    (∑ j, ∑ l, ∑ k, B j l k)=∑ f : Fin 3 → Fin m, B (f 0) (f 1) (f 2) := by
  have h := (tripleArrowEquivProd m).sum_comp (fun p => B p.1 p.2.1 p.2.2)
  simp only [tripleArrowEquivProd,Equiv.coe_fn_mk,Fintype.sum_prod_type] at h
  exact h.symm

abbrev IndependentNormalTriple {m r : ℕ} (u : Fin m → Vector r) :=
  {f : Fin 3 → Fin m // LinearIndependent ℝ (fun i => u (f i))}

noncomputable instance independentNormalTripleFintype {m r : ℕ} (u : Fin m → Vector r) :
    Fintype (IndependentNormalTriple u) := Fintype.ofFinite _

theorem IndependentNormalTriple.injective {m r : ℕ} {u : Fin m → Vector r}
    (f : IndependentNormalTriple u) : Function.Injective f.val := by
  intro i j hij
  apply f.property.injective
  exact congrArg u hij

theorem sum_eq_sum_subtype_of_zero {ι : Type*} [Fintype ι]
    (P : ι → Prop) [DecidablePred P] [F : Fintype {i // P i}] (B : ι → ℝ) (hz : ∀ i, ¬P i → B i=0) :
    (∑ i, B i)=∑ i : {i // P i}, B i.val := by
  classical
  calc
    _ = ∑ i, if P i then B i else 0 := by
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : P i
      · rw [if_pos hi]
      · rw [if_neg hi,hz i hi]
    _ = _ := by
      have h := Finset.sum_subtype
        (F := (inferInstance : Fintype {i : ι // P i}))
        (Finset.univ.filter P) (by simp) B
      rw [Finset.sum_filter] at h
      exact h

/-- Once dependent third-boundary atoms have been proved zero, the cube
sum is exactly the finite independent-triple family, with no chosen
frame or supporting level needed for dependent triples. -/
theorem sum_cube_eq_independent_triples {m r : ℕ} (u : Fin m → Vector r)
    (B : Fin m → Fin m → Fin m → ℝ)
    (hz : ∀ f : Fin 3 → Fin m, ¬LinearIndependent ℝ (fun i => u (f i)) →
      B (f 0) (f 1) (f 2)=0) :
    (∑ j, ∑ l, ∑ k, B j l k)=
      ∑ f : IndependentNormalTriple u, B (f.val 0) (f.val 1) (f.val 2) := by
  classical
  rw [sum_cube_eq_sum_triple_functions]
  exact sum_eq_sum_subtype_of_zero (F := independentNormalTripleFintype u) _ _ hz

end
end RectangleCLTArxivV1
