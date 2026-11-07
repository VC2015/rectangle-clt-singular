import RectangleCLTCompanion.SplitV4.SymmetricFamilyCountBounds
import RectangleCLTCompanion.SplitV4.FiniteProductColumns

/-! Exact disintegration of the masks into common activations and independent columns. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

abbrev FamilyMaskSign := Bool × Bool

def familyMaskSignLaw (P : SymmetricFamilyParameters) : Measure FamilyMaskSign :=
  (familyBernoulli familyHalf).prod (familyBernoulli (familyPi P))
instance familyMaskSignLaw_probability (P : SymmetricFamilyParameters) : IsProbabilityMeasure (familyMaskSignLaw P) := by
  unfold familyMaskSignLaw
  infer_instance

def familyRestRowToActivation (z : FamilyRestSeed m) : Bool × (Fin m → FamilyMaskSign) :=
  (z.2.1, fun u => (z.1 u, z.2.2 u))

theorem familyRestRowToActivation_preserving (P : SymmetricFamilyParameters) (m : ℕ) :
    MeasurePreserving familyRestRowToActivation (familyRestLaw P m)
      ((familyBernoulli (familyTheta P)).prod (Measure.pi (fun _ : Fin m => familyMaskSignLaw P))) := by
  have ha := measurePreserving_prodAssoc (familySignLaw m) (familyBernoulli (familyTheta P)) (familyMaskLaw P m)
  have hb := (Measure.measurePreserving_swap (μ := familySignLaw m) (ν := familyBernoulli (familyTheta P))).prod
    (MeasurePreserving.id (familyMaskLaw P m))
  have hc := measurePreserving_prodAssoc (familyBernoulli (familyTheta P)) (familySignLaw m) (familyMaskLaw P m)
  have hpair : MeasurePreserving (fun z : FamilySigns m × FamilySigns m => fun u => (z.1 u, z.2 u))
      ((familySignLaw m).prod (familyMaskLaw P m)) (Measure.pi (fun _ : Fin m => familyMaskSignLaw P)) :=
    (measurePreserving_arrowProdEquivProdArrow Bool Bool (Fin m)
      (fun _ => familyBernoulli familyHalf) (fun _ => familyBernoulli (familyPi P))).symm
  have hd : MeasurePreserving
      (fun z : Bool × (FamilySigns m × FamilySigns m) => (z.1, fun u => (z.2.1 u, z.2.2 u)))
      ((familyBernoulli (familyTheta P)).prod ((familySignLaw m).prod (familyMaskLaw P m)))
      ((familyBernoulli (familyTheta P)).prod (Measure.pi (fun _ : Fin m => familyMaskSignLaw P))) :=
    (MeasurePreserving.id (familyBernoulli (familyTheta P))).prod hpair
  have ha' := MeasurePreserving.symm
    (MeasurableEquiv.prodAssoc : ((FamilySigns m × Bool) × FamilySigns m) ≃ᵐ (FamilySigns m × (Bool × FamilySigns m))) ha
  exact hd.comp (hc.comp (hb.comp ha'))

abbrev FamilyActivationColumnsSeed (n m : ℕ) := (Fin n → Bool) × (Fin m → Fin n → FamilyMaskSign)

def familyActivationColumnsLaw (P : SymmetricFamilyParameters) (n m : ℕ) : Measure (FamilyActivationColumnsSeed n m) :=
  (Measure.pi (fun _ : Fin n => familyBernoulli (familyTheta P))).prod
    (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P)))

instance familyActivationColumnsLaw_probability (P : SymmetricFamilyParameters) (n m : ℕ) :
    IsProbabilityMeasure (familyActivationColumnsLaw P n m) := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => familyMaskSignLaw P)) := by
    constructor
    simp [Measure.pi_univ]
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P))) := by
    constructor
    simp [Measure.pi_univ]
  constructor
  change ((Measure.pi (fun _ : Fin n => familyBernoulli (familyTheta P))).prod
    (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P)))) univ = 1
  rw [← univ_prod_univ, Measure.prod_prod]
  simp [Measure.pi_univ]

def familyRestToActivationColumns {n m : ℕ} (z : Fin n → FamilyRestSeed m) : FamilyActivationColumnsSeed n m :=
  (fun i => (z i).2.1, fun u i => ((z i).1 u, (z i).2.2 u))

theorem familyRestToActivationColumns_preserving (P : SymmetricFamilyParameters) (n m : ℕ) :
    MeasurePreserving familyRestToActivationColumns (familyRestArrayLaw P n m) (familyActivationColumnsLaw P n m) := by
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => familyMaskSignLaw P)) := by
    constructor
    simp [Measure.pi_univ]
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin m => familyMaskSignLaw P))) := by
    constructor
    simp [Measure.pi_univ]
  have hr := measurePreserving_pi (fun _ : Fin n => familyRestLaw P m)
    (fun _ : Fin n => (familyBernoulli (familyTheta P)).prod (Measure.pi (fun _ : Fin m => familyMaskSignLaw P)))
    (fun _ => familyRestRowToActivation_preserving P m)
  have ha := measurePreserving_arrowProdEquivProdArrow Bool (Fin m → FamilyMaskSign) (Fin n)
    (fun _ => familyBernoulli (familyTheta P)) (fun _ => Measure.pi (fun _ : Fin m => familyMaskSignLaw P))
  have hc : MeasurePreserving
      (fun z : (Fin n → Bool) × (Fin n → Fin m → FamilyMaskSign) => (z.1, fun u i => z.2 i u))
      ((Measure.pi (fun _ : Fin n => familyBernoulli (familyTheta P))).prod
        (Measure.pi (fun _ : Fin n => Measure.pi (fun _ : Fin m => familyMaskSignLaw P))))
      (familyActivationColumnsLaw P n m) :=
    (MeasurePreserving.id (Measure.pi (fun _ : Fin n => familyBernoulli (familyTheta P)))).prod
      (finite_product_columns_preserving (I := Fin n) (J := Fin m) (familyMaskSignLaw P))
  exact hc.comp (ha.comp hr)

def familyActivationColumnCount {n : ℕ} (I : Fin n → Bool) : ℕ := Finset.univ.sum (fun i => if I i then 1 else 0)
def familyActivationColumnSum {n : ℕ} (I : Fin n → Bool) (z : Fin n → FamilyMaskSign) : ℝ :=
  ∑ i, familyIndicator (I i) * familyIndicator (z i).2 * familySign (z i).1

theorem familyActivationCount_columns {n m : ℕ} (z : Fin n → FamilyRestSeed m) :
    familyActivationCount z = (familyActivationColumnCount (familyRestToActivationColumns z).1 : ℝ) := by
  simp only [familyActivationCount, familyActivationColumnCount, familyRestToActivationColumns, Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro i _
  simp [familyIndicator]

theorem familyMaskedSignCount_columns {n m : ℕ} (z : Fin n → FamilyRestSeed m) (u : Fin m) :
    familyMaskedSignCount z u = familyActivationColumnSum (familyRestToActivationColumns z).1 ((familyRestToActivationColumns z).2 u) := rfl

end
end RectangleCLT.Companion.SplitV4
