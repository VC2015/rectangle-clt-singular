import RectangleCLTArxivV1.LowerRectangularFamilyProperties
import RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts

/-! Exact separated maximum of the actual two-count observation array. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

abbrev LowerFamilySeparatedSeed (n r m : ℕ) :=
  (Fin n → FamilySigns r) × (Fin n → FamilyRestSeed m)

def lowerFamilySeparatedLaw (P : SymmetricFamilyParameters) (n r m : ℕ) :
    Measure (LowerFamilySeparatedSeed n r m) :=
  (familySignArrayLaw n r).prod (familyRestArrayLaw P n m)

instance lowerFamilySeparatedLaw_probability (P : SymmetricFamilyParameters) (n r m : ℕ) :
    IsProbabilityMeasure (lowerFamilySeparatedLaw P n r m) := by
  unfold lowerFamilySeparatedLaw
  infer_instance

def lowerFamilySeparatedJoin {n r m : ℕ} (z : LowerFamilySeparatedSeed n r m) :
    Fin n → LowerFamilySeed r m := fun i => (z.1 i,z.2 i)

theorem lowerFamilySeparatedJoin_preserving (P : SymmetricFamilyParameters) (n r m : ℕ) :
    MeasurePreserving lowerFamilySeparatedJoin (lowerFamilySeparatedLaw P n r m)
      (lowerFamilyArrayLaw P n r m) := by
  exact (measurePreserving_arrowProdEquivProdArrow (FamilySigns r) (FamilyRestSeed m) (Fin n)
    (fun _ => familySignLaw r) (fun _ => familyRestLaw P m)).symm

def lowerFamilySeparatedSum (P : SymmetricFamilyParameters) {n r m : ℕ}
    (z : LowerFamilySeparatedSeed n r m) : Vector (r*m) :=
  sumVector (lowerFamilyNormalizedObservations P) (lowerFamilySeparatedJoin z)

theorem lowerFamilySeparatedSum_coordinate (P : SymmetricFamilyParameters) {n r m : ℕ}
    (z : LowerFamilySeparatedSeed n r m) (ju : Fin r × Fin m) :
    lowerFamilySeparatedSum P z (finProdFinEquiv ju) = P.scale * familyRademacherCoordinate z.1 ju.1 +
      (P.amplitude / Real.sqrt n) * familyMaskedSignCount z.2 ju.2 := by
  simp only [lowerFamilySeparatedSum, sumVector, Finset.sum_apply, lowerFamilyNormalizedObservations,
    Pi.smul_apply, smul_eq_mul, lowerFamilyRawObservations, lowerFamilyObservation, Equiv.symm_apply_apply,
    lowerFamilySeparatedJoin, familyActivated, familyRademacherCoordinate, familyMaskedSignCount]
  simp_rw [mul_add]
  rw [Finset.sum_add_distrib]
  have h1 : (∑ i : Fin n, (1 / Real.sqrt (n : ℝ)) * (P.scale * familySign (z.1 i ju.1))) =
      (P.scale * (1 / Real.sqrt n)) * ∑ i, familySign (z.1 i ju.1) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have h2 : (∑ i : Fin n, (1 / Real.sqrt (n : ℝ)) *
      (P.amplitude * familyIndicator (z.2 i).2.1 * familyIndicator ((z.2 i).2.2 ju.2) * familySign ((z.2 i).1 ju.2))) =
      (P.amplitude / Real.sqrt n) * ∑ i, familyIndicator (z.2 i).2.1 * familyIndicator ((z.2 i).2.2 ju.2) * familySign ((z.2 i).1 ju.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [h1, h2]
  ring

theorem lowerFamilySeparatedSum_maximum (P : SymmetricFamilyParameters) {n r m : ℕ} [NeZero r] [NeZero m]
    (z : LowerFamilySeparatedSeed n r m) :
    finiteMaximum (fun ju : Fin r × Fin m => lowerFamilySeparatedSum P z (finProdFinEquiv ju)) =
      P.scale * familyRademacherMaximum z.1 + (P.amplitude / Real.sqrt n) * familyMaskedSignMaximum z.2 := by
  simp_rw [lowerFamilySeparatedSum_coordinate]
  exact finiteMaximum_separable _ _ P.scale_pos.le (div_nonneg P.amplitude_pos.le (Real.sqrt_nonneg _))

theorem lowerFamilySeparatedSum_identDistrib (P : SymmetricFamilyParameters) (n r m : ℕ) :
    IdentDistrib (lowerFamilySeparatedSum P : LowerFamilySeparatedSeed n r m → Vector (r * m))
      (sumVector (lowerFamilyNormalizedObservations P)) (lowerFamilySeparatedLaw P n r m) (lowerFamilyArrayLaw P n r m) := by
  have hp := lowerFamilySeparatedJoin_preserving P n r m
  have hi : IdentDistrib lowerFamilySeparatedJoin id (lowerFamilySeparatedLaw P n r m) (lowerFamilyArrayLaw P n r m) :=
    ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact hp.map_eq⟩
  exact hi.comp (measurable_of_finite _)

theorem lowerFamilySeparated_maxima_independent (P : SymmetricFamilyParameters) (n r m : ℕ) [NeZero r] [NeZero m] :
    IndepFun (fun z : LowerFamilySeparatedSeed n r m => familyRademacherMaximum z.1)
      (fun z => familyMaskedSignMaximum z.2) (lowerFamilySeparatedLaw P n r m) := by
  have hi : IndepFun Prod.fst Prod.snd ((familySignArrayLaw n r).prod (familyRestArrayLaw P n m)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    simp only [show (fun z : LowerFamilySeparatedSeed n r m => (z.1, z.2)) = id from rfl,
      Measure.map_id, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
  exact hi.comp
    (measurable_of_finite (familyRademacherMaximum : (Fin n → FamilySigns r) → ℝ))
    (measurable_of_finite (familyMaskedSignMaximum : (Fin n → FamilyRestSeed m) → ℝ))

end
end RectangleCLTArxivV1
