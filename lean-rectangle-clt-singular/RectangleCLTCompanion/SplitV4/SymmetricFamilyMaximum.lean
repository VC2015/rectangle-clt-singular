import RectangleCLTCompanion.SplitV4.SymmetricFamilyCertification
import Mathlib.MeasureTheory.Constructions.Pi

/-! Exact maximum decomposition of the common masked family, including independent shifts. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty f

theorem le_finiteMaximum {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) (i : ι) : f i ≤ finiteMaximum f :=
  Finset.le_sup' f (Finset.mem_univ i)

theorem finiteMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) {b : ℝ}
    (hb : ∀ i, f i ≤ b) : finiteMaximum f ≤ b := Finset.sup'_le _ _ (fun i _ => hb i)

theorem finiteMaximum_attains {ι : Type*} [Fintype ι] [Nonempty ι] (f : ι → ℝ) :
    ∃ i, f i = finiteMaximum f := by
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup' Finset.univ_nonempty f
  exact ⟨i, hi.symm⟩

theorem measurable_finiteMaximum {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] [Nonempty ι]
    (f : ι → Ω → ℝ) (hf : ∀ i, Measurable (f i)) : Measurable (fun ω => finiteMaximum (fun i => f i ω)) := by
  have heq : (fun ω => finiteMaximum (fun i => f i ω)) = Finset.univ.sup' Finset.univ_nonempty f := by
    funext ω
    rw [Finset.sup'_apply]
    rfl
  rw [heq]
  exact Finset.measurable_sup' Finset.univ_nonempty (fun i _ => hf i)

theorem finiteMaximum_separable {ι κ : Type*} [Fintype ι] [Nonempty ι] [Fintype κ] [Nonempty κ]
    (f : ι → ℝ) (g : κ → ℝ) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    finiteMaximum (fun ij : ι × κ => a * f ij.1 + b * g ij.2) = a * finiteMaximum f + b * finiteMaximum g := by
  apply le_antisymm
  · apply finiteMaximum_le
    intro ij
    exact add_le_add (mul_le_mul_of_nonneg_left (le_finiteMaximum f ij.1) ha)
      (mul_le_mul_of_nonneg_left (le_finiteMaximum g ij.2) hb)
  · obtain ⟨i, hi⟩ := finiteMaximum_attains f
    obtain ⟨j, hj⟩ := finiteMaximum_attains g
    simpa only [hi, hj] using le_finiteMaximum (fun ij : ι × κ => a * f ij.1 + b * g ij.2) (i, j)

abbrev FamilyRestSeed (m : ℕ) := FamilySigns m × (Bool × FamilySigns m)
abbrev FamilySeparatedSeed (n m : ℕ) := (Fin n → FamilySigns m) × (Fin n → FamilyRestSeed m)

def familySignArrayLaw (n m : ℕ) : Measure (Fin n → FamilySigns m) := Measure.pi (fun _ => familySignLaw m)
def familyRestArrayLaw (P : SymmetricFamilyParameters) (n m : ℕ) : Measure (Fin n → FamilyRestSeed m) :=
  Measure.pi (fun _ => familyRestLaw P m)
def familySeparatedLaw (P : SymmetricFamilyParameters) (n m : ℕ) : Measure (FamilySeparatedSeed n m) :=
  (familySignArrayLaw n m).prod (familyRestArrayLaw P n m)

instance familySignArrayLaw_probability (n m : ℕ) : IsProbabilityMeasure (familySignArrayLaw n m) := by
  constructor
  simp [familySignArrayLaw, Measure.pi_univ]
instance familyRestArrayLaw_probability (P : SymmetricFamilyParameters) (n m : ℕ) :
    IsProbabilityMeasure (familyRestArrayLaw P n m) := by
  constructor
  simp [familyRestArrayLaw, Measure.pi_univ]
instance familySeparatedLaw_probability (P : SymmetricFamilyParameters) (n m : ℕ) :
    IsProbabilityMeasure (familySeparatedLaw P n m) := by unfold familySeparatedLaw; infer_instance

def familySeparatedJoin {n m : ℕ} (z : FamilySeparatedSeed n m) : Fin n → FamilySeed m := fun i => (z.1 i, z.2 i)

theorem familySeparatedJoin_preserving (P : SymmetricFamilyParameters) (n m : ℕ) :
    MeasurePreserving familySeparatedJoin (familySeparatedLaw P n m) (familyArrayLaw P n m) := by
  exact (measurePreserving_arrowProdEquivProdArrow (FamilySigns m) (FamilyRestSeed m) (Fin n)
    (fun _ => familySignLaw m) (fun _ => familyRestLaw P m)).symm

def familyRademacherCoordinate {n m : ℕ} (z : Fin n → FamilySigns m) (j : Fin m) : ℝ :=
  (1 / Real.sqrt n) * ∑ i, familySign (z i j)
def familyActivationCount {n m : ℕ} (z : Fin n → FamilyRestSeed m) : ℝ := ∑ i, familyIndicator (z i).2.1
def familyMaskedSignCount {n m : ℕ} (z : Fin n → FamilyRestSeed m) (u : Fin m) : ℝ :=
  ∑ i, familyIndicator (z i).2.1 * familyIndicator ((z i).2.2 u) * familySign ((z i).1 u)
def familyRademacherMaximum {n m : ℕ} [NeZero m] (z : Fin n → FamilySigns m) : ℝ :=
  finiteMaximum (familyRademacherCoordinate z)
def familyMaskedSignMaximum {n m : ℕ} [NeZero m] (z : Fin n → FamilyRestSeed m) : ℝ :=
  finiteMaximum (familyMaskedSignCount z)

def familySeparatedSum (P : SymmetricFamilyParameters) {n m : ℕ} (z : FamilySeparatedSeed n m) : Vector (m * m) :=
  sumVector (familyNormalizedObservations P) (familySeparatedJoin z)

theorem familySeparatedSum_coordinate (P : SymmetricFamilyParameters) {n m : ℕ}
    (z : FamilySeparatedSeed n m) (ju : Fin m × Fin m) :
    familySeparatedSum P z (finProdFinEquiv ju) = P.scale * familyRademacherCoordinate z.1 ju.1 +
      (P.amplitude / Real.sqrt n) * familyMaskedSignCount z.2 ju.2 := by
  simp only [familySeparatedSum, sumVector, Finset.sum_apply, familyNormalizedObservations,
    Pi.smul_apply, smul_eq_mul, familyRawObservations, familyObservation, Equiv.symm_apply_apply,
    familySeparatedJoin, familyActivated, familyRademacherCoordinate, familyMaskedSignCount]
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

theorem familySeparatedSum_maximum (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (z : FamilySeparatedSeed n m) :
    finiteMaximum (fun ju : Fin m × Fin m => familySeparatedSum P z (finProdFinEquiv ju)) =
      P.scale * familyRademacherMaximum z.1 + (P.amplitude / Real.sqrt n) * familyMaskedSignMaximum z.2 := by
  simp_rw [familySeparatedSum_coordinate]
  exact finiteMaximum_separable _ _ P.scale_pos.le (div_nonneg P.amplitude_pos.le (Real.sqrt_nonneg _))

theorem familySeparatedSum_identDistrib (P : SymmetricFamilyParameters) (n m : ℕ) :
    IdentDistrib (familySeparatedSum P : FamilySeparatedSeed n m → Vector (m * m))
      (sumVector (familyNormalizedObservations P)) (familySeparatedLaw P n m) (familyArrayLaw P n m) := by
  have hp := familySeparatedJoin_preserving P n m
  have hi : IdentDistrib familySeparatedJoin id (familySeparatedLaw P n m) (familyArrayLaw P n m) :=
    ⟨hp.measurable.aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact hp.map_eq⟩
  exact hi.comp (measurable_of_finite _)

theorem familySeparated_maxima_independent (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    IndepFun (fun z : FamilySeparatedSeed n m => familyRademacherMaximum z.1)
      (fun z => familyMaskedSignMaximum z.2) (familySeparatedLaw P n m) := by
  have hi : IndepFun Prod.fst Prod.snd ((familySignArrayLaw n m).prod (familyRestArrayLaw P n m)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    simp only [show (fun z : FamilySeparatedSeed n m => (z.1, z.2)) = id from rfl,
      Measure.map_id, Measure.map_fst_prod, Measure.map_snd_prod, measure_univ, one_smul]
  exact hi.comp
    (measurable_of_finite (familyRademacherMaximum : (Fin n → FamilySigns m) → ℝ))
    (measurable_of_finite (familyMaskedSignMaximum : (Fin n → FamilyRestSeed m) → ℝ))

end
end RectangleCLT.Companion.SplitV4
