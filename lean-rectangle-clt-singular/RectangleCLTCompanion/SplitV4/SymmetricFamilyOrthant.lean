import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster
import RectangleCLTCompanion.RectangleDistance

/-! The actual shifted comparison is an error on one genuine detecting rectangle. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyOrthant (p : ℕ) (t : ℝ) : Rect p where
  interval _ := Iic t
  ordConnected _ := ordConnected_Iic
  measurable _ := measurableSet_Iic

theorem familyOrthant_carrier (p : ℕ) (t : ℝ) : (familyOrthant p t).carrier = {z | ∀ j, z j ≤ t} := by
  ext z
  simp only [Rect.carrier, familyOrthant, mem_pi, mem_univ, forall_const, mem_Iic, mem_setOf_eq]

theorem finiteMaximum_pair_le_iff {m : ℕ} [NeZero m] (w : Vector (m * m)) (b : ℝ) :
    finiteMaximum (fun ju : Fin m × Fin m => w (finProdFinEquiv ju)) ≤ b ↔ ∀ j, w j ≤ b := by
  constructor
  · intro h j
    have hh := (le_finiteMaximum (fun ju : Fin m × Fin m => w (finProdFinEquiv ju)) (finProdFinEquiv.symm j)).trans h
    simpa only [Equiv.apply_symm_apply] using hh
  · intro h
    exact finiteMaximum_le _ (fun ju => h _)

theorem familySeparatedShift_orthant_event (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m] (t : ℝ) :
    {z : FamilySeparatedSeed n m | familyRademacherMaximum z.1 + familyObservationShift P z.2 ≤ t} =
      familySeparatedSum P ⁻¹' (familyOrthant (m * m) (P.scale * t)).carrier := by
  ext z
  simp only [mem_setOf_eq, mem_preimage, familyOrthant_carrier]
  rw [← finiteMaximum_pair_le_iff, familySeparatedSum_scaled_maximum, mul_le_mul_left P.scale_pos]

theorem familyGaussianShift_orthant_event (P : SymmetricFamilyParameters) {m : ℕ} [NeZero m] (t : ℝ) :
    {z : Vector m × Vector m | finiteMaximum z.1 + familyGaussianShift P z.2 ≤ t} =
      familyGaussianPairMap P ⁻¹' (familyOrthant (m * m) (P.scale * t)).carrier := by
  ext z
  simp only [mem_setOf_eq, mem_preimage, familyOrthant_carrier]
  rw [← finiteMaximum_pair_le_iff, familyGaussianPairMap_scaled_maximum, mul_le_mul_left P.scale_pos]

theorem familyShiftedCDFDifference_rectangleError (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m]
    (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ) (hA : A * A.transpose = familyCovariance m P.variance) (t : ℝ) :
    rectangleError (familyArrayLaw P n m) (sumVector (familyNormalizedObservations P)) A
      (familyOrthant (m * m) (P.scale * t)) = |familyShiftedCDFDifference P n m t| := by
  let R := familyOrthant (m * m) (P.scale * t)
  have hW : (familySeparatedLaw P n m).real {z | familyRademacherMaximum z.1 + familyObservationShift P z.2 ≤ t} =
      (familyArrayLaw P n m).real ((sumVector (familyNormalizedObservations P)) ⁻¹' R.carrier) := by
    rw [familySeparatedShift_orthant_event]
    exact congrArg ENNReal.toReal ((familySeparatedSum_identDistrib P n m).measure_mem_eq R.measurableSet_carrier)
  have hG : (familyGaussianPairLaw m).real {z | finiteMaximum z.1 + familyGaussianShift P z.2 ≤ t} =
      (gaussianLaw A).real R.carrier := by
    rw [familyGaussianShift_orthant_event]
    have hh := congrArg (fun μ : Measure (Vector (m * m)) => μ.real R.carrier) (familyGaussianPairMap_eq_gaussianLaw P A hA)
    dsimp only at hh
    rw [map_measureReal_apply (measurable_familyGaussianPairMap P m) R.measurableSet_carrier] at hh
    exact hh
  unfold rectangleError familyShiftedCDFDifference
  rw [hW, hG]

def familyGaussianSquareFactor (P : SymmetricFamilyParameters) (m : ℕ) : Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  Classical.choose (familyCovariance_factor_exists P m)

theorem familyGaussianSquareFactor_gram (P : SymmetricFamilyParameters) (m : ℕ) :
    familyGaussianSquareFactor P m * (familyGaussianSquareFactor P m).transpose = familyCovariance m P.variance :=
  Classical.choose_spec (familyCovariance_factor_exists P m)

def familyComparisonDistance (P : SymmetricFamilyParameters) (n m : ℕ) : ℝ :=
  rectangleDistance (familyArrayLaw P n m) (sumVector (familyNormalizedObservations P)) (familyGaussianSquareFactor P m)

theorem abs_familyShiftedCDFDifference_le_distance (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] (t : ℝ) :
    |familyShiftedCDFDifference P n m t| ≤ familyComparisonDistance P n m := by
  rw [← familyShiftedCDFDifference_rectangleError P n m (familyGaussianSquareFactor P m) (familyGaussianSquareFactor_gram P m) t]
  exact rectangleError_le_rectangleDistance _ _ _ _

theorem familyShiftedCDFDifference_le_distance (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] (t : ℝ) :
    familyShiftedCDFDifference P n m t ≤ familyComparisonDistance P n m :=
  (le_abs_self _).trans (abs_familyShiftedCDFDifference_le_distance P n m t)

end
end RectangleCLT.Companion.SplitV4
