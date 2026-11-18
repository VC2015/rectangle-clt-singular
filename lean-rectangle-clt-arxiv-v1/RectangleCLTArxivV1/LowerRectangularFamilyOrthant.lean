import RectangleCLTArxivV1.LowerRectangularFamilyMaster
import RectangleCLTCompanion.SplitV4.SymmetricFamilyOrthant

/-! The actual signed comparison detects a genuine rectangle discrepancy. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem finiteMaximum_rectangular_pair_le_iff {r m : ℕ} [NeZero r] [NeZero m]
    (w : Vector (r*m)) (b : ℝ) :
    finiteMaximum (fun ju : Fin r × Fin m => w (finProdFinEquiv ju)) ≤ b ↔ ∀ j, w j ≤ b := by
  constructor
  · intro h j
    have hh := (le_finiteMaximum (fun ju : Fin r × Fin m => w (finProdFinEquiv ju))
      (finProdFinEquiv.symm j)).trans h
    simpa only [Equiv.apply_symm_apply] using hh
  · intro h
    exact finiteMaximum_le _ (fun ju => h _)

theorem lowerFamilySeparatedShift_orthant_event (P : SymmetricFamilyParameters)
    {n r m : ℕ} [NeZero r] [NeZero m] (t : ℝ) :
    {z : LowerFamilySeparatedSeed n r m | familyRademacherMaximum z.1+familyObservationShift P z.2 ≤ t} =
      lowerFamilySeparatedSum P ⁻¹' (familyOrthant (r*m) (P.scale*t)).carrier := by
  ext z
  simp only [mem_setOf_eq,mem_preimage,familyOrthant_carrier]
  rw [← finiteMaximum_rectangular_pair_le_iff,lowerFamilySeparatedSum_scaled_maximum,mul_le_mul_left P.scale_pos]

theorem lowerFamilyGaussianShift_orthant_event (P : SymmetricFamilyParameters)
    {r m : ℕ} [NeZero r] [NeZero m] (t : ℝ) :
    {z : Vector r × Vector m | finiteMaximum z.1+familyGaussianShift P z.2 ≤ t} =
      lowerGridGaussianMap P.scale (Real.sqrt P.variance) ⁻¹'
        (familyOrthant (r*m) (P.scale*t)).carrier := by
  ext z
  simp only [mem_setOf_eq,mem_preimage,familyOrthant_carrier]
  rw [← finiteMaximum_rectangular_pair_le_iff,lowerFamilyGaussianPairMap_scaled_maximum,mul_le_mul_left P.scale_pos]

theorem lowerFamilyShiftedCDFDifference_rectangleError (P : SymmetricFamilyParameters)
    (n r m : ℕ) [NeZero r] [NeZero m]
    (A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ)
    (hA : A*A.transpose = lowerFamilyCovariance r m P.variance) (t : ℝ) :
    rectangleError (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P)) A
      (familyOrthant (r*m) (P.scale*t)) = |lowerFamilyShiftedCDFDifference P n r m t| := by
  let R := familyOrthant (r*m) (P.scale*t)
  have hW : (lowerFamilySeparatedLaw P n r m).real
      {z | familyRademacherMaximum z.1+familyObservationShift P z.2 ≤ t} =
      (lowerFamilyArrayLaw P n r m).real ((sumVector (lowerFamilyNormalizedObservations P)) ⁻¹' R.carrier) := by
    rw [lowerFamilySeparatedShift_orthant_event]
    exact congrArg ENNReal.toReal ((lowerFamilySeparatedSum_identDistrib P n r m).measure_mem_eq R.measurableSet_carrier)
  have hG : (lowerFamilyGaussianPairLaw r m).real
      {z | finiteMaximum z.1+familyGaussianShift P z.2 ≤ t} = (gaussianLaw A).real R.carrier := by
    rw [lowerFamilyGaussianShift_orthant_event]
    have hh := congrArg (fun μ : Measure (Vector (r*m)) => μ.real R.carrier)
      (lowerFamilyGaussianLaw_eq P A hA)
    unfold lowerGridGaussianLaw at hh
    dsimp only at hh
    rw [map_measureReal_apply (lowerGridGaussianMap_measurable r m P.scale (Real.sqrt P.variance))
      R.measurableSet_carrier] at hh
    exact hh
  unfold rectangleError lowerFamilyShiftedCDFDifference
  rw [hW,hG]

def lowerFamilyComparisonDistance (P : SymmetricFamilyParameters) (n r m : ℕ) : ℝ :=
  rectangleDistance (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P))
    (lowerFamilyGaussianFactor P r m)

theorem abs_lowerFamilyShiftedCDFDifference_le_distance (P : SymmetricFamilyParameters)
    (n r m : ℕ) [NeZero r] [NeZero m] (t : ℝ) :
    |lowerFamilyShiftedCDFDifference P n r m t| ≤ lowerFamilyComparisonDistance P n r m := by
  rw [← lowerFamilyShiftedCDFDifference_rectangleError P n r m (lowerFamilyGaussianFactor P r m)
    (lowerFamilyGaussianFactor_gram P r m) t]
  exact rectangleError_le_rectangleDistance _ _ _ _

end
end RectangleCLTArxivV1
