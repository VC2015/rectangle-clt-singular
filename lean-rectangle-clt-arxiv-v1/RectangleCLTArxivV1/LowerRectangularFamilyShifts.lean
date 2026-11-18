import RectangleCLTArxivV1.LowerRectangularFamilyMaximum
import RectangleCLTArxivV1.LowerRectangularFamilyGaussian
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaster

/-! The actual independent shifts for the two-count lower family. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def lowerFamilyGaussianPairLaw (r m : ℕ) : Measure (Vector r × Vector m) :=
  (standardGaussian r).prod (standardGaussian m)

instance lowerFamilyGaussianPairLaw_probability (r m : ℕ) :
    IsProbabilityMeasure (lowerFamilyGaussianPairLaw r m) := by unfold lowerFamilyGaussianPairLaw; infer_instance

theorem lowerFamilyGaussianPairMap_maximum (P : SymmetricFamilyParameters) {r m : ℕ}
    [NeZero r] [NeZero m] (z : Vector r × Vector m) :
    finiteMaximum (fun ju : Fin r × Fin m => lowerGridGaussianMap P.scale (Real.sqrt P.variance) z
      (finProdFinEquiv ju)) = P.scale*finiteMaximum z.1+Real.sqrt P.variance*finiteMaximum z.2 := by
  simp only [lowerGridGaussianMap,Equiv.symm_apply_apply]
  exact finiteMaximum_separable _ _ P.scale_pos.le (Real.sqrt_nonneg _)

theorem lowerFamilySeparatedSum_scaled_maximum (P : SymmetricFamilyParameters) {n r m : ℕ}
    [NeZero r] [NeZero m] (z : LowerFamilySeparatedSeed n r m) :
    finiteMaximum (fun ju : Fin r × Fin m => lowerFamilySeparatedSum P z (finProdFinEquiv ju)) =
      P.scale*(familyRademacherMaximum z.1+familyObservationShift P z.2) := by
  rw [lowerFamilySeparatedSum_maximum]
  unfold familyObservationShift
  simp_rw [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = P.scale * familyRademacherMaximum z.1 + (P.scale * P.scale⁻¹) *
        (P.amplitude * (Real.sqrt (n : ℝ))⁻¹ * familyMaskedSignMaximum z.2) := by
      rw [mul_inv_cancel₀ P.scale_pos.ne']
      ring
    _ = _ := by ring

theorem lowerFamilyGaussianPairMap_scaled_maximum (P : SymmetricFamilyParameters) {r m : ℕ}
    [NeZero r] [NeZero m] (z : Vector r × Vector m) :
    finiteMaximum (fun ju : Fin r × Fin m => lowerGridGaussianMap P.scale (Real.sqrt P.variance) z
      (finProdFinEquiv ju)) = P.scale*(finiteMaximum z.1+familyGaussianShift P z.2) := by
  rw [lowerFamilyGaussianPairMap_maximum]
  unfold familyGaussianShift
  field_simp [P.scale_pos.ne']
  ring

theorem lowerFamilyObservationShift_independent (P : SymmetricFamilyParameters) (n r m : ℕ)
    [NeZero r] [NeZero m] :
    IndepFun (fun z : LowerFamilySeparatedSeed n r m => familyRademacherMaximum z.1)
      (fun z => familyObservationShift P z.2) (lowerFamilySeparatedLaw P n r m) :=
  (lowerFamilySeparated_maxima_independent P n r m).comp measurable_id (measurable_const.mul measurable_id)

theorem lowerFamilyGaussianShift_independent (P : SymmetricFamilyParameters) (r m : ℕ)
    [NeZero r] [NeZero m] :
    IndepFun (fun z : Vector r × Vector m => finiteMaximum z.1)
      (fun z => familyGaussianShift P z.2) (lowerFamilyGaussianPairLaw r m) := by
  have hi : IndepFun Prod.fst Prod.snd ((standardGaussian r).prod (standardGaussian m)) := by
    apply (indepFun_iff_map_prod_eq_prod_map_map measurable_fst.aemeasurable measurable_snd.aemeasurable).mpr
    simp only [show (fun z : Vector r × Vector m => (z.1,z.2)) = id from rfl,
      Measure.map_id,Measure.map_fst_prod,Measure.map_snd_prod,measure_univ,one_smul]
  have hm (d : ℕ) [NeZero d] : Measurable (finiteMaximum : Vector d → ℝ) :=
    measurable_finiteMaximum (fun j (z : Vector d) => z j) (fun j => measurable_pi_apply j)
  exact hi.comp (hm r) (measurable_const.mul (hm m))

theorem lowerFamilyRademacher_realCDF (P : SymmetricFamilyParameters) (n r m : ℕ)
    [NeZero r] (t : ℝ) :
    realCDF (lowerFamilySeparatedLaw P n r m) (fun z : LowerFamilySeparatedSeed n r m =>
      familyRademacherMaximum z.1) t =
      (familySignArrayLaw n r).real {z | familyRademacherMaximum z ≤ t} :=
  realCDF_product_fst _ _ _ (measurable_of_finite _) t

theorem lowerFamilyGaussian_realCDF (r m : ℕ) [NeZero r] (t : ℝ) :
    realCDF (lowerFamilyGaussianPairLaw r m) (fun z : Vector r × Vector m => finiteMaximum z.1) t =
      normalMaximumCDF r t := by
  unfold lowerFamilyGaussianPairLaw
  rw [realCDF_product_fst _ _ finiteMaximum
    (measurable_finiteMaximum (fun j (z : Vector r) => z j) (fun j => measurable_pi_apply j))]
  exact finiteGaussianMaximum_cdf r t

def lowerFamilyShiftedCDFDifference (P : SymmetricFamilyParameters) (n r m : ℕ)
    [NeZero r] [NeZero m] (t : ℝ) : ℝ :=
  (lowerFamilySeparatedLaw P n r m).real {z | familyRademacherMaximum z.1+familyObservationShift P z.2 ≤ t}-
    (lowerFamilyGaussianPairLaw r m).real {z | finiteMaximum z.1+familyGaussianShift P z.2 ≤ t}

end
end RectangleCLTArxivV1
