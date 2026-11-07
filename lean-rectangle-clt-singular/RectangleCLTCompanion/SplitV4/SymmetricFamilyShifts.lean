import RectangleCLTCompanion.SplitV4.SymmetricFamilyGaussian
import RectangleCLTCompanion.SplitV4.GaussianExtremeMoments
import RectangleCLTCompanion.SplitV4.ShiftComparison

/-! The actual independent scalar shifts in the symmetric-family maximum comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyObservationShift (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (z : Fin n → FamilyRestSeed m) : ℝ := P.amplitude / (P.scale * Real.sqrt n) * familyMaskedSignMaximum z

def familyGaussianShift (P : SymmetricFamilyParameters) {m : ℕ} [NeZero m] (z : Vector m) : ℝ :=
  Real.sqrt P.variance / P.scale * finiteMaximum z

theorem familyObservationShift_integral (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (∫ z, familyObservationShift P z ∂familyRestArrayLaw P n m) = P.amplitude / (P.scale * Real.sqrt n) *
      ∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m := integral_const_mul _ _

theorem familyObservationShift_sq_integral_le (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (∫ z, familyObservationShift P z ^ 2 ∂familyRestArrayLaw P n m) ≤
      (P.amplitude / (P.scale * Real.sqrt n)) ^ 2 * (((n : ℝ) * P.theta) ^ 2 + (n : ℝ) * P.theta) := by
  simp_rw [familyObservationShift, mul_pow]
  rw [integral_const_mul]
  simpa only [mul_pow] using mul_le_mul_of_nonneg_left (integral_familyMaskedSignMaximum_sq_le P n m)
    (sq_nonneg (P.amplitude / (P.scale * Real.sqrt n)))

theorem familyGaussianShift_integrable (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    Integrable (familyGaussianShift P : Vector m → ℝ) (standardGaussian m) :=
  (integrable_finiteGaussianMaximum m).const_mul _

theorem familyGaussianShift_sq_integrable (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    Integrable (fun z : Vector m => familyGaussianShift P z ^ 2) (standardGaussian m) := by
  simpa only [familyGaussianShift, mul_pow] using (integrable_finiteGaussianMaximum_sq m).const_mul
    ((Real.sqrt P.variance / P.scale) ^ 2)

theorem familyGaussianShift_integral (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    (∫ z, familyGaussianShift P z ∂standardGaussian m) =
      Real.sqrt P.variance / P.scale * gaussianMaximumMean m := by
  change (∫ z, (Real.sqrt P.variance / P.scale) * finiteMaximum z ∂standardGaussian m) = _
  rw [integral_const_mul, ← gaussianMaximumMean_eq_integral]

theorem familyGaussianShift_sq_integral_le (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    (∫ z, familyGaussianShift P z ^ 2 ∂standardGaussian m) ≤
      (Real.sqrt P.variance / P.scale) ^ 2 * (Real.exp (11 / 2) * dimensionLog m) := by
  simp_rw [familyGaussianShift, mul_pow]
  rw [integral_const_mul]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_left (integral_finiteGaussianMaximum_sq_le m)
    (sq_nonneg (Real.sqrt P.variance / P.scale))

theorem realCDF_product_fst {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A : Ω → ℝ) (hA : Measurable A) (t : ℝ) :
    realCDF (μ.prod ν) (fun z : Ω × Γ => A z.1) t = realCDF μ A t := by
  unfold realCDF
  have heq : {z : Ω × Γ | A z.1 ≤ t} = {ω | A ω ≤ t} ×ˢ univ := by ext z; simp
  rw [heq, Measure.real, Measure.prod_prod]
  simp only [measure_univ, mul_one]
  rfl

theorem familyRademacher_realCDF (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] (t : ℝ) :
    realCDF (familySeparatedLaw P n m) (fun z : FamilySeparatedSeed n m => familyRademacherMaximum z.1) t =
      (familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ t} :=
  realCDF_product_fst _ _ _ (measurable_of_finite _) t

theorem familyGaussian_realCDF (m : ℕ) [NeZero m] (t : ℝ) :
    realCDF (familyGaussianPairLaw m) (fun z : Vector m × Vector m => finiteMaximum z.1) t = normalMaximumCDF m t := by
  unfold familyGaussianPairLaw
  rw [realCDF_product_fst _ _ finiteMaximum (measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j))]
  exact finiteGaussianMaximum_cdf m t

theorem contDiff_standardNormalCDF_two : ContDiff ℝ 2 standardNormalCDF := by
  have hpdf : ContDiff ℝ 1 standardNormalPDF := by
    have heq : standardNormalPDF = fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) :=
      funext standardNormalPDF_eq
    rw [heq]
    exact contDiff_const.mul (((contDiff_id.pow 2).neg.div_const 2).exp)
  have hderiv : deriv standardNormalCDF = standardNormalPDF := funext (fun x => (hasDerivAt_standardNormalCDF x).deriv)
  change ContDiff ℝ ((1 : WithTop ℕ∞) + 1) standardNormalCDF
  apply contDiff_succ_iff_deriv.mpr
  refine ⟨fun x => (hasDerivAt_standardNormalCDF x).differentiableAt, by simp, ?_⟩
  rw [hderiv]
  exact hpdf

theorem contDiff_normalMaximumCDF_two (m : ℕ) : ContDiff ℝ 2 (normalMaximumCDF m) :=
  contDiff_standardNormalCDF_two.pow m

theorem deriv_normalMaximumCDF (m : ℕ) : deriv (normalMaximumCDF m) = normalMaximumDensity m :=
  funext (fun t => (hasDerivAt_normalMaximumCDF m t).deriv)

theorem familyObservationShift_independent (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    IndepFun (fun z : FamilySeparatedSeed n m => familyRademacherMaximum z.1)
      (fun z => familyObservationShift P z.2) (familySeparatedLaw P n m) := by
  exact (familySeparated_maxima_independent P n m).comp measurable_id (measurable_const.mul measurable_id)

theorem familyGaussianShift_independent (P : SymmetricFamilyParameters) (m : ℕ) [NeZero m] :
    IndepFun (fun z : Vector m × Vector m => finiteMaximum z.1)
      (fun z => familyGaussianShift P z.2) (familyGaussianPairLaw m) :=
  (familyGaussian_maxima_independent m).comp measurable_id (measurable_const.mul measurable_id)

theorem familySeparatedSum_scaled_maximum (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (z : FamilySeparatedSeed n m) :
    finiteMaximum (fun ju : Fin m × Fin m => familySeparatedSum P z (finProdFinEquiv ju)) =
      P.scale * (familyRademacherMaximum z.1 + familyObservationShift P z.2) := by
  rw [familySeparatedSum_maximum]
  unfold familyObservationShift
  simp_rw [div_eq_mul_inv, mul_inv_rev]
  calc
    _ = P.scale * familyRademacherMaximum z.1 + (P.scale * P.scale⁻¹) *
        (P.amplitude * (Real.sqrt (n : ℝ))⁻¹ * familyMaskedSignMaximum z.2) := by
      rw [mul_inv_cancel₀ P.scale_pos.ne']
      ring
    _ = _ := by ring

theorem familyGaussianPairMap_scaled_maximum (P : SymmetricFamilyParameters) {m : ℕ} [NeZero m]
    (z : Vector m × Vector m) :
    finiteMaximum (fun ju : Fin m × Fin m => familyGaussianPairMap P z (finProdFinEquiv ju)) =
      P.scale * (finiteMaximum z.1 + familyGaussianShift P z.2) := by
  rw [familyGaussianPairMap_maximum]
  unfold familyGaussianShift
  field_simp [P.scale_pos.ne']
  ring

end
end RectangleCLT.Companion.SplitV4
