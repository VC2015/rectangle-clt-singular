import RectangleCLTArxivV1.LowerRectangularFamilyShifts
import RectangleCLTArxivV1.LowerLeadingCalibration

/-! The signed, global two-count maximum comparison in Appendix F.3. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lowerFamily_master_comparison (P : SymmetricFamilyParameters)
    {n r m : ℕ} [NeZero r] [NeZero m] (hr : 1 ≤ r) {ε : ℝ} (hε : 0 ≤ ε)
    (hCDF : ∀ x, |(familySignArrayLaw n r).real {z | familyRademacherMaximum z ≤ x}-normalMaximumCDF r x| ≤ ε)
    (t : ℝ) :
    |lowerFamilyShiftedCDFDifference P n r m t-normalMaximumDensity r t*familyShiftMeanDifference P n m| ≤
      ε+(lowerGaussianCurvatureConstant*dimensionLog r/2)*familyShiftSecondMoments P n m := by
  let μ := lowerFamilySeparatedLaw P n r m
  let ν := lowerFamilyGaussianPairLaw r m
  let A : LowerFamilySeparatedSeed n r m → ℝ := fun z => familyRademacherMaximum z.1
  let U : LowerFamilySeparatedSeed n r m → ℝ := fun z => familyObservationShift P z.2
  let G : Vector r × Vector m → ℝ := fun z => finiteMaximum z.1
  let V : Vector r × Vector m → ℝ := fun z => familyGaussianShift P z.2
  have hmax {d : ℕ} [NeZero d] : Measurable (finiteMaximum : Vector d → ℝ) :=
    measurable_finiteMaximum (fun j (z : Vector d) => z j) (fun j => measurable_pi_apply j)
  have hA : Measurable A := measurable_of_finite _
  have hU : Measurable U := measurable_of_finite _
  have hG : Measurable G := hmax.comp measurable_fst
  have hV : Measurable V := measurable_const.mul (hmax.comp measurable_snd)
  have hU2 : Integrable (fun z => U z^2) μ := integrable_family_finite _ _
  have hsnd : MeasurePreserving Prod.snd ν (standardGaussian m) := by
    refine ⟨measurable_snd, ?_⟩
    simp only [ν,lowerFamilyGaussianPairLaw,Measure.map_snd_prod,measure_univ,one_smul]
  have hV2 : Integrable (fun z => V z^2) ν :=
    (hsnd.integrable_comp (familyGaussianShift_sq_integrable P m).aestronglyMeasurable).mpr
      (familyGaussianShift_sq_integrable P m)
  have hFG : realCDF ν G = normalMaximumCDF r := funext (lowerFamilyGaussian_realCDF r m)
  have hF : ContDiff ℝ 2 (realCDF ν G) := by rw [hFG]; exact contDiff_normalMaximumCDF_two r
  have hB (x : ℝ) : |deriv (deriv (realCDF ν G)) x| ≤ lowerGaussianCurvatureConstant*dimensionLog r := by
    rw [hFG]
    exact normalMaximumCDF_second_derivative_bound_positive_count hr x
  have hCDF' : realCDFDistance μ A ν G ≤ ε := by
    apply (realCDFDistance_le_iff μ A ν G ε).mpr
    intro x
    rw [lowerFamilyRademacher_realCDF,lowerFamilyGaussian_realCDF]
    exact hCDF x
  have hh := independent_shift_comparison_of_second_derivative_bound μ ν A U G V hA hU hG hV
    (lowerFamilyObservationShift_independent P n r m) (lowerFamilyGaussianShift_independent P r m)
    hU2 hV2 hF (lowerGaussianCurvatureConstant*dimensionLog r) ε hε hB hCDF' t
  rw [hFG,deriv_normalMaximumCDF] at hh
  have hUi : (∫ z, U z ∂μ) = ∫ z, familyObservationShift P z ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n r) (familyRestArrayLaw P n m) (familyObservationShift P)
  have hVi : (∫ z, V z ∂ν) = ∫ z, familyGaussianShift P z ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian r) (standardGaussian m) (familyGaussianShift P)
  have hU2i : (∫ z, U z^2 ∂μ) = ∫ z, familyObservationShift P z^2 ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n r) (familyRestArrayLaw P n m) (fun z => familyObservationShift P z^2)
  have hV2i : (∫ z, V z^2 ∂ν) = ∫ z, familyGaussianShift P z^2 ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian r) (standardGaussian m) (fun z => familyGaussianShift P z^2)
  rw [hUi,hVi,hU2i,hV2i] at hh
  exact hh

/-- The leading CDF error is discharged from the actual independent signs.
The assertion is uniform in both counts and all actual family parameters. -/
theorem eventually_lowerFamily_master_comparison :
    ∀ᶠ n : ℕ in atTop, ∀ (P : SymmetricFamilyParameters) (r m : ℕ) (hr : 1 ≤ r) (hm : 1 ≤ m),
      letI : NeZero r := ⟨by omega⟩
      letI : NeZero m := ⟨by omega⟩
      dimensionLog r ≤ Printed.rademacherGlobalSmallConstant*Real.sqrt n → ∀ t : ℝ,
      |lowerFamilyShiftedCDFDifference P n r m t-normalMaximumDensity r t*familyShiftMeanDifference P n m| ≤
        lowerRademacherMaximumConstant*Printed.rademacherGlobalError n r+
          (lowerGaussianCurvatureConstant*dimensionLog r/2)*familyShiftSecondMoments P n m := by
  filter_upwards [eventually_lowerRademacherMaximum_global_error] with n hn
  intro P r m hr hm
  letI : NeZero r := ⟨by omega⟩
  letI : NeZero m := ⟨by omega⟩
  intro hL t
  apply lowerFamily_master_comparison P hr
    (mul_nonneg lowerRademacherMaximumConstant_pos.le (by unfold Printed.rademacherGlobalError; positivity))
    (fun x => hn r hr hL x) t

end
end RectangleCLTArxivV1
