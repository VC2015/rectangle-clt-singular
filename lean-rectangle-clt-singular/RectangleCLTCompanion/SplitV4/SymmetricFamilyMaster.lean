import RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts
import RectangleCLTCompanion.SplitV4.RademacherLocalComparison
import RectangleCLTCompanion.SplitV4.LocalShiftComparison

/-! Actual signed-shift master comparison for the common symmetric construction. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyShiftedCDFDifference (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] (t : ℝ) : ℝ :=
  (familySeparatedLaw P n m).real {z | familyRademacherMaximum z.1 + familyObservationShift P z.2 ≤ t} -
    (familyGaussianPairLaw m).real {z | finiteMaximum z.1 + familyGaussianShift P z.2 ≤ t}

def familyShiftMeanDifference (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] : ℝ :=
  (∫ z, familyGaussianShift P z ∂standardGaussian m) - (∫ z, familyObservationShift P z ∂familyRestArrayLaw P n m)

def familyShiftSecondMoments (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] : ℝ :=
  (∫ z, familyObservationShift P z ^ 2 ∂familyRestArrayLaw P n m) +
    (∫ z, familyGaussianShift P z ^ 2 ∂standardGaussian m)

theorem integral_product_snd_probability {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν] (f : Γ → ℝ) :
    (∫ z : Ω × Γ, f z.2 ∂μ.prod ν) = ∫ z, f z ∂ν := by
  simpa only [measureReal_univ_eq_one, one_smul] using MeasureTheory.integral_fun_snd (μ := μ) (ν := ν) f

theorem familyLocal_master_comparison (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (hn : 1 ≤ n) (hL : 1 ≤ Real.log (m : ℝ))
    (hmass : ∀ x : ℝ, |x-normalMaxThreshold m| ≤ 1/Real.sqrt (Real.log (m : ℝ)) →
      0 ≤ x ∧ |x| ≤ 3*Real.sqrt (Real.log (m : ℝ)) ∧ (m : ℝ)*standardNormalUpperTail x ≤ 8*Real.exp 3)
    (hsmall : moderateTailSmallConstant * ((1/Real.sqrt n)*(1+3*Real.sqrt (Real.log (m : ℝ)))) ≤ 1)
    (herror : rademacherLocalError n m ≤ 1) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : ℝ, |x-normalMaxThreshold m| ≤ 1/Real.sqrt (Real.log (m : ℝ)) →
      |deriv (normalMaximumDensity m) x| ≤ B) :
    |familyShiftedCDFDifference P n m (normalMaxThreshold m) - normalMaximumDensity m (normalMaxThreshold m) *
      familyShiftMeanDifference P n m| ≤ 8*Real.exp 4*rademacherLocalError n m +
        localShiftComparisonCost B (1/Real.sqrt (Real.log (m : ℝ))) (normalMaximumDensity m (normalMaxThreshold m)) *
          familyShiftSecondMoments P n m := by
  let μ := familySeparatedLaw P n m
  let ν := familyGaussianPairLaw m
  let A : FamilySeparatedSeed n m → ℝ := fun z => familyRademacherMaximum z.1
  let U : FamilySeparatedSeed n m → ℝ := fun z => familyObservationShift P z.2
  let G : Vector m × Vector m → ℝ := fun z => finiteMaximum z.1
  let V : Vector m × Vector m → ℝ := fun z => familyGaussianShift P z.2
  have hmax : Measurable (finiteMaximum : Vector m → ℝ) :=
    measurable_finiteMaximum (fun j (z : Vector m) => z j) (fun j => measurable_pi_apply j)
  have hA : Measurable A := measurable_of_finite _
  have hU : Measurable U := measurable_of_finite _
  have hG : Measurable G := hmax.comp measurable_fst
  have hV : Measurable V := measurable_const.mul (hmax.comp measurable_snd)
  have hU2 : Integrable (fun z => U z ^ 2) μ := integrable_family_finite _ _
  have hsnd : MeasurePreserving Prod.snd ν (standardGaussian m) := by
    refine ⟨measurable_snd, ?_⟩
    simp only [ν, familyGaussianPairLaw, Measure.map_snd_prod, measure_univ, one_smul]
  have hV2 : Integrable (fun z => V z ^ 2) ν := by
    exact (hsnd.integrable_comp (familyGaussianShift_sq_integrable P m).aestronglyMeasurable).mpr
      (familyGaussianShift_sq_integrable P m)
  have hFG : realCDF ν G = normalMaximumCDF m := funext (familyGaussian_realCDF m)
  have hF : ContDiff ℝ 2 (realCDF ν G) := by rw [hFG]; exact contDiff_normalMaximumCDF_two m
  have hε : 0 ≤ 8*Real.exp 4*rademacherLocalError n m := by
    unfold rademacherLocalError
    have hC := moderateTailRemainderConstant_bounds.1
    positivity
  have hr : 0 < 1/Real.sqrt (Real.log (m : ℝ)) := by positivity
  have hB' (x : ℝ) (hx : |x-normalMaxThreshold m| ≤ 1/Real.sqrt (Real.log (m : ℝ))) :
      |deriv (deriv (realCDF ν G)) x| ≤ B := by rw [hFG, deriv_normalMaximumCDF]; exact hB x hx
  have hCDF (x : ℝ) (hx : |x-normalMaxThreshold m| ≤ 1/Real.sqrt (Real.log (m : ℝ))) :
      |realCDF μ A x - realCDF ν G x| ≤ 8*Real.exp 4*rademacherLocalError n m := by
    rw [familyRademacher_realCDF, familyGaussian_realCDF]
    exact familyRademacherMaximum_local_error hn hL hmass hsmall herror hx
  have hh := independent_local_shift_comparison μ ν A U G V hA hU hG hV
    (familyObservationShift_independent P n m) (familyGaussianShift_independent P m) hU2 hV2 hF hB0 hε hr hB' hCDF
  rw [hFG, deriv_normalMaximumCDF] at hh
  have hUi : (∫ z, U z ∂μ) = ∫ z, familyObservationShift P z ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n m) (familyRestArrayLaw P n m) (familyObservationShift P)
  have hVi : (∫ z, V z ∂ν) = ∫ z, familyGaussianShift P z ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian m) (standardGaussian m) (familyGaussianShift P)
  have hU2i : (∫ z, U z ^ 2 ∂μ) = ∫ z, familyObservationShift P z ^ 2 ∂familyRestArrayLaw P n m :=
    integral_product_snd_probability (familySignArrayLaw n m) (familyRestArrayLaw P n m) (fun z => familyObservationShift P z ^ 2)
  have hV2i : (∫ z, V z ^ 2 ∂ν) = ∫ z, familyGaussianShift P z ^ 2 ∂standardGaussian m :=
    integral_product_snd_probability (standardGaussian m) (standardGaussian m) (fun z => familyGaussianShift P z ^ 2)
  rw [hUi, hVi, hU2i, hV2i] at hh
  exact hh

end
end RectangleCLT.Companion.SplitV4
