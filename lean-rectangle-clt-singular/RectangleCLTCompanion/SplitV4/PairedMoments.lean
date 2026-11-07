import RectangleCLTCompanion.SplitV4.FourthMaximum
import RectangleCLTCompanion.SplitV4.PairedSlepian
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Dynamics.Ergodic.MeasurePreserving

/-! Genuine moment and independence inputs for the paired increments.
The two original arrays are independent copies; distributions may differ
between summands. No symmetry of an original observation is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def pairedIncrement {Ω : Type*} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (z : Ω × Ω) : Vector p := ξ i z.2 - ξ i z.1

def pairedTruncatedArray {Ω : Type*} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (h : ℝ) (i : Fin n) (z : Ω × Ω) : Vector p :=
  pairedTruncatedIncrement (ξ i z.1) (ξ i z.2) h

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]

theorem pairedArray_measurePreserving (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    MeasurePreserving (fun z : Ω × Ω => fun i => (ξ i z.1, ξ i z.2))
      (μ.prod μ) (Measure.pi fun i => (μ.map (ξ i)).prod (μ.map (ξ i))) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (ξ i)
  haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hξ i).aemeasurable
  have hs : MeasurePreserving (fun ω i => ξ i ω) μ (Measure.pi ν) :=
    ⟨measurable_pi_lambda _ hξ,
      (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)).mp hind⟩
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Vector p) (Vector p) (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow (Vector p) (Vector p) (Fin n) ν ν
  exact (MeasurePreserving.symm e he).comp (hs.prod hs)

theorem iIndepFun_pairedArray (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    iIndepFun (fun i (z : Ω × Ω) => (ξ i z.1, ξ i z.2)) (μ.prod μ) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => ((hξ i |>.comp measurable_fst).prodMk (hξ i |>.comp measurable_snd)).aemeasurable)).mpr
  simp only [Function.comp_def]
  rw [(pairedArray_measurePreserving μ ξ hξ hind).map_eq]
  congr 1
  funext i
  exact Measure.map_prod_map μ μ (hξ i) (hξ i)

theorem iIndepFun_pairedIncrement (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    iIndepFun (pairedIncrement ξ) (μ.prod μ) :=
  (iIndepFun_pairedArray μ ξ hξ hind).comp (fun _ z => z.2 - z.1)
    (fun _ => measurable_snd.sub measurable_fst)

theorem iIndepFun_pairedTruncatedArray (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (h : ℝ) :
    iIndepFun (pairedTruncatedArray ξ h) (μ.prod μ) := by
  exact (iIndepFun_pairedArray μ ξ hξ hind).comp
    (fun _ z => pairedTruncatedIncrement z.1 z.2 h)
    (fun _ => Measurable.ite
      (measurableSet_le (measurable_snd.sub measurable_fst).norm measurable_const)
      (measurable_snd.sub measurable_fst) measurable_const)

theorem fourth_sub_le (x y : ℝ) : (y - x)^4 ≤ 8 * (x^4 + y^4) := by
  have hs : (y-x)^2 ≤ 2*(x^2+y^2) := by nlinarith [sq_nonneg (x+y)]
  calc
    _ = ((y-x)^2)^2 := by ring
    _ ≤ (2*(x^2+y^2))^2 := pow_le_pow_left₀ (sq_nonneg _) hs 2
    _ ≤ _ := by nlinarith [sq_nonneg (x^2-y^2)]

theorem integrable_pairedIncrement_fourth (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) (j : Fin p)
    (hfourth : Integrable (fun ω => ξ i ω j ^ 4) μ) :
    Integrable (fun z : Ω × Ω => pairedIncrement ξ i z j ^ 4) (μ.prod μ) := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hsnd : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  have hfi : Integrable (fun z : Ω × Ω => ξ i z.1 j ^ 4) (μ.prod μ) :=
    (hfst.integrable_comp hfourth.aestronglyMeasurable).mpr hfourth
  have hsi : Integrable (fun z : Ω × Ω => ξ i z.2 j ^ 4) (μ.prod μ) :=
    (hsnd.integrable_comp hfourth.aestronglyMeasurable).mpr hfourth
  apply ((hfi.add hsi).const_mul 8).mono'
    ((((measurable_pi_apply j).comp ((hξ i |>.comp measurable_snd).sub
      (hξ i |>.comp measurable_fst))).pow_const 4).aestronglyMeasurable)
  apply ae_of_all
  intro z
  change ‖pairedIncrement ξ i z j ^ 4‖ ≤ 8 * ((ξ i z.1 j)^4 + (ξ i z.2 j)^4)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ pairedIncrement ξ i z j ^ 4)]
  exact fourth_sub_le _ _

theorem integral_pairedIncrement_fourth_le (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) (j : Fin p)
    (hfourth : Integrable (fun ω => ξ i ω j ^ 4) μ) :
    (∫ z : Ω × Ω, pairedIncrement ξ i z j ^ 4 ∂μ.prod μ) ≤
      16 * ∫ ω, ξ i ω j ^ 4 ∂μ := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_fst, by simp⟩
  have hsnd : MeasurePreserving (Prod.snd : Ω × Ω → Ω) (μ.prod μ) μ :=
    ⟨measurable_snd, by simp⟩
  have hfi : Integrable (fun z : Ω × Ω => ξ i z.1 j ^ 4) (μ.prod μ) :=
    (hfst.integrable_comp hfourth.aestronglyMeasurable).mpr hfourth
  have hsi : Integrable (fun z : Ω × Ω => ξ i z.2 j ^ 4) (μ.prod μ) :=
    (hsnd.integrable_comp hfourth.aestronglyMeasurable).mpr hfourth
  have h := integral_mono (integrable_pairedIncrement_fourth μ ξ hξ i j hfourth)
    ((hfi.add hsi).const_mul 8) (fun z => fourth_sub_le (ξ i z.1 j) (ξ i z.2 j))
  have heq : (∫ z : Ω × Ω, 8 * ((ξ i z.1 j)^4 + (ξ i z.2 j)^4) ∂μ.prod μ) =
      16 * ∫ ω, ξ i ω j ^ 4 ∂μ := by
    have heF : (∫ z : Ω × Ω, ξ i z.1 j ^ 4 ∂μ.prod μ) = ∫ ω, ξ i ω j ^ 4 ∂μ := by
      simpa using (integral_fun_fst (μ := μ) (ν := μ) (fun ω => ξ i ω j ^ 4))
    have heS : (∫ z : Ω × Ω, ξ i z.2 j ^ 4 ∂μ.prod μ) = ∫ ω, ξ i ω j ^ 4 ∂μ := by
      simpa using (integral_fun_snd (μ := μ) (ν := μ) (fun ω => ξ i ω j ^ 4))
    rw [integral_const_mul, integral_add hfi hsi, heF, heS]
    ring
  exact h.trans_eq heq

theorem measurable_pairedTruncatedArray (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (h : ℝ) (i : Fin n) :
    Measurable (pairedTruncatedArray ξ h i) :=
  C4Test.measurable_pairedTruncatedIncrement (ξ i) (hξ i) h

theorem pairedTruncatedArray_fourth_le (ξ : Fin n → Ω → Vector p)
    (h : ℝ) (i : Fin n) (z : Ω × Ω) (j : Fin p) :
    pairedTruncatedArray ξ h i z j ^ 4 ≤ pairedIncrement ξ i z j ^ 4 := by
  by_cases he : ‖ξ i z.2 - ξ i z.1‖ ≤ h
  · simp [pairedTruncatedArray, pairedTruncatedIncrement, pairedIncrement, he]
  · simp only [pairedTruncatedArray, pairedTruncatedIncrement, if_neg he,
      Pi.zero_apply, zero_pow (by decide : 4 ≠ 0)]
    positivity

theorem integrable_pairedTruncatedArray_fourth (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (h : ℝ) (i : Fin n) (j : Fin p)
    (hfourth : Integrable (fun ω => ξ i ω j ^ 4) μ) :
    Integrable (fun z : Ω × Ω => pairedTruncatedArray ξ h i z j ^ 4) (μ.prod μ) := by
  apply (integrable_pairedIncrement_fourth μ ξ hξ i j hfourth).mono'
    (((measurable_pi_apply j).comp
      (measurable_pairedTruncatedArray ξ hξ h i)).pow_const 4).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    change ‖pairedTruncatedArray ξ h i z j ^ 4‖ ≤ pairedIncrement ξ i z j ^ 4
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ pairedTruncatedArray ξ h i z j ^ 4)]
    exact pairedTruncatedArray_fourth_le ξ h i z j

theorem integral_pairedTruncatedArray_fourth_le (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (h : ℝ) (i : Fin n) (j : Fin p)
    (hfourth : Integrable (fun ω => ξ i ω j ^ 4) μ) :
    (∫ z : Ω × Ω, pairedTruncatedArray ξ h i z j ^ 4 ∂μ.prod μ) ≤
      16 * ∫ ω, ξ i ω j ^ 4 ∂μ := by
  apply (integral_mono (integrable_pairedTruncatedArray_fourth μ ξ hξ h i j hfourth)
    (integrable_pairedIncrement_fourth μ ξ hξ i j hfourth)
    (fun z => pairedTruncatedArray_fourth_le ξ h i z j)).trans
  exact integral_pairedIncrement_fourth_le μ ξ hξ i j hfourth

theorem pairedTruncatedArray_fourth_budget_from_original (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (h : ℝ)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    {D : ℝ} (hD : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) (j : Fin p) :
    (∑ i, ∫ z : Ω × Ω, pairedTruncatedArray ξ h i z j ^ 4 ∂μ.prod μ) ≤ 16 * D := by
  calc
    _ ≤ ∑ i, 16 * ∫ ω, ξ i ω j ^ 4 ∂μ := Finset.sum_le_sum fun i _ =>
      integral_pairedTruncatedArray_fourth_le μ ξ hξ h i j (hfourth i j)
    _ = 16 * ∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ := (Finset.mul_sum _ _ _).symm
    _ ≤ _ := mul_le_mul_of_nonneg_left (hD j) (by norm_num)

theorem expected_pairedFourthBudget_le (hp : 1 ≤ p)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {h D : ℝ} (hh : 0 < h) (hD0 : 0 ≤ D)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hD : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ D) :
    (∫ z : Ω × Ω, coordinateFourthBudget (fun i => pairedTruncatedArray ξ h i z) ∂μ.prod μ) ≤
      h^4 * Real.log (2 * (p : ℝ)) + (Real.exp 1 - 1) * (16 * D) := by
  exact expected_coordinateFourthBudget_le hp (pairedTruncatedArray ξ h)
    (measurable_pairedTruncatedArray ξ hξ h)
    (iIndepFun_pairedTruncatedArray μ ξ hξ hind h) hh (mul_nonneg (by norm_num) hD0)
    (fun i => ae_of_all _ fun z => C4Test.norm_pairedTruncatedIncrement_le _ _ hh.le)
    (pairedTruncatedArray_fourth_budget_from_original μ ξ hξ h hfourth hD)

theorem integrable_pairedFourthBudget (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {h : ℝ} (hh : 0 ≤ h) :
    Integrable (fun z : Ω × Ω => coordinateFourthBudget
      (fun i => pairedTruncatedArray ξ h i z)) (μ.prod μ) := by
  have hm : Measurable (fun z : Ω × Ω => coordinateFourthBudget
      (fun i => pairedTruncatedArray ξ h i z)) := by
    unfold coordinateFourthBudget
    apply Measurable.norm
    apply measurable_pi_lambda; intro j
    exact Finset.measurable_sum _ fun i _ =>
      (((measurable_pi_apply j).comp (measurable_pairedTruncatedArray ξ hξ h i)).pow_const 4)
  apply (integrable_const ((n : ℝ) * h^4)).mono' hm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateFourthBudget_nonneg _)]
  unfold coordinateFourthBudget
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  have hnonneg : 0 ≤ ∑ i, pairedTruncatedArray ξ h i z j ^ 4 :=
    Finset.sum_nonneg fun i _ => by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hnonneg]
  calc
    _ ≤ ∑ _i : Fin n, h^4 := Finset.sum_le_sum fun i _ => by
      have hnorm := C4Test.norm_pairedTruncatedIncrement_le (ξ i z.1) (ξ i z.2) hh
      have hj : |pairedTruncatedArray ξ h i z j| ≤ h := (norm_le_pi_norm _ j).trans hnorm
      calc
        _ = |pairedTruncatedArray ξ h i z j|^4 := by
          rw [pow_abs]
          exact (abs_of_nonneg (by positivity : 0 ≤ pairedTruncatedArray ξ h i z j ^ 4)).symm
        _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hj 4
    _ = _ := by simp

end
end RectangleCLT.Companion.SplitV4
