import RectangleCLT.RectangleConcentration
import RectangleCLTCompanion.SplitV4.IntrinsicCubeBoundary
import Mathlib.Probability.IdentDistrib

/-! Actual independent-copy and independent-sign laws used in the intrinsic
bounded-sum argument. Coordinate selection preserves the complete array law,
including for nonidentically distributed independent observations. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {n p : ℕ}

/-- Random coordinate selection, on an actual copy-pair times sign space. -/
def randomCubeSelectedArray (ξ : Fin n → Ω → Vector p)
    (z : (Ω × Ω) × Kane.Cube n) : Fin n → Vector p :=
  selectedArray ξ z.2 z.1

theorem measurable_randomCubeSelectedArray (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) : Measurable (randomCubeSelectedArray ξ) :=
  measurable_from_prod_countable fun x => measurable_selectedArray ξ hξ x

/-- Averaging a family of equal pushforward laws over an independent countable
parameter preserves that law. In particular, the parameter need not be uniform. -/
theorem measurePreserving_random_countable_selector
    {S E : Type*} [MeasurableSpace S] [Countable S] [MeasurableSingletonClass S]
    [MeasurableSpace E] (μ : Measure Ω) [SFinite μ]
    (ν : Measure S) [IsProbabilityMeasure ν] (τ : Measure E)
    (f : Ω × S → E) (hf : ∀ s, Measurable fun ω => f (ω, s))
    (hlaw : ∀ s, μ.map (fun ω => f (ω, s)) = τ) :
    MeasurePreserving f (μ.prod ν) τ := by
  have hmeas : Measurable f := measurable_from_prod_countable hf
  refine ⟨hmeas, ?_⟩
  ext A hA
  rw [Measure.map_apply hmeas hA, Measure.prod_apply_symm (hmeas hA)]
  have hsection (s : S) : μ ((fun ω => (ω, s)) ⁻¹' (f ⁻¹' A)) = τ A := by
    simpa only [Set.preimage_preimage] using
      (Measure.map_apply (hf s) hA).symm.trans (congrArg (fun ρ => ρ A) (hlaw s))
  simp_rw [hsection]
  simp

theorem fixedCubeSelectedArray_measurePreserving
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    MeasurePreserving (selectedArray ξ x) (μ.prod μ)
      (μ.map (fun ω i => ξ i ω)) :=
  ⟨measurable_selectedArray ξ hξ x, selectedArray_law_eq_original μ ξ hξ hind x⟩

theorem fixedCubeSelectedArray_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    IdentDistrib (selectedArray ξ x) (fun ω i => ξ i ω) (μ.prod μ) μ :=
  ⟨(measurable_selectedArray ξ hξ x).aemeasurable,
    (measurable_pi_lambda _ hξ).aemeasurable,
    selectedArray_law_eq_original μ ξ hξ hind x⟩

/-- The selected and unselected arrays retain their full independent-copy law. -/
theorem fixedCubeSelectedPair_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    IdentDistrib
      (fun ω => (selectedArray ξ x ω, selectedArray ξ (fun i => !(x i)) ω))
      (fun ω : Ω × Ω => ((fun i => ξ i ω.1), (fun i => ξ i ω.2)))
      (μ.prod μ) (μ.prod μ) := by
  have ha : Measurable (fun ω i => ξ i ω) := measurable_pi_lambda _ hξ
  refine ⟨((measurable_selectedArray ξ hξ x).prodMk
    (measurable_selectedArray ξ hξ (fun i => !(x i)))).aemeasurable,
    ((ha.comp measurable_fst).prodMk (ha.comp measurable_snd)).aemeasurable, ?_⟩
  rw [selectedPair_law_eq_original μ ξ hξ hind x]
  exact Measure.map_prod_map μ μ ha ha

theorem randomCubeSelectedArray_measurePreserving
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (ν : Measure (Kane.Cube n)) [IsProbabilityMeasure ν] :
    MeasurePreserving (randomCubeSelectedArray ξ) ((μ.prod μ).prod ν)
      (μ.map (fun ω i => ξ i ω)) :=
  measurePreserving_random_countable_selector (μ.prod μ) ν _ _
    (fun x => measurable_selectedArray ξ hξ x)
    (fun x => selectedArray_law_eq_original μ ξ hξ hind x)

theorem randomCubeSelectedArray_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (ν : Measure (Kane.Cube n)) [IsProbabilityMeasure ν] :
    IdentDistrib (randomCubeSelectedArray ξ) (fun ω i => ξ i ω)
      ((μ.prod μ).prod ν) μ :=
  ⟨(measurable_randomCubeSelectedArray ξ hξ).aemeasurable,
    (measurable_pi_lambda _ hξ).aemeasurable,
    (randomCubeSelectedArray_measurePreserving μ ξ hξ hind ν).map_eq⟩

theorem uniformCubeSelectedArray_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    IdentDistrib (randomCubeSelectedArray ξ) (fun ω i => ξ i ω)
      ((μ.prod μ).prod (cubeUniformLaw n)) μ :=
  randomCubeSelectedArray_identDistrib μ ξ hξ hind (cubeUniformLaw n)

/-- Midpoint and half-difference of a genuine original/copy observation. -/
def cubePairMidpoint (ξ : Fin n → Ω → Vector p) (ω : Ω × Ω) (i : Fin n) : Vector p :=
  (1 / 2 : ℝ) • (ξ i ω.1 + ξ i ω.2)

def cubePairDifference (ξ : Fin n → Ω → Vector p) (ω : Ω × Ω) (i : Fin n) : Vector p :=
  (1 / 2 : ℝ) • (ξ i ω.1 - ξ i ω.2)

omit [MeasurableSpace Ω] in
theorem selectedArray_eq_midpoint_add_signed_difference
    (ξ : Fin n → Ω → Vector p) (x : Kane.Cube n) (ω : Ω × Ω) (i : Fin n) :
    selectedArray ξ x ω i =
      cubePairMidpoint ξ ω i + cubeSign x i • cubePairDifference ξ ω i := by
  ext j
  cases hx : x i <;>
    simp [selectedArray, cubePairMidpoint, cubePairDifference, cubeSign, hx] <;> ring

omit [MeasurableSpace Ω] in
theorem selectedSum_eq_midpoint_add_signed_difference
    (ξ : Fin n → Ω → Vector p) (x : Kane.Cube n) (ω : Ω × Ω) :
    (∑ i, selectedArray ξ x ω i) =
      (∑ i, cubePairMidpoint ξ ω i) + ∑ i, cubeSign x i • cubePairDifference ξ ω i := by
  simp_rw [selectedArray_eq_midpoint_add_signed_difference]
  exact Finset.sum_add_distrib

theorem measurable_cubeArraySum : Measurable (fun a : Fin n → Vector p => ∑ i, a i) := by
  exact Finset.measurable_sum _ (fun i _ => measurable_pi_apply i)

theorem uniformCubeSelectedSum_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    IdentDistrib (fun z => ∑ i, randomCubeSelectedArray ξ z i)
      (fun ω => ∑ i, ξ i ω) ((μ.prod μ).prod (cubeUniformLaw n)) μ :=
  (uniformCubeSelectedArray_identDistrib μ ξ hξ hind).comp measurable_cubeArraySum

/-- Coordinate signs on the copy difference are implemented by swapping the
selected and unselected observations, so no symmetry assumption is needed. -/
theorem fixedCubeSignedDifference_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    IdentDistrib (fun ω : Ω × Ω => fun i => cubeSign x i • (ξ i ω.1 - ξ i ω.2))
      (fun ω : Ω × Ω => fun i => ξ i ω.1 - ξ i ω.2) (μ.prod μ) (μ.prod μ) := by
  have hm : Measurable (fun a : (Fin n → Vector p) × (Fin n → Vector p) =>
      fun i => a.1 i - a.2 i) :=
    measurable_pi_lambda _ (fun i =>
      ((measurable_pi_apply i).comp measurable_fst).sub
        ((measurable_pi_apply i).comp measurable_snd))
  have hid := (fixedCubeSelectedPair_identDistrib μ ξ hξ hind x).comp hm
  convert hid using 1
  funext ω i j
  cases hx : x i <;> simp [Function.comp_def, selectedArray, cubeSign, hx]

theorem randomCubeSignedDifference_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (ν : Measure (Kane.Cube n)) [IsProbabilityMeasure ν] :
    IdentDistrib
      (fun z : (Ω × Ω) × Kane.Cube n => fun i =>
        cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2))
      (fun ω : Ω × Ω => fun i => ξ i ω.1 - ξ i ω.2)
      ((μ.prod μ).prod ν) (μ.prod μ) := by
  have hslice (x : Kane.Cube n) :
      Measurable (fun ω : Ω × Ω => fun i => cubeSign x i • (ξ i ω.1 - ξ i ω.2)) :=
    measurable_pi_lambda _ (fun i => by
      simpa only [Pi.smul_apply] using
        (((hξ i).comp measurable_fst).sub ((hξ i).comp measurable_snd)).const_smul
          (cubeSign x i))
  have hp := measurePreserving_random_countable_selector (μ.prod μ) ν
    ((μ.prod μ).map (fun ω : Ω × Ω => fun i => ξ i ω.1 - ξ i ω.2))
    (fun z : (Ω × Ω) × Kane.Cube n => fun i =>
      cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2)) hslice
    (fun x => (fixedCubeSignedDifference_identDistrib μ ξ hξ hind x).map_eq)
  exact ⟨hp.measurable.aemeasurable,
    (measurable_pi_lambda _ (fun i =>
      ((hξ i).comp measurable_fst).sub ((hξ i).comp measurable_snd))).aemeasurable,
    hp.map_eq⟩

/-- Product extension preserves identical distribution when the new variable
is independent of the original probability space. -/
theorem identDistrib_prod_independent
    {E : Type*} [MeasurableSpace E] {f : Ω → E} {g : Γ → E}
    {μ : Measure Ω} {ν : Measure Γ} [SFinite μ] [SFinite ν]
    (h : IdentDistrib f g μ ν) (hf : Measurable f) (hg : Measurable g)
    {T : Type*} [MeasurableSpace T] (τ : Measure T) [SFinite τ] :
    IdentDistrib (fun z : Ω × T => (f z.1, z.2))
      (fun z : Γ × T => (g z.1, z.2)) (μ.prod τ) (ν.prod τ) := by
  refine ⟨((hf.comp measurable_fst).prodMk measurable_snd).aemeasurable,
    ((hg.comp measurable_fst).prodMk measurable_snd).aemeasurable, ?_⟩
  calc
    _ = (μ.map f).prod (τ.map id) := (Measure.map_prod_map μ τ hf measurable_id).symm
    _ = (ν.map g).prod (τ.map id) := by rw [h.map_eq]
    _ = _ := Measure.map_prod_map ν τ hg measurable_id

theorem uniformCubeSelectedSum_with_independent_shift_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (ν : Measure Γ) [SFinite ν] (R : Γ → Vector p) (hR : Measurable R) :
    IdentDistrib
      (fun z : ((Ω × Ω) × Kane.Cube n) × Γ =>
        (∑ i, randomCubeSelectedArray ξ z.1 i) + R z.2)
      (fun z : Ω × Γ => (∑ i, ξ i z.1) + R z.2)
      (((μ.prod μ).prod (cubeUniformLaw n)).prod ν) (μ.prod ν) := by
  have hm := measurable_cubeArraySum.comp (measurable_randomCubeSelectedArray ξ hξ)
  have ho : Measurable (fun ω => ∑ i, ξ i ω) := Finset.measurable_sum _ (fun i _ => hξ i)
  exact (identDistrib_prod_independent
    (uniformCubeSelectedSum_identDistrib μ ξ hξ hind) hm ho ν).comp
    (measurable_fst.add (hR.comp measurable_snd))

/-- Genuine test integration under the independent signs and copy pair. The
integrability conclusion is transported from the actual original sum. -/
theorem uniformCubeSelectedSum_test_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : Vector p → E) (hF : Measurable F)
    (hFi : Integrable (fun ω => F (∑ i, ξ i ω)) μ) :
    Integrable (fun z => F (∑ i, randomCubeSelectedArray ξ z i))
      ((μ.prod μ).prod (cubeUniformLaw n)) ∧
      (∫ z, F (∑ i, randomCubeSelectedArray ξ z i)
        ∂((μ.prod μ).prod (cubeUniformLaw n))) = ∫ ω, F (∑ i, ξ i ω) ∂μ := by
  have hid := (uniformCubeSelectedSum_identDistrib μ ξ hξ hind).comp hF
  exact ⟨hid.integrable_iff.mpr hFi, hid.integral_eq⟩

theorem uniformCubeSignedDifference_test_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : (Fin n → Vector p) → E) (hF : Measurable F)
    (hFi : Integrable (fun ω : Ω × Ω => F (fun i => ξ i ω.1 - ξ i ω.2)) (μ.prod μ)) :
    Integrable (fun z : (Ω × Ω) × Kane.Cube n =>
      F (fun i => cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2)))
      ((μ.prod μ).prod (cubeUniformLaw n)) ∧
      (∫ z, F (fun i => cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2))
        ∂((μ.prod μ).prod (cubeUniformLaw n))) =
      ∫ ω : Ω × Ω, F (fun i => ξ i ω.1 - ξ i ω.2) ∂(μ.prod μ) := by
  have hid := (randomCubeSignedDifference_identDistrib μ ξ hξ hind (cubeUniformLaw n)).comp hF
  exact ⟨hid.integrable_iff.mpr hFi, hid.integral_eq⟩

/-- The same law transport with signs integrated first, as used in conditional
Rademacher symmetrization. Fubini applies to the actual integrable test. -/
theorem uniformCubeSignedDifference_iterated_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (F : (Fin n → Vector p) → E) (hF : Measurable F)
    (hFi : Integrable (fun ω : Ω × Ω => F (fun i => ξ i ω.1 - ξ i ω.2)) (μ.prod μ)) :
    (∫ x, ∫ ω : Ω × Ω, F (fun i => cubeSign x i • (ξ i ω.1 - ξ i ω.2))
      ∂(μ.prod μ) ∂(cubeUniformLaw n)) =
      ∫ ω : Ω × Ω, F (fun i => ξ i ω.1 - ξ i ω.2) ∂(μ.prod μ) := by
  obtain ⟨hi, heq⟩ := uniformCubeSignedDifference_test_transport μ ξ hξ hind F hF hFi
  exact (integral_prod_symm _ hi).symm.trans heq

theorem uniformCubeMidpointSignedSum_identDistrib
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    IdentDistrib
      (fun z : (Ω × Ω) × Kane.Cube n =>
        (∑ i, cubePairMidpoint ξ z.1 i) + ∑ i, cubeSign z.2 i • cubePairDifference ξ z.1 i)
      (fun ω => ∑ i, ξ i ω) ((μ.prod μ).prod (cubeUniformLaw n)) μ := by
  convert uniformCubeSelectedSum_identDistrib μ ξ hξ hind using 1
  funext z
  exact (selectedSum_eq_midpoint_add_signed_difference ξ z.2 z.1).symm

theorem uniformCubeSelectedSum_with_independent_shift_test_transport
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (ν : Measure Γ) [SFinite ν] (R : Γ → Vector p) (hR : Measurable R)
    (F : Vector p → E) (hF : Measurable F)
    (hFi : Integrable (fun z : Ω × Γ => F ((∑ i, ξ i z.1) + R z.2)) (μ.prod ν)) :
    Integrable (fun z : ((Ω × Ω) × Kane.Cube n) × Γ =>
      F ((∑ i, randomCubeSelectedArray ξ z.1 i) + R z.2))
      (((μ.prod μ).prod (cubeUniformLaw n)).prod ν) ∧
      (∫ z, F ((∑ i, randomCubeSelectedArray ξ z.1 i) + R z.2)
        ∂(((μ.prod μ).prod (cubeUniformLaw n)).prod ν)) =
      ∫ z : Ω × Γ, F ((∑ i, ξ i z.1) + R z.2) ∂(μ.prod ν) := by
  have hid := (uniformCubeSelectedSum_with_independent_shift_identDistrib
    μ ξ hξ hind ν R hR).comp hF
  exact ⟨hid.integrable_iff.mpr hFi, hid.integral_eq⟩

end
end RectangleCLT.Companion.SplitV4
