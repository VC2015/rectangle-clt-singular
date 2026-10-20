import RectangleCLT.RandomResampling
import RectangleCLT.IndependentFourthMoment
import Mathlib.Probability.Independence.Basic

/-! The resampling coupling used in rectangle concentration. In particular,
independence of the original observations identifies both coupling marginals
with the law of their actual sum. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

/-- Select coordinate observations from two independent whole-array copies. -/
def selectedArray {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (x : Kane.Cube n) (ω : Ω × Ω) : Fin n → Vector p :=
  fun i => if x i then ξ i ω.1 else ξ i ω.2

theorem measurable_selectedArray {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (x : Kane.Cube n) :
    Measurable (selectedArray ξ x) := by
  apply measurable_pi_lambda
  intro i
  cases hx : x i
  · simpa only [selectedArray, hx, Bool.false_eq_true, ↓reduceIte] using
      (hξ i).comp measurable_snd
  · simpa only [selectedArray, hx, ↓reduceIte] using (hξ i).comp measurable_fst

/-- A fixed coordinatewise choice between two independent copies preserves
the full array law when the original observations are independent. -/
theorem selectedArray_law_eq_original {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    (μ.prod μ).map (selectedArray ξ x) = μ.map (fun ω i => ξ i ω) := by
  classical
  have horiginal := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)).mp hind
  rw [horiginal]
  letI (i : Fin n) : IsProbabilityMeasure (μ.map (ξ i)) :=
    isProbabilityMeasure_map (hξ i).aemeasurable
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply (measurable_selectedArray ξ hξ x) (MeasurableSet.univ_pi hs)]
  let lsets : Fin n → Set (Vector p) := fun i => if x i then s i else Set.univ
  let rsets : Fin n → Set (Vector p) := fun i => if x i then Set.univ else s i
  have hlmeas : ∀ i, MeasurableSet (lsets i) := by
    intro i
    cases hi : x i <;> simp [lsets, hi, hs i]
  have hrmeas : ∀ i, MeasurableSet (rsets i) := by
    intro i
    cases hi : x i <;> simp [rsets, hi, hs i]
  have hpre : selectedArray ξ x ⁻¹' Set.univ.pi s =
      (⋂ i : Fin n, ξ i ⁻¹' lsets i) ×ˢ (⋂ i : Fin n, ξ i ⁻¹' rsets i) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_prod, Set.mem_iInter]
    constructor
    · intro h
      constructor
      · intro i
        cases hi : x i
        · simp [lsets, hi]
        · simpa [lsets, selectedArray, hi] using h i
      · intro i
        cases hi : x i
        · simpa [rsets, selectedArray, hi] using h i
        · simp [rsets, hi]
    · rintro ⟨hl, hr⟩ i
      cases hi : x i
      · simpa [rsets, selectedArray, hi] using hr i
      · simpa [lsets, selectedArray, hi] using hl i
  rw [hpre, Measure.prod_prod]
  have hl := hind.measure_inter_preimage_eq_mul Finset.univ (sets := lsets) (fun i _ => hlmeas i)
  have hr := hind.measure_inter_preimage_eq_mul Finset.univ (sets := rsets) (fun i _ => hrmeas i)
  simp only [Finset.mem_univ, Set.iInter_true] at hl hr
  rw [hl, hr, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  rw [Measure.map_apply (hξ i) (hs i)]
  cases hi : x i <;> simp [lsets, rsets, hi]

/-- Swap each coordinate of a pair of arrays according to a fixed selector. -/
def swapArrays {p n : ℕ} (x : Kane.Cube n)
    (a : (Fin n → Vector p) × (Fin n → Vector p)) :
    (Fin n → Vector p) × (Fin n → Vector p) :=
  (fun i => if x i then a.1 i else a.2 i,
   fun i => if x i then a.2 i else a.1 i)

/-- Coordinate swaps preserve two independent copies of a product law. -/
theorem measurePreserving_swapArrays {p n : ℕ}
    (ν : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (ν i)]
    (x : Kane.Cube n) :
    MeasurePreserving (swapArrays x) ((Measure.pi ν).prod (Measure.pi ν))
      ((Measure.pi ν).prod (Measure.pi ν)) := by
  let e := MeasurableEquiv.arrowProdEquivProdArrow (Vector p) (Vector p) (Fin n)
  have he := measurePreserving_arrowProdEquivProdArrow (Vector p) (Vector p) (Fin n) ν ν
  let f : Fin n → (Vector p × Vector p) → (Vector p × Vector p) :=
    fun i z => if x i then z else z.swap
  have hf : ∀ i, MeasurePreserving (f i) ((ν i).prod (ν i)) ((ν i).prod (ν i)) := by
    intro i
    cases hi : x i
    · simpa only [f, hi, Bool.false_eq_true, ↓reduceIte] using
        (Measure.measurePreserving_swap (μ := ν i) (ν := ν i))
    · simpa only [f, hi, ↓reduceIte] using (MeasurePreserving.id ((ν i).prod (ν i)))
  have hp := measurePreserving_pi (fun i => (ν i).prod (ν i))
    (fun i => (ν i).prod (ν i)) hf
  have hh := he.comp (hp.comp (MeasurePreserving.symm e he))
  convert hh using 1
  ext a : 1
  apply Prod.ext <;> funext i <;> cases hi : x i <;> simp [swapArrays, Function.comp_def, e, f, hi,
    MeasurableEquiv.arrowProdEquivProdArrow, Equiv.arrowProdEquivProdArrow]

/-- Selecting one observation and leaving its independent partner unselected
preserves their joint array law. This is stronger than either marginal identity. -/
theorem selectedPair_law_eq_original {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    (μ.prod μ).map (fun ω =>
      (selectedArray ξ x ω, selectedArray ξ (fun i => !(x i)) ω)) =
      (μ.map (fun ω i => ξ i ω)).prod (μ.map (fun ω i => ξ i ω)) := by
  let ν : Fin n → Measure (Vector p) := fun i => μ.map (ξ i)
  letI (i : Fin n) : IsProbabilityMeasure (ν i) :=
    isProbabilityMeasure_map (hξ i).aemeasurable
  have hlaw := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hξ i).aemeasurable)).mp hind
  have ha : MeasurePreserving (fun ω i => ξ i ω) μ (Measure.pi ν) :=
    ⟨measurable_pi_lambda _ hξ, hlaw⟩
  have hh := ((measurePreserving_swapArrays ν x).comp (ha.prod ha)).map_eq
  rw [hlaw]
  convert hh using 1
  congr 1
  funext ω
  dsimp [Function.comp_def, Prod.map, swapArrays, selectedArray]
  congr 1
  funext i
  cases hi : x i <;> simp [selectedArray, hi]

private theorem measurable_arraySum {p n : ℕ} :
    Measurable (fun a : Fin n → Vector p => ∑ i, a i) := by
  apply measurable_pi_lambda
  intro j
  simpa only [Finset.sum_apply] using
    (Finset.measurable_sum Finset.univ (fun i _ =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)))

/-- The selected sum has the original sum law for each fixed selector. -/
theorem selectedSum_law_eq_original {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (x : Kane.Cube n) :
    (μ.prod μ).map (fun ω => resampledSum (fun i => ξ i ω.1) (fun i => ξ i ω.2) x) =
      μ.map (sumVector ξ) := by
  have hh := congrArg (fun ν : Measure (Fin n → Vector p) =>
    ν.map (fun a => ∑ i, a i)) (selectedArray_law_eq_original μ ξ hξ hind x)
  dsimp only at hh
  rw [Measure.map_map measurable_arraySum (measurable_selectedArray ξ hξ x),
    Measure.map_map measurable_arraySum (measurable_pi_lambda _ hξ)] at hh
  convert hh using 1
  · congr 1
    funext ω j
    simp [Function.comp_apply, resampledSum, selectedArray, Finset.sum_apply, ite_apply]

private theorem uniformSelectorWeights_sum (n : ℕ) :
    (∑ _x : Kane.Cube n, ENNReal.ofReal ((Fintype.card (Kane.Cube n) : ℝ)⁻¹)) = 1 := by
  have hc : (Fintype.card (Kane.Cube n) : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_ne_zero (α := Kane.Cube n))
  rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => inv_nonneg.mpr (Nat.cast_nonneg _))]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [mul_inv_cancel₀ hc]
  norm_num

theorem independentCopy_uniformResampledSumLaw_eq_original
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    uniformResampledSumLaw (μ.prod μ) (fun ω i => ξ i ω.1) (fun ω i => ξ i ω.2) =
      μ.map (sumVector ξ) := by
  unfold uniformResampledSumLaw
  simp_rw [selectedSum_law_eq_original μ ξ hξ hind]
  rw [← Finset.sum_smul, uniformSelectorWeights_sum, one_smul]

/-- Ordinary coordinate resampling replaces every marked original observation
by the corresponding observation in an independent copy. -/
def freshResamplingPair {Ω : Type u} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (mask : Kane.Cube n) (ω : Ω × Ω) :
    Vector p × Vector p :=
  (sumVector ξ ω.1,
   resampledSum (fun i => ξ i ω.2) (fun i => ξ i ω.1) mask)

theorem measurable_freshResamplingPair {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (mask : Kane.Cube n) :
    Measurable (freshResamplingPair ξ mask) := by
  exact ((Finset.measurable_sum Finset.univ (fun i _ => hξ i)).comp measurable_fst).prodMk
    (measurable_random_resampledSum (fun ω : Ω × Ω => fun i => ξ i ω.2) (fun ω : Ω × Ω => fun i => ξ i ω.1)
      (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd))
      (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst)) mask)

/-- For each fixed mask and selector, the Kane coupling is exactly the ordinary
independent-copy resampling coupling, as a joint probability law. -/
theorem resamplingPair_law_eq_fresh {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (x mask : Kane.Cube n) :
    (μ.prod μ).map (resamplingPair (fun ω i => ξ i ω.1) (fun ω i => ξ i ω.2) x mask) =
      (μ.prod μ).map (freshResamplingPair ξ mask) := by
  let g : ((Fin n → Vector p) × (Fin n → Vector p)) → Vector p × Vector p :=
    fun a => (∑ i, a.1 i, resampledSum a.2 a.1 mask)
  have hg : Measurable g :=
    (measurable_arraySum.comp measurable_fst).prodMk
      (measurable_random_resampledSum Prod.snd Prod.fst measurable_snd measurable_fst mask)
  have hh := congrArg (fun ν : Measure ((Fin n → Vector p) × (Fin n → Vector p)) =>
    ν.map g) (selectedPair_law_eq_original μ ξ hξ hind x)
  dsimp only at hh
  rw [Measure.map_prod_map μ μ (measurable_pi_lambda _ hξ) (measurable_pi_lambda _ hξ),
    Measure.map_map hg ((measurable_selectedArray ξ hξ x).prodMk
      (measurable_selectedArray ξ hξ (fun i => !(x i)))),
    Measure.map_map hg ((measurable_pi_lambda _ hξ).prodMap
      (measurable_pi_lambda _ hξ))] at hh
  convert hh using 1
  · congr 1
    funext ω
    apply Prod.ext <;> funext j
    · simp [g, Function.comp_apply, resamplingPair, selectedArray, resampledSum,
        Finset.sum_apply, ite_apply]
    · simp only [g, Function.comp_apply, resamplingPair, resampledSum, Finset.sum_apply]
      apply Finset.sum_congr rfl
      intro i _
      cases hm : mask i <;> cases hx : x i <;>
        simp [Kane.maskedFlip, selectedArray, hm, hx]

/-- The genuine independent-copy coordinate-resampling law. -/
def freshResamplingLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (θ : ℝ) :
    Measure (Vector p × Vector p) :=
  bernoulliMixtureLaw (μ.prod μ) (freshResamplingPair ξ) θ

/-- The noise coupling proved using Kane equals ordinary coordinate resampling. -/
theorem independentCopyResampling_eq_fresh {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) (θ : ℝ) :
    independentCopyResamplingLaw μ ξ θ = freshResamplingLaw μ ξ θ := by
  unfold independentCopyResamplingLaw randomResamplingLaw bernoulliMixtureLaw
  simp_rw [resamplingPair_law_eq_fresh μ ξ hξ hind]
  rw [← Finset.sum_smul, uniformSelectorWeights_sum, one_smul]
  rfl

/-- Independently replace each fixed observation by a fresh observation
with probability `θ`. The law is a genuine product of one-coordinate mixtures. -/
def coordinateReplacementLaw {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (a : Fin n → Vector p) (θ : ℝ) :
    Measure (Fin n → Vector p) :=
  Measure.pi (fun i => ENNReal.ofReal (1 - θ) • Measure.dirac (a i) +
    ENNReal.ofReal θ • μ.map (ξ i))

private theorem replacementCoordinate_isProbability
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) (i : Fin n) :
    IsProbabilityMeasure (ENNReal.ofReal (1 - θ) • Measure.dirac (a i) +
      ENNReal.ofReal θ • μ.map (ξ i)) := by
  constructor
  simp only [Measure.add_apply, Measure.smul_apply, Measure.dirac_apply_of_mem
    (Set.mem_univ _), smul_eq_mul, mul_one,
    Measure.map_apply (hξ i) MeasurableSet.univ, Set.preimage_univ, measure_univ]
  rw [← ENNReal.ofReal_add (sub_nonneg.mpr hθone) hθ]
  norm_num

theorem coordinateReplacementLaw_isProbability
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    IsProbabilityMeasure (coordinateReplacementLaw μ ξ a θ) := by
  letI (i : Fin n) := replacementCoordinate_isProbability μ ξ hξ a θ hθ hθone i
  unfold coordinateReplacementLaw
  infer_instance

/-- Finite Bernoulli mixing of independent observations gives the product of
its one-observation mixture laws. -/
theorem bernoulliReplacement_eq_product
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (a : Fin n → Vector p) (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    bernoulliMixtureLaw μ (fun mask ω i => if mask i then ξ i ω else a i) θ =
      coordinateReplacementLaw μ ξ a θ := by
  classical
  let ν : Fin n → Measure (Vector p) := fun i =>
    ENNReal.ofReal (1 - θ) • Measure.dirac (a i) + ENNReal.ofReal θ • μ.map (ξ i)
  letI (i : Fin n) : IsProbabilityMeasure (ν i) :=
    replacementCoordinate_isProbability μ ξ hξ a θ hθ hθone i
  have hmeas (mask : Kane.Cube n) :
      Measurable (fun ω i => if mask i then ξ i ω else a i) := by
    apply measurable_pi_lambda
    intro i
    cases hi : mask i <;> simp only [hi, Bool.false_eq_true, ↓reduceIte]
    · exact measurable_const
    · exact hξ i
  symm
  apply Measure.pi_eq
  intro s hs
  unfold bernoulliMixtureLaw
  rw [Measure.finset_sum_apply]
  simp_rw [Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (hmeas _) (MeasurableSet.univ_pi hs)]
  have hpre (mask : Kane.Cube n) :
      (fun ω i => if mask i then ξ i ω else a i) ⁻¹' Set.univ.pi s =
        ⋂ i, ξ i ⁻¹' (if mask i then s i else if a i ∈ s i then Set.univ else ∅) := by
    ext ω
    simp only [Set.mem_preimage, Set.mem_pi, Set.mem_univ, forall_true_left,
      Set.mem_iInter]
    apply forall_congr'
    intro i
    cases hi : mask i <;> simp [hi]
  have hfactor (mask : Kane.Cube n) :
      μ ((fun ω i => if mask i then ξ i ω else a i) ⁻¹' Set.univ.pi s) =
        ∏ i, if mask i then (μ.map (ξ i)) (s i) else
          if a i ∈ s i then (1 : ENNReal) else 0 := by
    rw [hpre]
    have hh := hind.measure_inter_preimage_eq_mul Finset.univ
      (sets := fun i => if mask i then s i else if a i ∈ s i then Set.univ else ∅)
      (fun i _ => by
        cases hi : mask i
        · simp only [hi, Bool.false_eq_true, ↓reduceIte]
          split_ifs <;> simp
        · simpa only [hi, ↓reduceIte] using hs i)
    simp only [Finset.mem_univ, Set.iInter_true] at hh
    rw [hh]
    apply Finset.prod_congr rfl
    intro i _
    cases hi : mask i
    · simp only [hi, Bool.false_eq_true, ↓reduceIte]
      split_ifs <;> simp
    · simp [hi, Measure.map_apply (hξ i) (hs i)]
  simp_rw [hfactor]
  have hw (mask : Kane.Cube n) :
      ENNReal.ofReal (Kane.maskWeight θ mask) =
        ∏ i, ENNReal.ofReal (if mask i then θ else 1 - θ) := by
    exact ENNReal.ofReal_prod_of_nonneg (fun i _ => by
      cases hi : mask i <;> simp [hi, hθ, sub_nonneg.mpr hθone])
  simp_rw [hw, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun i (b : Bool) =>
    ENNReal.ofReal (if b then θ else 1 - θ) *
      (if b then (μ.map (ξ i)) (s i) else if a i ∈ s i then 1 else 0))]
  apply Finset.prod_congr rfl
  intro i _
  by_cases hmem : a i ∈ s i <;>
    simp [ν, Measure.add_apply, Measure.smul_apply, smul_eq_mul, hs i,
      Measure.dirac_apply, Set.indicator, hmem, add_comm]

private theorem pi_eval_map {p n : ℕ}
    (ν : Fin n → Measure (Vector p)) [∀ i, IsProbabilityMeasure (ν i)] (i : Fin n) :
    (Measure.pi ν).map (fun b => b i) = ν i := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs,
    ← Set.univ_pi_update_univ, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

/-- Replacement coordinates remain independent under their actual mixture law. -/
theorem coordinateReplacement_independent
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    iIndepFun (fun i (b : Fin n → Vector p) => b i)
      (coordinateReplacementLaw μ ξ a θ) := by
  let ν : Fin n → Measure (Vector p) := fun i =>
    ENNReal.ofReal (1 - θ) • Measure.dirac (a i) + ENNReal.ofReal θ • μ.map (ξ i)
  letI (i : Fin n) : IsProbabilityMeasure (ν i) :=
    replacementCoordinate_isProbability μ ξ hξ a θ hθ hθone i
  change iIndepFun (fun i (b : Fin n → Vector p) => b i) (Measure.pi ν)
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp_rw [pi_eval_map ν]
  exact Measure.map_id

/-- Integration of one replacement observation uses its two genuine mixture
components. -/
theorem integral_replacement_coordinate
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (i : Fin n) (g : Vector p → ℝ) (hg : Measurable g)
    (hgi : Integrable (fun ω => g (ξ i ω)) μ) :
    (∫ b, g (b i) ∂coordinateReplacementLaw μ ξ a θ) =
      (1 - θ) * g (a i) + θ * ∫ ω, g (ξ i ω) ∂μ := by
  let ν : Fin n → Measure (Vector p) := fun i =>
    ENNReal.ofReal (1 - θ) • Measure.dirac (a i) + ENNReal.ofReal θ • μ.map (ξ i)
  letI (i : Fin n) : IsProbabilityMeasure (ν i) :=
    replacementCoordinate_isProbability μ ξ hξ a θ hθ hθone i
  have hmap : (coordinateReplacementLaw μ ξ a θ).map (fun b => b i) = ν i :=
    pi_eval_map ν i
  have hgm : Integrable g (μ.map (ξ i)) :=
    (integrable_map_measure hg.aestronglyMeasurable (hξ i).aemeasurable).mpr hgi
  rw [← integral_map (measurable_pi_apply i).aemeasurable hg.aestronglyMeasurable,
    hmap]
  dsimp [ν]
  rw [integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (hgm.smul_measure ENNReal.ofReal_ne_top), integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hθone), ENNReal.toReal_ofReal hθ,
    integral_dirac, integral_map (hξ i).aemeasurable hg.aestronglyMeasurable]
  rfl

/-- The replacement keeps the original uniform coordinate envelope. -/
theorem replacement_coordinate_bound
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) {η : ℝ}
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (ha : ∀ i j, |a i j| ≤ η) (i : Fin n) (j : Fin p) :
    ∀ᵐ b ∂coordinateReplacementLaw μ ξ a θ, |b i j| ≤ η := by
  let ν : Fin n → Measure (Vector p) := fun i =>
    ENNReal.ofReal (1 - θ) • Measure.dirac (a i) + ENNReal.ofReal θ • μ.map (ξ i)
  letI (i : Fin n) : IsProbabilityMeasure (ν i) :=
    replacementCoordinate_isProbability μ ξ hξ a θ hθ hθone i
  have hv : ∀ᵐ v ∂ν i, |v j| ≤ η := by
    apply ae_add_measure_iff.mpr
    constructor
    · exact Measure.ae_smul_measure (by simpa only [ae_dirac_eq] using ha i j) _
    · apply Measure.ae_smul_measure
      exact (ae_map_iff (hξ i).aemeasurable
        (measurableSet_le (measurable_pi_apply j).abs measurable_const)).mpr (hbound i j)
  have hmap : (coordinateReplacementLaw μ ξ a θ).map (fun b => b i) = ν i :=
    pi_eval_map ν i
  rw [← hmap] at hv
  exact ae_of_ae_map (measurable_pi_apply i).aemeasurable hv

/-- Conditional centered summands have mean zero. -/
theorem replacement_centered_mean
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (i : Fin n) (j : Fin p) :
    (∫ b, b i j - (1 - θ) * a i j ∂coordinateReplacementLaw μ ξ a θ) = 0 := by
  have hh := integral_replacement_coordinate μ ξ hξ a θ hθ hθone i
    (fun v => v j - (1 - θ) * a i j)
    ((measurable_pi_apply j).sub measurable_const)
    ((hi i j).sub (integrable_const _))
  rw [integral_sub (hi i j) (integrable_const _), hcenter i j] at hh
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hh
  rw [hh]
  ring

/-- The conditional variance contains the fresh-copy variance and a further
nonnegative term from whether each fixed observation is replaced. -/
theorem replacement_centered_second
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (hi2 : ∀ i j, Integrable (fun ω => (ξ i ω j) ^ 2) μ)
    (i : Fin n) (j : Fin p) :
    (∫ b, (b i j - (1 - θ) * a i j) ^ 2 ∂coordinateReplacementLaw μ ξ a θ) =
      θ * (∫ ω, (ξ i ω j) ^ 2 ∂μ) + θ * (1 - θ) * (a i j) ^ 2 := by
  let c := (1 - θ) * a i j
  have hexp : (fun ω => (ξ i ω j - c) ^ 2) =
      (fun ω => (ξ i ω j) ^ 2 - 2 * c * ξ i ω j + c ^ 2) := by
    funext ω
    ring
  have hip : Integrable (fun ω => (ξ i ω j - c) ^ 2) μ := by
    rw [hexp]
    exact ((hi2 i j).sub ((hi i j).const_mul (2 * c))).add (integrable_const _)
  have hh := integral_replacement_coordinate μ ξ hξ a θ hθ hθone i
    (fun v => (v j - c) ^ 2) (((measurable_pi_apply j).sub measurable_const).pow_const 2) hip
  have hpoly : (∫ ω, (ξ i ω j - c) ^ 2 ∂μ) =
      (∫ ω, (ξ i ω j) ^ 2 ∂μ) + c ^ 2 := by
    rw [hexp, integral_add (f := fun ω => (ξ i ω j) ^ 2 - 2 * c * ξ i ω j) ((hi2 i j).sub ((hi i j).const_mul (2 * c)))
      (integrable_const _), integral_sub (f := fun ω => (ξ i ω j) ^ 2) (hi2 i j) ((hi i j).const_mul (2 * c)),
      integral_const_mul, hcenter i j]
    simp
  rw [hpoly] at hh
  rw [hh]
  dsimp [c]
  ring

/-- Centering the replacement changes its envelope by at most a factor two. -/
theorem replacement_centered_bound
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) {η : ℝ}
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (ha : ∀ i j, |a i j| ≤ η) (i : Fin n) (j : Fin p) :
    ∀ᵐ b ∂coordinateReplacementLaw μ ξ a θ,
      |b i j - (1 - θ) * a i j| ≤ 2 * η := by
  filter_upwards [replacement_coordinate_bound μ ξ hξ a θ hθ hθone hbound ha i j]
    with b hb
  calc
    _ ≤ |b i j| + |(1 - θ) * a i j| := abs_sub _ _
    _ = |b i j| + (1 - θ) * |a i j| := by
      rw [abs_mul, abs_of_nonneg (sub_nonneg.mpr hθone)]
    _ ≤ η + 1 * η := add_le_add hb
      (mul_le_mul (by linarith : 1 - θ ≤ 1) (ha i j) (abs_nonneg _) zero_le_one)
    _ = _ := by ring

private theorem independent_sum_second_moment
    {E : Type*} [MeasurableSpace E] {ν : Measure E} [IsProbabilityMeasure ν]
    {n : ℕ} {X : Fin n → E → ℝ} {B : ℝ}
    (hm : ∀ i, Measurable (X i)) (hind : iIndepFun X ν)
    (hb : ∀ i, ∀ᵐ b ∂ν, |X i b| ≤ B)
    (hc : ∀ i, (∫ b, X i b ∂ν) = 0) :
    (∫ b, (∑ i, X i b) ^ 2 ∂ν) = ∑ i, ∫ b, (X i b) ^ 2 ∂ν := by
  have hLp (i : Fin n) : MemLp (X i) 2 ν := by
    apply MemLp.of_bound (hm i).aestronglyMeasurable B
    simpa only [Real.norm_eq_abs] using hb i
  have hi (i : Fin n) : Integrable (X i) ν := by
    simpa only [pow_one] using integral_pow_of_bounded (hm i) (hb i) 1
  have hsc : (∫ b, ∑ i, X i b ∂ν) = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
    simp only [hc, Finset.sum_const_zero]
  have hv := IndepFun.variance_sum (s := Finset.univ) (X := X) (fun i _ => hLp i)
    (fun i _ j _ hij => hind.indepFun hij)
  have hvs (i : Fin n) : variance (X i) ν = ∫ b, (X i b) ^ 2 ∂ν := by
    rw [variance_def' (hLp i), hc i]
    simp
  simp_rw [hvs] at hv
  rw [variance_def' (memLp_finset_sum' Finset.univ (fun i _ => hLp i))] at hv
  simpa only [Finset.sum_apply, Pi.pow_apply, hsc, zero_pow (by decide : 2 ≠ 0),
    sub_zero] using hv

/-- The summed second moments equal the actual coordinate variance, with
no unit-variance normalization or spectral assumption. -/
theorem coordinate_second_moments_eq_covariance_of_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) {η : ℝ}
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (j : Fin p) :
    (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) = covariance μ (sumVector ξ) j j := by
  have hm (i : Fin n) : Measurable (fun ω => ξ i ω j) :=
    (measurable_pi_apply j).comp (hξ i)
  have hi (i : Fin n) : Integrable (fun ω => ξ i ω j) μ := by
    simpa only [pow_one] using integral_pow_of_bounded (hm i) (hbound i j) 1
  have hc : (∫ ω, ∑ i, ξ i ω j ∂μ) = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
    simp only [hcenter, Finset.sum_const_zero]
  have hh := independent_sum_second_moment hm
    (hind.comp (fun _ v => v j) (fun _ => measurable_pi_apply j))
    (fun i => hbound i j) (fun i => hcenter i j)
  rw [← hh]
  simp only [covariance, sumVector, Finset.sum_apply, hc, mul_zero, sub_zero, pow_two]

/-- Exact variance of the sum in the conditional resampling experiment. -/
theorem replacement_centered_sum_second
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) {η : ℝ}
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (ha : ∀ i j, |a i j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (j : Fin p) :
    (∫ b, (∑ i, (b i j - (1 - θ) * a i j)) ^ 2
      ∂coordinateReplacementLaw μ ξ a θ) =
      θ * (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) +
        θ * (1 - θ) * (∑ i, (a i j) ^ 2) := by
  letI := coordinateReplacementLaw_isProbability μ ξ hξ a θ hθ hθone
  have hm (i : Fin n) : Measurable (fun b : Fin n → Vector p => b i j - (1 - θ) * a i j) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).sub measurable_const
  have hi (i : Fin n) (k : Fin p) : Integrable (fun ω => ξ i ω k) μ := by
    simpa only [pow_one] using integral_pow_of_bounded
      ((measurable_pi_apply k).comp (hξ i)) (hbound i k) 1
  have hi2 (i : Fin n) (k : Fin p) : Integrable (fun ω => (ξ i ω k) ^ 2) μ :=
    integral_pow_of_bounded ((measurable_pi_apply k).comp (hξ i)) (hbound i k) 2
  rw [independent_sum_second_moment hm
    ((coordinateReplacement_independent μ ξ hξ a θ hθ hθone).comp
      (fun i v => v j - (1 - θ) * a i j)
      (fun _ => (measurable_pi_apply j).sub measurable_const))
    (fun i => replacement_centered_bound μ ξ hξ a θ hθ hθone hbound ha i j)
    (fun i => replacement_centered_mean μ ξ hξ a θ hθ hθone hcenter hi i j)]
  simp_rw [replacement_centered_second μ ξ hξ a θ hθ hθone hcenter hi hi2]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]

/-- Every conditional resampling sum has a uniform tail in either signed
coordinate direction, once its standard deviation dominates the envelope. -/
theorem replacement_centered_sum_tail
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (a : Fin n → Vector p)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) {η σ ε : ℝ}
    (hη : 0 ≤ η) (hσ : 0 < σ) (hησ : η ≤ σ) (hε : |ε| = 1)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (ha : ∀ i j, |a i j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (j : Fin p)
    (hvariance : θ * (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) +
      θ * (1 - θ) * (∑ i, (a i j) ^ 2) = σ ^ 2) :
    (1 : ℝ) / 16384 ≤ (coordinateReplacementLaw μ ξ a θ).real
      {b | σ / 256 ≤ ε * ((∑ i, b i j) - (1 - θ) * (∑ i, a i j))} := by
  classical
  let ν := coordinateReplacementLaw μ ξ a θ
  letI := coordinateReplacementLaw_isProbability μ ξ hξ a θ hθ hθone
  let X : Fin n → (Fin n → Vector p) → ℝ :=
    fun i b => ε * (b i j - (1 - θ) * a i j)
  have hm (i : Fin n) : Measurable (X i) := by
    change Measurable (fun b : Fin n → Vector p => ε * (b i j - (1 - θ) * a i j))
    have hcoord : Measurable (fun b : Fin n → Vector p => b i j) :=
      (measurable_pi_apply j).comp (measurable_pi_apply i)
    exact (hcoord.sub measurable_const).const_mul ε
  have hind : iIndepFun X ν :=
    (coordinateReplacement_independent μ ξ hξ a θ hθ hθone).comp
      (fun i v => ε * (v j - (1 - θ) * a i j))
      (fun i => by
        have hcoord : Measurable (fun v : Vector p => v j) := measurable_pi_apply j
        exact (hcoord.sub measurable_const).const_mul ε)
  have hb (i : Fin n) : ∀ᵐ b ∂ν, |X i b| ≤ 2 * η := by
    filter_upwards [replacement_centered_bound μ ξ hξ a θ hθ hθone hbound ha i j]
      with b hb
    simpa only [X, abs_mul, hε, one_mul] using hb
  have hi (i : Fin n) (k : Fin p) : Integrable (fun ω => ξ i ω k) μ := by
    simpa only [pow_one] using integral_pow_of_bounded
      ((measurable_pi_apply k).comp (hξ i)) (hbound i k) 1
  have hc (i : Fin n) : (∫ b, X i b ∂ν) = 0 := by
    dsimp [X, ν]
    rw [integral_const_mul, replacement_centered_mean μ ξ hξ a θ hθ hθone hcenter hi]
    simp
  have hεsq : ε ^ 2 = 1 := by nlinarith [sq_abs ε]
  have hs2 : (∫ b, (∑ i, X i b) ^ 2 ∂ν) = σ ^ 2 := by
    have hf : (fun b => (∑ i, X i b) ^ 2) =
        (fun b => (∑ i, (b i j - (1 - θ) * a i j)) ^ 2) := by
      funext b
      simp only [X, ← Finset.mul_sum, mul_pow, hεsq, one_mul]
    rw [hf, replacement_centered_sum_second μ ξ hξ a θ hθ hθone hbound ha hcenter j,
      hvariance]
  have hsm : Measurable (fun b => ∑ i, X i b) :=
    Finset.measurable_sum Finset.univ fun i _ => hm i
  have hsb : ∀ᵐ b ∂ν, |∑ i, X i b| ≤ (n : ℝ) * (2 * η) := by
    filter_upwards [ae_all_iff.mpr hb] with b hb
    calc
      _ ≤ ∑ i, |X i b| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _i : Fin n, 2 * η := Finset.sum_le_sum (fun i _ => hb i)
      _ = _ := by simp
  have hs1 : Integrable (fun b => ∑ i, X i b) ν := by
    simpa only [pow_one] using integral_pow_of_bounded hsm hsb 1
  have hsc : (∫ b, ∑ i, X i b ∂ν) = 0 := by
    rw [integral_finset_sum Finset.univ (fun i _ => by
      simpa only [pow_one] using integral_pow_of_bounded (hm i) (hb i) 1)]
    simp only [hc, Finset.sum_const_zero]
  have hs4 : (∫ b, (∑ i, X i b) ^ 4 ∂ν) ≤ 32 * σ ^ 4 := by
    have hh := independent_sum_fourth_moment_le hm hind hb hc
    rw [hs2] at hh
    have hηsq : η ^ 2 ≤ σ ^ 2 := by nlinarith
    have hprod := mul_nonneg (sub_nonneg.mpr hηsq) (sq_nonneg σ)
    nlinarith [sq_nonneg (σ ^ 2)]
  have ht := positive_tail_of_fourth_moment_scaled hσ hsm hs1
    (integral_pow_of_bounded hsm hsb 2) (integral_pow_of_bounded hsm hsb 4)
    hsc hs2 hs4
  convert ht using 2
  ext b
  simp only [X, Set.mem_setOf_eq, ← Finset.mul_sum, Finset.sum_sub_distrib]

private theorem integrable_bounded_one {E : Type*} [MeasurableSpace E]
    {ν : Measure E} [IsFiniteMeasure ν] {g : E → ℝ}
    (hg : Measurable g) (hgb : ∀ z, |g z| ≤ 1) : Integrable g ν := by
  apply (integrable_const (1 : ℝ)).mono' hg.aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun z => by simpa only [Real.norm_eq_abs] using hgb z)

private theorem measurable_replacementArray
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (a : Fin n → Vector p) (mask : Kane.Cube n) :
    Measurable (fun ω i => if mask i then ξ i ω else a i) := by
  apply measurable_pi_lambda
  intro i
  cases hi : mask i <;> simp only [hi, Bool.false_eq_true, ↓reduceIte]
  · exact measurable_const
  · exact hξ i

/-- Explicit conditional integration for the actual replacement-array law. -/
theorem integral_conditional_replacement
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (g : Vector p × Vector p → ℝ) (hg : Measurable g) (hgb : ∀ z, |g z| ≤ 1)
    (ω : Ω) :
    (∫ b, g (sumVector ξ ω, ∑ i, b i)
      ∂coordinateReplacementLaw μ ξ (fun i => ξ i ω) θ) =
      ∑ mask : Kane.Cube n, Kane.maskWeight θ mask *
        ∫ ω', g (freshResamplingPair ξ mask (ω, ω')) ∂μ := by
  let a : Fin n → Vector p := fun i => ξ i ω
  let H : (Fin n → Vector p) → ℝ := fun b => g (sumVector ξ ω, ∑ i, b i)
  have hH : Measurable H := hg.comp (measurable_const.prodMk measurable_arraySum)
  have hHb : ∀ b, |H b| ≤ 1 := fun b => hgb _
  have hmap (mask : Kane.Cube n) :
      IsProbabilityMeasure (μ.map (fun ω i => if mask i then ξ i ω else a i)) :=
    isProbabilityMeasure_map (measurable_replacementArray ξ hξ a mask).aemeasurable
  rw [← bernoulliReplacement_eq_product μ ξ hξ hind (fun i => ξ i ω) θ hθ hθone,
    integral_bernoulliMixtureLaw μ _ θ hθ hθone _ (fun mask => by
      letI := hmap mask
      exact integrable_bounded_one hH hHb)]
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_map (measurable_replacementArray ξ hξ a mask).aemeasurable
    hH.aestronglyMeasurable]
  congr 1
  apply integral_congr_ae
  filter_upwards [] with ω'
  dsimp only [H]
  congr 1
  apply Prod.ext
  · rfl
  · funext j
    simp [freshResamplingPair, H, a, resampledSum, Finset.sum_apply, ite_apply]

/-- The genuine resampling experiment disintegrates by an explicit finite
mixture and product integration. No conditional-probability existence theorem
or conditional-independence hypothesis is used. -/
theorem integral_freshResamplingLaw
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (g : Vector p × Vector p → ℝ) (hg : Measurable g) (hgb : ∀ z, |g z| ≤ 1) :
    (∫ z, g z ∂freshResamplingLaw μ ξ θ) =
      ∫ ω, ∫ b, g (sumVector ξ ω, ∑ i, b i)
        ∂coordinateReplacementLaw μ ξ (fun i => ξ i ω) θ ∂μ := by
  have hm (mask : Kane.Cube n) : Measurable (freshResamplingPair ξ mask) :=
    measurable_freshResamplingPair ξ hξ mask
  have hi (mask : Kane.Cube n) : Integrable g ((μ.prod μ).map (freshResamplingPair ξ mask)) := by
    letI := isProbabilityMeasure_map (μ := μ.prod μ) (hm mask).aemeasurable
    exact integrable_bounded_one hg hgb
  have hip (mask : Kane.Cube n) :
      Integrable (fun z => g (freshResamplingPair ξ mask z)) (μ.prod μ) :=
    integrable_bounded_one (hg.comp (hm mask)) (fun _ => hgb _)
  unfold freshResamplingLaw
  rw [integral_bernoulliMixtureLaw _ _ θ hθ hθone g hi]
  simp_rw [integral_map (hm _).aemeasurable hg.aestronglyMeasurable]
  simp_rw [integral_prod _ (hip _)]
  have hw (mask : Kane.Cube n) :
      Kane.maskWeight θ mask * (∫ ω, ∫ ω', g (freshResamplingPair ξ mask (ω, ω')) ∂μ ∂μ) =
        ∫ ω, Kane.maskWeight θ mask * (∫ ω', g (freshResamplingPair ξ mask (ω, ω')) ∂μ) ∂μ :=
    (integral_const_mul _ _).symm
  simp_rw [hw]
  rw [← integral_finset_sum Finset.univ (fun mask _ =>
    ((hip mask).integral_prod_left).const_mul _)]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω =>
    (integral_conditional_replacement μ ξ hξ hind θ hθ hθone g hg hgb ω).symm)

theorem integrable_conditional_replacement
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1)
    (g : Vector p × Vector p → ℝ) (hg : Measurable g) (hgb : ∀ z, |g z| ≤ 1) :
    Integrable (fun ω => ∫ b, g (sumVector ξ ω, ∑ i, b i)
      ∂coordinateReplacementLaw μ ξ (fun i => ξ i ω) θ) μ := by
  have hip (mask : Kane.Cube n) :
      Integrable (fun z => g (freshResamplingPair ξ mask z)) (μ.prod μ) :=
    integrable_bounded_one (hg.comp (measurable_freshResamplingPair ξ hξ mask)) (fun _ => hgb _)
  have hf := funext (integral_conditional_replacement μ ξ hξ hind θ hθ hθone g hg hgb)
  rw [hf]
  exact integrable_finset_sum Finset.univ (fun mask _ =>
    ((hip mask).integral_prod_left).const_mul _)

namespace FaceSmoother

/-- Expand every active face of the rectangle by a common amount. -/
def outerSet {p : ℕ} (s : FaceSmoother p) (a : ℝ) : Set (Vector p) :=
  {z | ∀ f ∈ s.faces, normalDot f z ≤ s.offsets f + a}

/-- The closed outer rectangle with its closed inner rectangle removed. -/
def boundaryLayer {p : ℕ} (s : FaceSmoother p) (a : ℝ) : Set (Vector p) :=
  s.outerSet a \ s.outerSet (-a)

theorem measurableSet_outerSet {p : ℕ} (s : FaceSmoother p) (a : ℝ) :
    MeasurableSet (s.outerSet a) := by
  unfold outerSet
  simp only [Set.setOf_forall]
  apply MeasurableSet.iInter
  intro f
  apply MeasurableSet.iInter
  intro _
  have hm : Measurable (normalDot f) := by
    change Measurable (fun z : Vector p => if f.2 then z f.1 else -z f.1)
    cases hf : f.2 <;> simp only [hf, Bool.false_eq_true, ↓reduceIte]
    · exact (measurable_pi_apply f.1).neg
    · exact measurable_pi_apply f.1
  exact measurableSet_le hm measurable_const

theorem measurableSet_boundaryLayer {p : ℕ} (s : FaceSmoother p) (a : ℝ) :
    MeasurableSet (s.boundaryLayer a) :=
  (s.measurableSet_outerSet a).diff (s.measurableSet_outerSet (-a))

/-- A point in the boundary layer exits the outer rectangle with uniformly
positive probability in the actual conditional replacement experiment.
The gap condition quantifies precisely the required noise scale and drift. -/
theorem replacement_crossing_probability
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (a : Fin n → Vector p) (r : Vector p) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) {η v d : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (ha : ∀ i j, |a i j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hsecond : ∀ j, (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) = v)
    (hscale : η ≤ Real.sqrt (θ * v))
    (hpoint : (∑ i, a i) + r ∈ s.boundaryLayer d)
    (hgap : 2 * d + θ * ‖∑ i, a i‖ < Real.sqrt (θ * v) / 256) :
    (1 : ℝ) / 16384 ≤ (coordinateReplacementLaw μ ξ a θ).real
      {b | (∑ i, b i) + r ∉ s.outerSet d} := by
  classical
  let A : Vector p := ∑ i, a i
  have hinner : ¬∀ f ∈ s.faces, normalDot f (A + r) ≤ s.offsets f - d := by
    simpa only [boundaryLayer, Set.mem_diff, outerSet, Set.mem_setOf_eq, sub_eq_add_neg]
      using hpoint.2
  push_neg at hinner
  obtain ⟨f, hf, hnear⟩ := hinner
  let ε : ℝ := if f.2 then 1 else -1
  let V := θ * v + θ * (1 - θ) * (∑ i, (a i f.1) ^ 2)
  let σ := Real.sqrt V
  have hV : θ * v ≤ V := by
    dsimp [V]
    have hp : 0 ≤ θ * (1 - θ) * (∑ i, (a i f.1) ^ 2) :=
      mul_nonneg (mul_nonneg hθ.le (sub_nonneg.mpr hθone))
        (Finset.sum_nonneg (fun i _ => sq_nonneg (a i f.1)))
    linarith
  have hV0 : 0 < V := (mul_pos hθ hv).trans_le hV
  have hσ : 0 < σ := Real.sqrt_pos.mpr hV0
  have hσge : Real.sqrt (θ * v) ≤ σ := Real.sqrt_le_sqrt hV
  have hvariance : θ * (∑ i, ∫ ω, (ξ i ω f.1) ^ 2 ∂μ) +
      θ * (1 - θ) * (∑ i, (a i f.1) ^ 2) = σ ^ 2 := by
    rw [hsecond, Real.sq_sqrt hV0.le]
  have hε : |ε| = 1 := by cases he : f.2 <;> simp [ε, he]
  have htail := replacement_centered_sum_tail μ ξ hξ a θ hθ.le hθone
    hη hσ (hscale.trans hσge) hε hbound ha hcenter f.1 hvariance
  letI := coordinateReplacementLaw_isProbability μ ξ hξ a θ hθ.le hθone
  apply htail.trans
  apply measureReal_mono (μ := coordinateReplacementLaw μ ξ a θ) ?_ (measure_ne_top _ _)
  intro b hb
  change ¬∀ g ∈ s.faces, normalDot g ((∑ i, b i) + r) ≤ s.offsets g + d
  intro hout
  have hA : ε * A f.1 ≤ ‖A‖ := by
    have hh : |A f.1| ≤ ‖A‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm A f.1
    calc
      _ ≤ |ε * A f.1| := le_abs_self _
      _ = |A f.1| := by rw [abs_mul, hε, one_mul]
      _ ≤ _ := hh
  have hnorm : normalDot f ((∑ i, b i) + r) =
      ε * ((∑ i, b i f.1) - (1 - θ) * (∑ i, a i f.1)) +
        normalDot f (A + r) - θ * (ε * A f.1) := by
    cases he : f.2 <;> simp [normalDot, ε, he, A, Finset.sum_apply] <;> ring
  have hdrift := mul_le_mul_of_nonneg_left hA hθ.le
  have hh := hout f hf
  rw [hnorm] at hh
  change σ / 256 ≤ ε * ((∑ i, b i f.1) - (1 - θ) * (∑ i, a i f.1)) at hb
  change 2 * d + θ * ‖A‖ < Real.sqrt (θ * v) / 256 at hgap
  linarith

/-- Uniform conditional crossings control the actual boundary probability on
the moderate-sum event by the genuine resampling disagreement probability. -/
theorem boundary_good_probability_le_disagreement
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (r : Vector p) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) {η v d : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hsecond : ∀ j, (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) = v)
    (hscale : η ≤ Real.sqrt (θ * v)) :
    (1 : ℝ) / 16384 * μ.real {ω | sumVector ξ ω + r ∈ s.boundaryLayer d ∧
      2 * d + θ * ‖sumVector ξ ω‖ < Real.sqrt (θ * v) / 256} ≤
      (freshResamplingLaw μ ξ θ).real
        (membershipDisagreement {z | z + r ∈ s.outerSet d}) := by
  classical
  let A : Set (Vector p) := {z | z + r ∈ s.outerSet d}
  let G : Set Ω := {ω | sumVector ξ ω + r ∈ s.boundaryLayer d ∧
    2 * d + θ * ‖sumVector ξ ω‖ < Real.sqrt (θ * v) / 256}
  let g := disagreementValue A
  have hS : Measurable (sumVector ξ) :=
    Finset.measurable_sum Finset.univ (fun i _ => hξ i)
  have hA : MeasurableSet A :=
    (s.measurableSet_outerSet d).preimage (measurable_id.add_const r)
  have hG : MeasurableSet G :=
    ((s.measurableSet_boundaryLayer d).preimage (hS.add_const r)).inter
      (measurableSet_lt ((hS.norm.const_mul θ).const_add (2 * d)) measurable_const)
  have hg : Measurable g := measurable_disagreementValue hA
  have hgb : ∀ z, |g z| ≤ 1 := by
    intro z
    by_cases hz : z ∈ membershipDisagreement A <;> simp [g, disagreementValue, hz]
  let e : Ω → ℝ := fun ω => ∫ b, g (sumVector ξ ω, ∑ i, b i)
    ∂coordinateReplacementLaw μ ξ (fun i => ξ i ω) θ
  have hei : Integrable e μ :=
    integrable_conditional_replacement μ ξ hξ hind θ hθ.le hθone g hg hgb
  have hpoint : ∀ᵐ ω ∂μ, G.indicator (fun _ => (1 : ℝ) / 16384) ω ≤ e ω := by
    filter_upwards [ae_all_iff.mpr (fun i => ae_all_iff.mpr (hbound i))] with ω hω
    by_cases hgood : ω ∈ G
    · rw [Set.indicator_of_mem hgood]
      have hc := s.replacement_crossing_probability μ ξ hξ (fun i => ξ i ω) r θ
        hθ hθone hη hv hbound hω hcenter hsecond hscale hgood.1 hgood.2
      have hinside : sumVector ξ ω ∈ A := hgood.1.1
      have hset : MeasurableSet {b : Fin n → Vector p | (∑ i, b i) + r ∉ s.outerSet d} :=
        ((s.measurableSet_outerSet d).preimage (measurable_arraySum.add_const r)).compl
      have heq : (fun b => g (sumVector ξ ω, ∑ i, b i)) =
          {b : Fin n → Vector p | (∑ i, b i) + r ∉ s.outerSet d}.indicator (fun _ => (1 : ℝ)) := by
        funext b
        change sumVector ξ ω + r ∈ s.outerSet d at hinside
        by_cases hb : (∑ i, b i) + r ∈ s.outerSet d <;>
          simp [g, disagreementValue, membershipDisagreement, Set.mem_symmDiff,
            A, Set.indicator, hinside, hb]
      change (1 : ℝ) / 16384 ≤ ∫ b, g (sumVector ξ ω, ∑ i, b i)
        ∂coordinateReplacementLaw μ ξ (fun i => ξ i ω) θ
      rw [heq, integral_indicator_const (1 : ℝ) hset, smul_eq_mul, mul_one]
      exact hc
    · rw [Set.indicator_of_not_mem hgood]
      apply integral_nonneg
      intro b
      simp only [g, disagreementValue, Set.indicator]
      split_ifs <;> norm_num
  have hh := integral_mono_ae ((integrable_const ((1 : ℝ) / 16384)).indicator hG) hei hpoint
  rw [integral_indicator_const _ hG, smul_eq_mul, mul_comm] at hh
  change (1 : ℝ) / 16384 * μ.real G ≤ _
  apply hh.trans_eq
  rw [← integral_freshResamplingLaw μ ξ hξ hind θ hθ.le hθone g hg hgb]
  exact integral_indicator_one (measurableSet_membershipDisagreement hA)

private theorem normalDot_add {p : ℕ} (f : Face p) (z r : Vector p) :
    normalDot f (z + r) = normalDot f z + normalDot f r := by
  cases hf : f.2 <;> simp [normalDot, hf, add_comm]

/-- Kane's verified noise estimate for an expanded and translated rectangle
in the ordinary independent-copy resampling model. -/
theorem freshResampling_outer_disagreement_le
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (r : Vector p) (d : ℝ)
    (hp : 1 ≤ p) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    (freshResamplingLaw μ ξ θ).real
        (membershipDisagreement {z | z + r ∈ s.outerSet d}) ≤
      8 * Real.sqrt (θ * dimensionLog p) := by
  let t : FaceSmoother p :=
    { faces := s.faces
      offsets := fun f => s.offsets f + d - normalDot f r
      bandwidth := s.bandwidth
      bandwidth_pos := s.bandwidth_pos }
  have hset : {z | z + r ∈ s.outerSet d} = {z | t.Inside z} := by
    ext z
    simp only [Set.mem_setOf_eq, outerSet, Inside, faceScore, normalDot_add]
    constructor <;> intro h f hf <;> have hh := h f hf <;>
      dsimp [t] at * <;> linarith
  rw [hset, ← independentCopyResampling_eq_fresh μ ξ hξ hind θ]
  exact t.independentCopyResampling_disagreement_le μ ξ hξ hp θ hθ hθone

/-- An actual concentration estimate before optimizing the resampling rate:
the boundary probability is controlled by Kane's noise estimate and one
ordinary maximum tail of the original sum. -/
theorem boundary_probability_le_noise_add_tail
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (r : Vector p) (hp : 1 ≤ p) (θ : ℝ)
    (hθ : 0 < θ) (hθone : θ ≤ 1) {η v d M : ℝ}
    (hη : 0 ≤ η) (hv : 0 < v)
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ η)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hsecond : ∀ j, (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) = v)
    (hscale : η ≤ Real.sqrt (θ * v))
    (hgap : 2 * d + θ * M < Real.sqrt (θ * v) / 256) :
    μ.real {ω | sumVector ξ ω + r ∈ s.boundaryLayer d} ≤
      131072 * Real.sqrt (θ * dimensionLog p) +
        μ.real {ω | M < ‖sumVector ξ ω‖} := by
  let G : Set Ω := {ω | sumVector ξ ω + r ∈ s.boundaryLayer d ∧
    2 * d + θ * ‖sumVector ξ ω‖ < Real.sqrt (θ * v) / 256}
  have hg := s.boundary_good_probability_le_disagreement (d := d) μ ξ hξ hind r θ hθ hθone
    hη hv hbound hcenter hsecond hscale
  have hu := s.freshResampling_outer_disagreement_le μ ξ hξ hind r d hp θ hθ hθone
  have hgood : μ.real G ≤ 131072 * Real.sqrt (θ * dimensionLog p) := by
    dsimp [G]
    linarith
  have hsub : {ω | sumVector ξ ω + r ∈ s.boundaryLayer d} ⊆
      G ∪ {ω | M < ‖sumVector ξ ω‖} := by
    intro ω hω
    by_cases hb : M < ‖sumVector ξ ω‖
    · exact Or.inr hb
    · left
      refine ⟨hω, ?_⟩
      have hnorm := mul_le_mul_of_nonneg_left (le_of_not_gt hb) hθ.le
      exact lt_of_le_of_lt (add_le_add_left hnorm _) hgap
  calc
    _ ≤ μ.real (G ∪ {ω | M < ‖sumVector ξ ω‖}) := measureReal_mono hsub
    _ ≤ μ.real G + μ.real {ω | M < ‖sumVector ξ ω‖} := measureReal_union_le _ _
    _ ≤ _ := add_le_add_right hgood _

end FaceSmoother

/-- The first resampling-coupling marginal is the actual original sum law. -/
theorem independentCopyResampling_fst_eq_original
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (independentCopyResamplingLaw μ ξ θ).map Prod.fst = μ.map (sumVector ξ) := by
  have hh := randomResamplingLaw_fst (μ.prod μ)
    (fun ω i => ξ i ω.1) (fun ω i => ξ i ω.2)
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst))
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd)) θ hθ hθone
  exact hh.trans (independentCopy_uniformResampledSumLaw_eq_original μ ξ hξ hind)

/-- The perturbed marginal also has the actual original sum law. -/
theorem independentCopyResampling_snd_eq_original
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hθone : θ ≤ 1) :
    (independentCopyResamplingLaw μ ξ θ).map Prod.snd = μ.map (sumVector ξ) := by
  have hh := randomResamplingLaw_snd (μ.prod μ)
    (fun ω i => ξ i ω.1) (fun ω i => ξ i ω.2)
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_fst))
    (measurable_pi_lambda _ (fun i => (hξ i).comp measurable_snd)) θ hθ hθone
  exact hh.trans (independentCopy_uniformResampledSumLaw_eq_original μ ξ hξ hind)

end

end RectangleCLT
