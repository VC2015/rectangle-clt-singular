import RectangleCLT.BernoulliPathDerivative
import RectangleCLT.OneObservationBounds
import RectangleCLT.BernoulliSelectorAlgebra

/-! Common-point aggregation for the actual Bernoulli--Gaussian derivative. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

/-- A fixed selector's leave-one-out sum is independent of the omitted
original observation. -/
theorem indepFun_maskObservationSum_leaveOne
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (mask : Kane.Cube n) (i : Fin n) :
    IndepFun (ξ i) (maskObservationSum ξ (Function.update mask i false)) μ := by
  classical
  let g : Fin n → Vector p → Vector p := fun j v =>
    if j = i then v else if mask j then v else 0
  have hg (j : Fin n) : Measurable (g j) := by
    by_cases hji : j = i
    · simpa only [g, hji, ↓reduceIte] using measurable_id
    · cases hj : mask j
      · simpa only [g, hji, hj, Bool.false_eq_true, ↓reduceIte] using
          (measurable_const : Measurable (fun _ : Vector p => (0 : Vector p)))
      · simpa only [g, hji, hj, ↓reduceIte] using
          (measurable_id : Measurable (id : Vector p → Vector p))
  have hmeas (j : Fin n) : Measurable (g j ∘ ξ j) := (hg j).comp (hξ j)
  have hh := ((hind.comp g hg).indepFun_finset_sum_of_not_mem hmeas
    (Finset.not_mem_erase i Finset.univ)).symm
  have heq : (∑ j ∈ Finset.univ.erase i, g j ∘ ξ j) =
      maskObservationSum ξ (Function.update mask i false) := by
    funext ω
    simp only [Finset.sum_apply, Function.comp_def, maskObservationSum]
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => if Function.update mask i false j then ξ j ω else 0) (Finset.mem_univ i)]
    simp only [Function.update_self, Bool.false_eq_true, ↓reduceIte, add_zero]
    apply Finset.sum_congr rfl
    intro j hj
    have hji := (Finset.mem_erase.mp hj).1
    simp only [g, hji, ↓reduceIte, Function.update_of_ne hji]
  rw [heq] at hh
  simpa only [g, ↓reduceIte, Function.comp_def] using hh

/-- Independence replaces one observation by a genuine fresh copy under the
same probability measure. The test is allowed to couple the two arguments. -/
theorem integral_indep_pair_eq_double
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U V : Ω → Vector p)
    (hU : Measurable U) (hV : Measurable V) (hind : IndepFun U V μ)
    (f : Vector p × Vector p → ℝ) (hf : Measurable f)
    (hfi : Integrable f ((μ.map U).prod (μ.map V))) :
    (∫ ω, f (U ω, V ω) ∂μ) = ∫ ω, ∫ ω', f (U ω', V ω) ∂μ ∂μ := by
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map
    hU.aemeasurable hV.aemeasurable).mp hind
  calc
    _ = ∫ z, f z ∂μ.map (fun ω => (U ω, V ω)) :=
      (integral_map (hU.prodMk hV).aemeasurable hf.aestronglyMeasurable).symm
    _ = ∫ z, f z ∂(μ.map U).prod (μ.map V) := by rw [hlaw]
    _ = ∫ v, ∫ u, f (u, v) ∂μ.map U ∂μ.map V := integral_prod_symm _ hfi
    _ = ∫ v, ∫ ω', f (U ω', v) ∂μ ∂μ.map V := by
      apply integral_congr_ae
      refine ae_of_all _ (fun v => ?_)
      exact integral_map hU.aemeasurable
        ((hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)
    _ = _ := by
      apply integral_map hV.aemeasurable
      exact hfi.integral_prod_right.aestronglyMeasurable.congr
        (ae_of_all _ (fun v => by
          exact integral_map hU.aemeasurable
            ((hf.comp (measurable_id.prodMk measurable_const)).aestronglyMeasurable)))

/-- A test bounded on the first marginal's almost-sure support is integrable
under the genuine independent product law. -/
theorem integrable_pair_of_bounded_first
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U V : Ω → Vector p)
    (hU : Measurable U) (_hV : Measurable V)
    {δ C : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ δ)
    (f : Vector p × Vector p → ℝ) (hf : Measurable f)
    (hbdd : ∀ u v, ‖u‖ ≤ δ → ‖f (u, v)‖ ≤ C) :
    Integrable f ((μ.map U).prod (μ.map V)) := by
  letI : IsProbabilityMeasure (μ.map U) := isProbabilityMeasure_map hU.aemeasurable
  letI : IsProbabilityMeasure (μ.map V) := isProbabilityMeasure_map _hV.aemeasurable
  have hmap : ∀ᵐ u ∂μ.map U, ‖u‖ ≤ δ :=
    (ae_map_iff hU.aemeasurable (measurableSet_le measurable_id.norm measurable_const)).mpr hbound
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  apply (Measure.ae_prod_iff_ae_ae
    (measurableSet_le (hf.norm) measurable_const)).mpr
  filter_upwards [hmap] with u hu
  exact ae_of_all _ (fun v => hbdd u v hu)

theorem maskObservationSum_update_add
    {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (mask : Kane.Cube n) (i : Fin n) (b : Bool) (ω : Ω) :
    maskObservationSum ξ (Function.update mask i b) ω =
      maskObservationSum ξ (Function.update mask i false) ω + (if b then ξ i ω else 0) := by
  classical
  have hsum (c : Bool) :
      maskObservationSum ξ (Function.update mask i c) ω =
        (∑ j ∈ Finset.univ.erase i, if mask j then ξ j ω else 0) +
          (if c then ξ i ω else 0) := by
    unfold maskObservationSum
    rw [← Finset.sum_erase_add Finset.univ
      (fun j => if Function.update mask i c j then ξ j ω else 0) (Finset.mem_univ i)]
    rw [Function.update_self]
    congr 1
    apply Finset.sum_congr rfl
    intro j hj
    rw [Function.update_of_ne (Finset.mem_erase.mp hj).1]
  rw [hsum b, hsum false]
  simp

/-- Force one selector on, then replace that independent observation by a
fresh copy. This identity applies to any bounded continuous test. -/
theorem integral_mask_force_true_eq_double
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (mask : Kane.Cube n) (i : Fin n) (a : ℝ) (x : Vector p)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    (∫ ω, G (x + a • maskObservationSum ξ (Function.update mask i true) ω) ∂μ) =
      ∫ ω, ∫ ω', G (x + a • maskObservationSum ξ (Function.update mask i false) ω +
        a • ξ i ω') ∂μ ∂μ := by
  let V := maskObservationSum ξ (Function.update mask i false)
  let f : Vector p × Vector p → ℝ := fun z => G (x + a • z.2 + a • z.1)
  have hV := measurable_maskObservationSum ξ hξ (Function.update mask i false)
  have hf : Measurable f := by
    apply hG.measurable.comp
    fun_prop
  have hfi : Integrable f ((μ.map (ξ i)).prod (μ.map V)) :=
    integrable_pair_of_bounded_first μ (ξ i) V (hξ i) hV (hbound i) f hf
      (fun u v _ => hGbound _)
  have h := integral_indep_pair_eq_double μ (ξ i) V (hξ i) hV
    (indepFun_maskObservationSum_leaveOne μ ξ hξ hind mask i) f hf hfi
  convert h using 1
  · apply integral_congr_ae
    refine ae_of_all _ (fun ω => ?_)
    dsimp [f, V]
    rw [maskObservationSum_update_add ξ mask i true ω]
    simp only [Bool.true_eq, ↓reduceIte, smul_add, add_assoc]

/-- The same fresh-copy identity for a coordinate times a bounded test. -/
theorem integral_coordinate_mask_force_true_eq_double
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (mask : Kane.Cube n) (i : Fin n) (a : ℝ) (x : Vector p) (j : Fin p)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (_hC : 0 ≤ C)
    (hGbound : ∀ y, ‖G y‖ ≤ C) :
    (∫ ω, ξ i ω j * G (x + a • maskObservationSum ξ (Function.update mask i true) ω) ∂μ) =
      ∫ ω, ∫ ω', ξ i ω' j * G (x + a • maskObservationSum ξ (Function.update mask i false) ω +
        a • ξ i ω') ∂μ ∂μ := by
  let V := maskObservationSum ξ (Function.update mask i false)
  let f : Vector p × Vector p → ℝ := fun z => z.1 j * G (x + a • z.2 + a • z.1)
  have hV := measurable_maskObservationSum ξ hξ (Function.update mask i false)
  have hf : Measurable f := by
    apply Measurable.mul
    · exact (measurable_pi_apply j).comp measurable_fst
    · apply hG.measurable.comp
      fun_prop
  have hfi : Integrable f ((μ.map (ξ i)).prod (μ.map V)) := by
    apply integrable_pair_of_bounded_first μ (ξ i) V (hξ i) hV (hbound i) f hf
      (C := δ * C)
    intro u v hu
    change ‖u j * G (x + a • v + a • u)‖ ≤ δ * C
    rw [norm_mul]
    exact mul_le_mul ((norm_le_pi_norm u j).trans hu) (hGbound _) (norm_nonneg _) hδ
  have h := integral_indep_pair_eq_double μ (ξ i) V (hξ i) hV
    (indepFun_maskObservationSum_leaveOne μ ξ hξ hind mask i) f hf hfi
  convert h using 1
  · apply integral_congr_ae
    refine ae_of_all _ (fun ω => ?_)
    dsimp [f, V]
    rw [maskObservationSum_update_add ξ mask i true ω]
    simp only [Bool.true_eq, ↓reduceIte, smul_add, add_assoc]

theorem integrable_bounded_test_comp
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (W : Ω → Vector p) (hW : Measurable W)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    Integrable (fun ω => G (W ω)) μ :=
  (integrable_const C).mono' (hG.measurable.comp hW).aestronglyMeasurable
    (ae_of_all _ (fun _ω => hGbound _))

theorem integrable_coordinate_mul_bounded_test
    {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Vector p) (hξ : Measurable ξ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (W : Ω → Vector p) (hW : Measurable W) (j : Fin p)
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ) (hGbound : ∀ y, ‖G y‖ ≤ C) :
    Integrable (fun ω => ξ ω j * G (W ω)) μ := by
  apply (integrable_const (δ * C)).mono'
    ((((measurable_pi_apply j).comp hξ).mul (hG.measurable.comp hW)).aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  rw [norm_mul]
  exact mul_le_mul ((norm_le_pi_norm (ξ ω) j).trans hω)
    (hGbound _) (norm_nonneg _) hδ

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem heatShiftDerivative_eq_spatial_add_heat
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ζ : Ω → Vector p) (hζ : Measurable ζ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ᵐ ω ∂μ, ‖ζ ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    s.heatShiftDerivative μ ζ A x t =
      (∫ ω, ∑ j, ζ ω j * s.convolutionFirstDerivative
        (gaussianLaw (Real.sqrt t • A)) (x + thinningScale t • ζ ω) j ∂μ) +
      (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        ∫ ω, s.convolutionSecondDerivative
          (gaussianLaw (Real.sqrt t • A)) (x + thinningScale t • ζ ω) j k ∂μ := by
  let ν := gaussianLaw (Real.sqrt t • A)
  let W := fun ω => x + thinningScale t • ζ ω
  have hW : Measurable W := measurable_const.add (measurable_const.smul hζ)
  have h₁ (j : Fin p) : Integrable
      (fun ω => ζ ω j * s.convolutionFirstDerivative ν (W ω) j) μ :=
    integrable_coordinate_mul_bounded_test μ ζ hζ hδ hbound W hW j _
      (s.continuous_convolutionFirstDerivative ν j) _
      (fun y => s.norm_convolutionFirstDerivative_le ν y j)
  have h₂ (j k : Fin p) : Integrable
      (fun ω => s.convolutionSecondDerivative ν (W ω) j k) μ :=
    integrable_bounded_test_comp μ W hW _ (s.continuous_convolutionSecondDerivative ν j k)
      _ (fun y => s.norm_convolutionSecondDerivative_le ν y j k)
  unfold heatShiftDerivative
  change (∫ ω, (∑ j, ζ ω j * s.convolutionFirstDerivative ν (W ω) j) +
      (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative ν (W ω) j k ∂μ) = _
  rw [integral_add
    (integrable_finset_sum Finset.univ (fun j _ => h₁ j))
    ((integrable_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (h₂ j k).const_mul _))).const_mul _),
    integral_const_mul,
    integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ => (h₂ j k).const_mul _))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => (h₂ _ k).const_mul _),
    integral_const_mul]
  rfl

noncomputable def fixedSelectorValue (ν : Measure (Vector p))
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (a : ℝ)
    (mask : Kane.Cube n) : ℝ :=
  ∫ ω, s.convolution ν (x + a • maskObservationSum ξ mask ω) ∂μ

noncomputable def fixedSelectorGradient (ν : Measure (Vector p))
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (x : Vector p) (a : ℝ)
    (i : Fin n) (mask : Kane.Cube n) : ℝ :=
  ∫ ω, ∑ j, ξ i ω j * s.convolutionFirstDerivative ν
    (x + a • maskObservationSum ξ mask ω) j ∂μ

noncomputable def fixedSelectorHeat (ν : Measure (Vector p))
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (Q : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a : ℝ)
    (mask : Kane.Cube n) : ℝ :=
  (1 / 2 : ℝ) * ∑ j, ∑ k, Q j k *
    ∫ ω, s.convolutionSecondDerivative ν (x + a • maskObservationSum ξ mask ω) j k ∂μ

theorem integral_maskObservationSum_gradient_eq
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (mask : Kane.Cube n) :
    (∫ ω, ∑ j, maskObservationSum ξ mask ω j *
      s.convolutionFirstDerivative ν (x + a • maskObservationSum ξ mask ω) j ∂μ) =
      ∑ i, if mask i then s.fixedSelectorGradient ν μ ξ x a i mask else 0 := by
  let W := fun ω => x + a • maskObservationSum ξ mask ω
  have hW : Measurable W :=
    measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))
  have hi (i : Fin n) (j : Fin p) : Integrable
      (fun ω => ξ i ω j * s.convolutionFirstDerivative ν (W ω) j) μ :=
    integrable_coordinate_mul_bounded_test μ (ξ i) (hξ i) hδ (hbound i) W hW j _
      (s.continuous_convolutionFirstDerivative ν j) _
      (fun y => s.norm_convolutionFirstDerivative_le ν y j)
  have hif (i : Fin n) : Integrable
      (fun ω => if mask i then ∑ j, ξ i ω j * s.convolutionFirstDerivative ν (W ω) j else 0) μ := by
    cases hm : mask i
    · simpa only [hm, Bool.false_eq_true, ↓reduceIte] using (integrable_const (0 : ℝ))
    · simpa only [hm, ↓reduceIte] using
        integrable_finset_sum Finset.univ (fun j _ => hi i j)
  have heq (ω : Ω) :
      (∑ j, maskObservationSum ξ mask ω j * s.convolutionFirstDerivative ν (W ω) j) =
        ∑ i, if mask i then ∑ j, ξ i ω j * s.convolutionFirstDerivative ν (W ω) j else 0 := by
    simp only [maskObservationSum, Finset.sum_apply, ite_apply, Pi.zero_apply,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    cases hm : mask i <;> simp [hm]
  calc
    _ = ∫ ω, ∑ i, if mask i then
        ∑ j, ξ i ω j * s.convolutionFirstDerivative ν (W ω) j else 0 ∂μ :=
      integral_congr_ae (ae_of_all _ heq)
    _ = _ := by
      rw [integral_finset_sum Finset.univ (fun i _ => hif i)]
      apply Finset.sum_congr rfl
      intro i _
      cases hm : mask i <;> simp only [hm, Bool.false_eq_true, ↓reduceIte,
        integral_zero, fixedSelectorGradient]
      rfl

/-- The actual path derivative regrouped into one-coordinate forced-selector
increments, retained amplitude terms, and the heat covariance contribution. -/
theorem selectorHeatDerivative_eq_forced_increments
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) :
    s.selectorHeatDerivative μ ξ A x t =
      ((t - 3) / (1 + t) ^ 3) *
        (∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
          (s.fixedSelectorValue (gaussianLaw (Real.sqrt t • A)) μ ξ x (thinningScale t)
              (Function.update mask i true) -
            s.fixedSelectorValue (gaussianLaw (Real.sqrt t • A)) μ ξ x (thinningScale t)
              (Function.update mask i false))) +
      thinningProbability t *
        (∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
          s.fixedSelectorGradient (gaussianLaw (Real.sqrt t • A)) μ ξ x (thinningScale t)
            i (Function.update mask i true)) +
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        s.fixedSelectorHeat (gaussianLaw (Real.sqrt t • A)) μ ξ
          (A * A.transpose) x (thinningScale t) mask := by
  let ν := gaussianLaw (Real.sqrt t • A)
  have hsplit (mask : Kane.Cube n) :
      s.heatShiftDerivative μ (maskObservationSum ξ mask) A x t =
        (∑ i, if mask i then s.fixedSelectorGradient ν μ ξ x (thinningScale t) i mask else 0) +
          s.fixedSelectorHeat ν μ ξ (A * A.transpose) x (thinningScale t) mask := by
    rw [s.heatShiftDerivative_eq_spatial_add_heat μ _
      (measurable_maskObservationSum ξ hξ mask) (mul_nonneg (Nat.cast_nonneg n) hδ)
      (maskObservationSum_bounded μ ξ hδ hbound mask) A x t]
    rw [s.integral_maskObservationSum_gradient_eq ν μ ξ hξ hδ hbound]
    rfl
  have hvalue (mask : Kane.Cube n) :
      s.heatShiftExpectation μ (maskObservationSum ξ mask) A x t =
        s.fixedSelectorValue ν μ ξ x (thinningScale t) mask := by
    unfold heatShiftExpectation fixedSelectorValue
    simp_rw [s.gaussianHeat_eq_convolution]
    rfl
  unfold selectorHeatDerivative
  simp_rw [hvalue, hsplit, mul_add]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  rw [← add_assoc]
  congr 1
  · congr 1
    · simpa only [selectorWeightDerivative, BernoulliSelectorAlgebra.massDerivative,
        BernoulliSelectorAlgebra.coordinateMassDerivative, BernoulliSelectorAlgebra.weightExcept]
        using BernoulliSelectorAlgebra.mass_derivative_regroup (thinningProbability t)
          ((t - 3) / (1 + t) ^ 3) (s.fixedSelectorValue ν μ ξ x (thinningScale t))
    · exact BernoulliSelectorAlgebra.retained_amplitude_regroup _ _

/-- The actual derivative of the one-observation translation operator with
the convolution held fixed. -/
noncomputable def observationTranslationDerivative
    (ν : Measure (Vector p)) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ((t - 3) / (1 + t) ^ 3) *
      (s.translatedConvolution ν μ ξ x (thinningScale t) - s.convolution ν x) +
    thinningProbability t * (∫ ω, ∑ j, ξ ω j *
      s.convolutionFirstDerivative ν (line x (ξ ω) (thinningScale t)) j ∂μ)

theorem integrable_translatedConvolution_base
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) (a : ℝ) :
    Integrable (fun ω => s.translatedConvolution ν μ ξ (W ω) a) μ := by
  let f : Ω × Ω → ℝ := fun z => s.convolution ν (W z.1 + a • ξ z.2)
  have hm : Measurable f := by
    apply (s.continuous_convolution ν).measurable.comp
    exact (hW.comp measurable_fst).add (measurable_const.smul (hξ.comp measurable_snd))
  have hi : Integrable f (μ.prod μ) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun _ => s.norm_convolution_le_one ν _))
  exact hi.integral_prod_left

theorem norm_convolutionGradient_le
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (x y : Vector p) {δ : ℝ} (hδ : 0 ≤ δ) (hy : ‖y‖ ≤ δ) :
    ‖∑ j, y j * s.convolutionFirstDerivative ν x j‖ ≤
      (p : ℝ) * (δ * (1 / s.bandwidth)) := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _j : Fin p, δ * (1 / s.bandwidth) := by
      apply Finset.sum_le_sum
      intro j _
      rw [norm_mul]
      exact mul_le_mul ((norm_le_pi_norm y j).trans hy)
        (s.norm_convolutionFirstDerivative_le ν x j) (norm_nonneg _) hδ
    _ = _ := by simp

theorem integrable_observationGradient_base
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (a : ℝ) :
    Integrable (fun ω => ∫ ω', ∑ j, ξ ω' j *
      s.convolutionFirstDerivative ν (line (W ω) (ξ ω') a) j ∂μ) μ := by
  let f : Ω × Ω → ℝ := fun z => ∑ j, ξ z.2 j *
    s.convolutionFirstDerivative ν (W z.1 + a • ξ z.2) j
  have hpoint : Measurable (fun z : Ω × Ω => W z.1 + a • ξ z.2) :=
    (hW.comp measurable_fst).add (measurable_const.smul (hξ.comp measurable_snd))
  have hm : Measurable f := by
    exact Finset.measurable_sum _ (fun j _ =>
      (((measurable_pi_apply j).comp hξ).comp measurable_snd).mul
        ((s.continuous_convolutionFirstDerivative ν j).measurable.comp hpoint))
  have hi : Integrable f (μ.prod μ) := by
    apply (integrable_const ((p : ℝ) * (δ * (1 / s.bandwidth)))).mono'
      hm.aestronglyMeasurable
    apply (Measure.ae_prod_iff_ae_ae
      (measurableSet_le hm.norm measurable_const)).mpr
    exact ae_of_all _ (fun ω => hbound.mono (fun ω' hω' =>
      s.norm_convolutionGradient_le ν _ _ hδ hω'))
  exact hi.integral_prod_left

theorem integrable_observationTranslationDerivative_base
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ W : Ω → Vector p)
    (hξ : Measurable ξ) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (t : ℝ) :
    Integrable (fun ω => s.observationTranslationDerivative ν μ ξ (W ω) t) μ := by
  have htr := s.integrable_translatedConvolution_base ν μ ξ W hξ hW (thinningScale t)
  have hf := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolution ν) _ (fun y => s.norm_convolution_le_one ν y)
  have hg := s.integrable_observationGradient_base ν μ ξ W hξ hW hδ hbound (thinningScale t)
  exact ((htr.sub hf).const_mul _).add (hg.const_mul _)

set_option maxHeartbeats 1000000 in
theorem fixedSelectorGradient_force_true_eq_double
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (mask : Kane.Cube n) (i : Fin n) (x : Vector p) (a : ℝ) :
    s.fixedSelectorGradient ν μ ξ x a i (Function.update mask i true) =
      ∫ ω, ∫ ω', ∑ j, ξ i ω' j * s.convolutionFirstDerivative ν
        (line (x + a • maskObservationSum ξ (Function.update mask i false) ω)
          (ξ i ω') a) j ∂μ ∂μ := by
  let V := maskObservationSum ξ (Function.update mask i false)
  let f : Vector p × Vector p → ℝ := fun z =>
    ∑ j, z.1 j * s.convolutionFirstDerivative ν (x + a • z.2 + a • z.1) j
  have hV := measurable_maskObservationSum ξ hξ (Function.update mask i false)
  have hf : Measurable f := by
    apply Finset.measurable_sum
    intro j _
    apply Measurable.mul
    · exact (measurable_pi_apply j).comp measurable_fst
    · apply (s.continuous_convolutionFirstDerivative ν j).measurable.comp
      fun_prop
  have hfi : Integrable f ((μ.map (ξ i)).prod (μ.map V)) := by
    apply integrable_pair_of_bounded_first μ (ξ i) V (hξ i) hV (hbound i) f hf
      (C := (p : ℝ) * (δ * (1 / s.bandwidth)))
    intro u v hu
    change ‖∑ j, u j * s.convolutionFirstDerivative ν (x + a • v + a • u) j‖ ≤ _
    exact s.norm_convolutionGradient_le ν _ u hδ hu
  have h := integral_indep_pair_eq_double μ (ξ i) V (hξ i) hV
    (indepFun_maskObservationSum_leaveOne μ ξ hξ hind mask i) f hf hfi
  calc
    _ = ∫ ω, f (ξ i ω, V ω) ∂μ := by
      apply integral_congr_ae
      refine ae_of_all _ (fun ω => ?_)
      change (∑ j, ξ i ω j * s.convolutionFirstDerivative ν
        (x + a • maskObservationSum ξ (Function.update mask i true) ω) j) = _
      dsimp only [f, V]
      rw [maskObservationSum_update_add ξ mask i true ω]
      simp only [Bool.true_eq, ↓reduceIte, smul_add, add_assoc]
    _ = _ := h

/-- The forced-selector terms are precisely the expectation of the actual
one-observation derivative at the independent leave-one-out point. -/
theorem forced_increment_eq_integral_observationTranslationDerivative
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (mask : Kane.Cube n) (i : Fin n) (x : Vector p) (t : ℝ) :
    ((t - 3) / (1 + t) ^ 3) *
        (s.fixedSelectorValue ν μ ξ x (thinningScale t) (Function.update mask i true) -
          s.fixedSelectorValue ν μ ξ x (thinningScale t) (Function.update mask i false)) +
      thinningProbability t *
        s.fixedSelectorGradient ν μ ξ x (thinningScale t) i (Function.update mask i true) =
      ∫ ω, s.observationTranslationDerivative ν μ (ξ i)
        (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω) t ∂μ := by
  let W := fun ω => x + thinningScale t •
    maskObservationSum ξ (Function.update mask i false) ω
  have hW : Measurable W := measurable_const.add
    (measurable_const.smul (measurable_maskObservationSum ξ hξ (Function.update mask i false)))
  have htr := s.integrable_translatedConvolution_base ν μ (ξ i) W (hξ i) hW (thinningScale t)
  have hf := integrable_bounded_test_comp μ W hW _
    (s.continuous_convolution ν) _ (fun y => s.norm_convolution_le_one ν y)
  have hg := s.integrable_observationGradient_base ν μ (ξ i) W (hξ i) hW hδ (hbound i)
    (thinningScale t)
  have htrue : s.fixedSelectorValue ν μ ξ x (thinningScale t) (Function.update mask i true) =
      ∫ ω, s.translatedConvolution ν μ (ξ i) (W ω) (thinningScale t) ∂μ := by
    exact integral_mask_force_true_eq_double μ ξ hξ hind hbound mask i (thinningScale t) x
      _ (s.continuous_convolution ν) _ (fun y => s.norm_convolution_le_one ν y)
  rw [htrue, s.fixedSelectorGradient_force_true_eq_double ν μ ξ hξ hind hδ hbound]
  unfold observationTranslationDerivative
  rw [integral_add (f := fun ω => ((t - 3) / (1 + t) ^ 3) *
      (s.translatedConvolution ν μ (ξ i) (W ω) (thinningScale t) - s.convolution ν (W ω)))
    (g := fun ω => thinningProbability t * (∫ ω', ∑ j, ξ i ω' j *
      s.convolutionFirstDerivative ν (line (W ω) (ξ i ω') (thinningScale t)) j ∂μ))
    ((htr.sub hf).const_mul _) (hg.const_mul _), integral_const_mul,
    integral_const_mul, integral_sub htr hf]
  rfl

theorem observationTranslationDerivative_eq_taylor
    (ν : Measure (Vector p)) {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    s.observationTranslationDerivative ν μ ξ x t =
      -(s.observationSecondTerm ν μ ξ x) / 2 -
        t / 3 * s.observationThirdTerm ν μ ξ x +
        s.oneObservationTaylorResidual ν μ ξ x t := by
  unfold observationTranslationDerivative oneObservationTaylorResidual
  have hn : 1 + t ≠ 0 := by linarith
  unfold thinningProbability thinningScale
  field_simp [hn]
  ring

end FaceSmoother

end RectangleCLT
