import RectangleCLT.BernoulliComparison
import RectangleCLT.InterpolationLaw

/-!
# Differentiation of the actual Bernoulli--Gaussian path

The path is represented by its finite independent-selector mixture. Gaussian
and bounded-observation differentiation is justified under the actual integrals.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology

universe u

namespace RectangleCLT

/-- Reassemble a Boolean mask from one coordinate and its complement. -/
def joinMask {n : ℕ} (i : Fin n) (b : Bool) (r : {j : Fin n // j ≠ i} → Bool) :
    Kane.Cube n := (Equiv.funSplitAt i Bool).symm (b, r)

@[simp] theorem joinMask_self {n : ℕ} (i : Fin n) (b : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) : joinMask i b r i = b := by
  simp [joinMask, Equiv.funSplitAt, Equiv.piSplitAt]

theorem joinMask_ne {n : ℕ} (i : Fin n) (b : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) (j : Fin n) (hj : j ≠ i) :
    joinMask i b r j = r ⟨j, hj⟩ := by
  simp [joinMask, Equiv.funSplitAt, Equiv.piSplitAt, hj]

theorem update_joinMask {n : ℕ} (i : Fin n) (b c : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    Function.update (joinMask i b r) i c = joinMask i c r := by
  ext j
  by_cases hj : j = i
  · subst j
    simp
  · simp [Function.update_of_ne hj, joinMask_ne i b r j hj, joinMask_ne i c r j hj]

theorem sum_cube_split {n : ℕ} (i : Fin n) (f : Kane.Cube n → ℝ) :
    (∑ mask, f mask) = ∑ r : {j : Fin n // j ≠ i} → Bool,
      (f (joinMask i false r) + f (joinMask i true r)) := by
  classical
  calc
    _ = ∑ z : Bool × ({j : Fin n // j ≠ i} → Bool),
        f ((Equiv.funSplitAt i Bool).symm z) :=
      ((Equiv.funSplitAt i Bool).symm.sum_comp f).symm
    _ = _ := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro r _
      simp [joinMask, add_comm]

def selectorWeightExcept {n : ℕ} (q : ℝ) (mask : Kane.Cube n) (i : Fin n) : ℝ :=
  ∏ j ∈ Finset.univ.erase i, if mask j then q else 1 - q

theorem maskWeight_eq_coordinate_mul_except {n : ℕ} (q : ℝ)
    (mask : Kane.Cube n) (i : Fin n) :
    Kane.maskWeight q mask = (if mask i then q else 1 - q) *
      selectorWeightExcept q mask i := by
  exact (Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ i)).symm

theorem selectorWeightExcept_join {n : ℕ} (q : ℝ) (i : Fin n) (b c : Bool)
    (r : {j : Fin n // j ≠ i} → Bool) :
    selectorWeightExcept q (joinMask i b r) i =
      selectorWeightExcept q (joinMask i c r) i := by
  apply Finset.prod_congr rfl
  intro j hj
  have hji := (Finset.mem_erase.mp hj).1
  rw [joinMask_ne i b r j hji, joinMask_ne i c r j hji]

/-- Derivative of the actual independent Bernoulli mask mass. -/
def selectorWeightDerivative {n : ℕ} (q q' : ℝ) (mask : Kane.Cube n) : ℝ :=
  ∑ i, (∏ j ∈ Finset.univ.erase i, if mask j then q else 1 - q) *
    (if mask i then q' else -q')

theorem hasDerivAt_maskWeight_thinning {n : ℕ} (mask : Kane.Cube n)
    {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun r => Kane.maskWeight (thinningProbability r) mask)
      (selectorWeightDerivative (thinningProbability t) ((t - 3) / (1 + t) ^ 3) mask) t := by
  have h := HasDerivAt.finset_prod (u := Finset.univ)
    (f := fun i r => if mask i then thinningProbability r else 1 - thinningProbability r)
    (f' := fun i => if mask i then (t - 3) / (1 + t) ^ 3 else -((t - 3) / (1 + t) ^ 3))
    (fun i _ => by
      cases hi : mask i
      · simpa only [hi, Bool.false_eq_true, ↓reduceIte] using
          (hasDerivAt_thinningProbability ht).const_sub 1
      · simpa only [hi, ↓reduceIte] using hasDerivAt_thinningProbability ht)
  simpa only [Kane.maskWeight, selectorWeightDerivative, smul_eq_mul] using h

/-- Sum of the original observations selected by a fixed mask, without scaling. -/
def maskObservationSum {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (mask : Kane.Cube n) (ω : Ω) : Vector p :=
  ∑ i, if mask i then ξ i ω else 0

theorem measurable_maskObservationSum {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (mask : Kane.Cube n) :
    Measurable (maskObservationSum ξ mask) := by
  apply Finset.measurable_sum
  intro i _
  cases hi : mask i
  · simpa only [hi, Bool.false_eq_true, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : Ω => (0 : Vector p)))
  · simpa only [hi, ↓reduceIte] using hξ i

theorem maskObservationSum_bounded {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) (mask : Kane.Cube n) :
    ∀ᵐ ω ∂μ, ‖maskObservationSum ξ mask ω‖ ≤ (n : ℝ) * δ := by
  have hall : ∀ᵐ ω ∂μ, ∀ i, ‖ξ i ω‖ ≤ δ := (ae_all_iff).mpr hbound
  filter_upwards [hall] with ω hω
  apply (norm_sum_le _ _).trans
  calc
    (∑ i : Fin n, ‖if mask i then ξ i ω else 0‖) ≤ ∑ _i : Fin n, δ := by
      apply Finset.sum_le_sum
      intro i _
      cases hi : mask i
      · simpa only [hi, Bool.false_eq_true, ↓reduceIte, norm_zero] using hδ
      · simpa only [hi, ↓reduceIte] using hω i
    _ = _ := by simp

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem continuous_convolutionSecondDerivative
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (j k : Fin p) :
    Continuous (fun x => s.convolutionSecondDerivative ν x j k) := by
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν _
    (s.continuous_secondDerivative j k) _ (fun y => s.norm_secondDerivative_le y j k)

/-- A moving bounded observation, independently smoothed by the heat law. -/
noncomputable def heatShiftExpectation {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ζ : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) : ℝ :=
  ∫ ω, s.gaussianHeat A (x + thinningScale t • ζ ω) t ∂μ

noncomputable def heatShiftDerivative {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ζ : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) : ℝ :=
  ∫ ω, (∑ j, ζ ω j * s.convolutionFirstDerivative
      (gaussianLaw (Real.sqrt t • A)) (x + thinningScale t • ζ ω) j) +
    (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
      s.convolutionSecondDerivative
        (gaussianLaw (Real.sqrt t • A)) (x + thinningScale t • ζ ω) j k ∂μ

/-- Differentiation under both actual probability laws. The bound used for
domination is uniform in time after the Gaussian heat identity is applied. -/
theorem hasDerivAt_heatShiftExpectation
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ζ : Ω → Vector p) (hζ : Measurable ζ) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, ‖ζ ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (s.heatShiftExpectation μ ζ A x)
      (s.heatShiftDerivative μ ζ A x t) t := by
  let K := (p : ℝ) * (δ * (1 / s.bandwidth)) +
    (1 / 2 : ℝ) * ∑ j, ∑ k, |(A * A.transpose) j k| * (3 / s.bandwidth ^ 2)
  have hpoint (r : ℝ) : Measurable (fun ω => x + thinningScale r • ζ ω) := by
    have hsm : Measurable (fun ω => thinningScale r • ζ ω) := by
      simpa only [Pi.smul_apply] using hζ.const_smul (thinningScale r)
    exact measurable_const.add hsm
  have hF (r : ℝ) : AEStronglyMeasurable
      (fun ω => s.gaussianHeat A (x + thinningScale r • ζ ω) r) μ := by
    simp_rw [s.gaussianHeat_eq_convolution]
    exact ((s.continuous_convolution (gaussianLaw (Real.sqrt r • A))).measurable.comp
      (hpoint r)).aestronglyMeasurable
  have hD (r : ℝ) : AEStronglyMeasurable
      (fun ω => (∑ j, ζ ω j * s.convolutionFirstDerivative
          (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j) +
        (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
          s.convolutionSecondDerivative
            (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j k) μ := by
    apply Measurable.aestronglyMeasurable
    apply Measurable.add
    · exact Finset.measurable_sum _ (fun j _ =>
        ((measurable_pi_apply j).comp hζ).mul
          (((s.continuous_convolutionFirstDerivative
            (gaussianLaw (Real.sqrt r • A)) j).measurable).comp (hpoint r)))
    · apply Measurable.const_mul
      exact Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun k _ =>
        ((((s.continuous_convolutionSecondDerivative
          (gaussianLaw (Real.sqrt r • A)) j k).measurable).comp (hpoint r)).const_mul _)))
  have hnorm (ω : Ω) (hω : ‖ζ ω‖ ≤ δ) (r : ℝ) :
      ‖(∑ j, ζ ω j * s.convolutionFirstDerivative
          (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j) +
        (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
          s.convolutionSecondDerivative
            (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j k‖ ≤ K := by
    apply (norm_add_le _ _).trans
    apply add_le_add
    · apply (norm_sum_le _ _).trans
      calc
        _ ≤ ∑ _j : Fin p, δ * (1 / s.bandwidth) := by
          apply Finset.sum_le_sum
          intro j _
          rw [norm_mul]
          exact mul_le_mul ((norm_le_pi_norm (ζ ω) j).trans hω)
            (s.norm_convolutionFirstDerivative_le _ _ j) (norm_nonneg _ ) hδ
        _ = _ := by simp
    · rw [norm_mul, Real.norm_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      apply mul_le_mul_of_nonneg_left _ (by norm_num : (0 : ℝ) ≤ 1 / 2)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro j _
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_mul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (s.norm_convolutionSecondDerivative_le _ _ j k) (abs_nonneg _)
  have hpos {r : ℝ} (hr : r ∈ Metric.ball t (t / 2)) : 0 < r := by
    have hh : |r - t| < t / 2 := by simpa only [Metric.mem_ball, Real.dist_eq] using hr
    have := (abs_lt.mp hh).1
    linarith
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ : Ω => K) (ε := t / 2)
    (F := fun r ω => s.gaussianHeat A (x + thinningScale r • ζ ω) r)
    (F' := fun r ω => (∑ j, ζ ω j * s.convolutionFirstDerivative
        (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j) +
      (1 / 2 : ℝ) * ∑ j, ∑ k, (A * A.transpose) j k *
        s.convolutionSecondDerivative
          (gaussianLaw (Real.sqrt r • A)) (x + thinningScale r • ζ ω) j k)
    (x₀ := t) (by positivity)
    (Filter.Eventually.of_forall hF)
    ((integrable_const (1 : ℝ)).mono' (hF t) (ae_of_all _ (fun ω => by
      change ‖s.gaussianHeat A (x + thinningScale t • ζ ω) t‖ ≤ 1
      rw [s.gaussianHeat_eq_convolution]
      exact s.norm_convolution_le_one _ _))) (hD t)
    (hbound.mono (fun ω hω r _ => hnorm ω hω r)) (integrable_const K)
    (ae_of_all _ (fun ω r hr => by
      have h := s.hasDerivAt_gaussianHeat_line A (x + ζ ω) (ζ ω) (hpos hr)
      have heq (a : ℝ) : line (x + ζ ω) (ζ ω) a = x + thinningScale a • ζ ω := by
        ext j
        simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul, thinningScale]
        ring
      simpa only [heq] using h))
  exact hd.2

/-- The finite-selector expression for the complete interpolation expectation. -/
noncomputable def selectorHeatExpectation {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask *
    s.heatShiftExpectation μ (maskObservationSum ξ mask) A x t

/-- A computed derivative, with no comparison estimate included as a premise. -/
noncomputable def selectorHeatDerivative {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (t : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n,
    (selectorWeightDerivative (thinningProbability t) ((t - 3) / (1 + t) ^ 3) mask *
        s.heatShiftExpectation μ (maskObservationSum ξ mask) A x t +
      Kane.maskWeight (thinningProbability t) mask *
        s.heatShiftDerivative μ (maskObservationSum ξ mask) A x t)

/-- Differentiate the actual finite selector law and the actual Gaussian
integral. This identity does not require independence between observations. -/
theorem hasDerivAt_selectorHeatExpectation
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (s.selectorHeatExpectation μ ξ A x)
      (s.selectorHeatDerivative μ ξ A x t) t := by
  unfold selectorHeatExpectation selectorHeatDerivative
  apply HasDerivAt.sum
  intro mask _
  exact (hasDerivAt_maskWeight_thinning mask ht.le).mul
    (s.hasDerivAt_heatShiftExpectation μ (maskObservationSum ξ mask)
      (measurable_maskObservationSum ξ hξ mask) (mul_nonneg (Nat.cast_nonneg _) hδ)
      (maskObservationSum_bounded μ ξ hδ hbound mask) A x ht)

/-- The differentiated finite sum is exactly the expectation under the
concrete interpolation probability law. -/
theorem integral_interpolationLaw_eq_selectorHeatExpectation
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ z, s.F z ∂interpolationLaw μ ξ A t) =
      s.selectorHeatExpectation μ ξ A 0 t := by
  let ν := gaussianLaw (Real.sqrt t • A)
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have hm : Measurable (fun a : (Fin n → Vector p) × Vector p =>
      s.F (interpolationSum a)) :=
    s.continuous_F.measurable.comp (measurable_interpolationSum p n)
  have hi : Integrable (fun a : (Fin n → Vector p) × Vector p =>
      s.F (interpolationSum a)) ((bernoulliArrayLaw μ ξ t).prod ν) :=
    (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
      (ae_of_all _ (fun a => s.norm_F_le_one _))
  unfold interpolationLaw
  rw [integral_map (measurable_interpolationSum p n).aemeasurable
    s.continuous_F.measurable.aestronglyMeasurable]
  change (∫ a, s.F (interpolationSum a) ∂(bernoulliArrayLaw μ ξ t).prod ν) = _
  rw [integral_prod _ hi]
  change (∫ b, s.convolution ν (arraySum b) ∂bernoulliArrayLaw μ ξ t) = _
  have hmg : Measurable (fun b : Fin n → Vector p => s.convolution ν (arraySum b)) :=
    (s.continuous_convolution ν).measurable.comp (measurable_arraySum p n)
  have hig (mask : Kane.Cube n) : Integrable
      (fun b : Fin n → Vector p => s.convolution ν (arraySum b))
      (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact (integrable_const (1 : ℝ)).mono' hmg.aestronglyMeasurable
      (ae_of_all _ (fun b => s.norm_convolution_le_one ν _))
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1)
    (thinningProbability_le_one ht) _ hig]
  unfold selectorHeatExpectation
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable
    hmg.aestronglyMeasurable]
  unfold heatShiftExpectation
  apply integral_congr_ae
  refine ae_of_all _ (fun ω => ?_)
  change s.convolution ν (arraySum (retainedArray ξ t mask ω)) =
    s.gaussianHeat A (0 + thinningScale t • maskObservationSum ξ mask ω) t
  rw [s.gaussianHeat_eq_convolution]
  have heq : arraySum (retainedArray ξ t mask ω) =
      thinningScale t • maskObservationSum ξ mask ω := by
    unfold arraySum maskObservationSum
    rw [Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    cases hi : mask i <;> simp [retainedArray, hi]
  simp only [zero_add, heq]
  rfl

/-- The original interpolation expectation has the explicitly computed
derivative at every interior time. -/
theorem hasDerivAt_integral_interpolationLaw
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (fun r => ∫ z, s.F z ∂interpolationLaw μ ξ A r)
      (s.selectorHeatDerivative μ ξ A 0 t) t := by
  apply (s.hasDerivAt_selectorHeatExpectation μ ξ hξ hδ hbound A 0 ht).congr_of_eventuallyEq
  have hnear : Set.Ioo (0 : ℝ) 1 ∈ 𝓝 t := isOpen_Ioo.mem_nhds ⟨ht, ht1⟩
  filter_upwards [hnear] with r hr
  exact s.integral_interpolationLaw_eq_selectorHeatExpectation μ ξ hξ A hr.1.le hr.2.le

end FaceSmoother
end RectangleCLT
