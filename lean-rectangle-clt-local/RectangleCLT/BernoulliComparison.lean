import RectangleCLT.GaussianHeat
import RectangleCLT.TranslationTaylor
import RectangleCLT.Interpolation
import RectangleCLT.Normalization
import RectangleCLT.RectangleConcentration

/-!
# Actual one-summand translation differentiation on the Bernoulli path

Translation expectations use concrete probability measures. The Gaussian
heat identity is proved in `GaussianHeat`; the translation derivative below
holds a probability convolution fixed while the amplitude and retention
probability vary. Subsequent Taylor estimates preserve the signed moment
coefficients before taking absolute values.
-/

open MeasureTheory
open ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

/-- The actual thinned-array law is a product of its one-observation mixture
laws whenever the original whole-vector observations are independent. -/
theorem bernoulliArrayLaw_eq_coordinate_product
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
    bernoulliArrayLaw μ ξ t =
      coordinateReplacementLaw μ (fun i ω => thinningScale t • ξ i ω) 0
        (thinningProbability t) := by
  have hscaled (i : Fin n) : Measurable (fun ω => thinningScale t • ξ i ω) :=
    by simpa only [Pi.smul_apply] using (hξ i).const_smul (thinningScale t)
  have hindscaled : iIndepFun (fun i ω => thinningScale t • ξ i ω) μ :=
    hind.comp (fun _ y => thinningScale t • y)
      (fun _ => measurable_const.smul measurable_id)
  exact bernoulliReplacement_eq_product μ _ hscaled hindscaled 0 _
    (thinningProbability_nonneg htone) (thinningProbability_le_one ht)

/-- Independence holds for the canonical observations under the actual
finite Bernoulli mixture, rather than merely for its formal coefficients. -/
theorem bernoulliArrayLaw_independent
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) :
    iIndepFun (fun i (b : Fin n → Vector p) => b i) (bernoulliArrayLaw μ ξ t) := by
  rw [bernoulliArrayLaw_eq_coordinate_product μ ξ hξ hind t ht htone]
  have hscaled (i : Fin n) : Measurable (fun ω => thinningScale t • ξ i ω) := by
    simpa only [Pi.smul_apply] using (hξ i).const_smul (thinningScale t)
  exact coordinateReplacement_independent μ _ hscaled 0 _
    (thinningProbability_nonneg htone) (thinningProbability_le_one ht)

/-- The actual thinned observations inherit the maximum-norm envelope `2δ`
throughout the interpolation interval. -/
theorem bernoulliArrayLaw_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {δ : ℝ} (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ)
    (t : ℝ) (ht : 0 ≤ t) (htone : t ≤ 1) (i : Fin n) :
    ∀ᵐ b ∂bernoulliArrayLaw μ ξ t, ‖b i‖ ≤ 2 * δ := by
  have hset : MeasurableSet {b : Fin n → Vector p | ‖b i‖ ≤ 2 * δ} :=
    measurableSet_le (measurable_pi_apply i).norm measurable_const
  have hmap (mask : Kane.Cube n) :
      ∀ᵐ b ∂μ.map (retainedArray ξ t mask), ‖b i‖ ≤ 2 * δ := by
    apply (ae_map_iff (measurable_retainedArray ξ hξ t mask).aemeasurable hset).mpr
    filter_upwards [hbound i] with ω hω
    by_cases hi : mask i = true
    · simp only [retainedArray, hi, ↓reduceIte, norm_smul, Real.norm_eq_abs,
        abs_of_pos (thinningScale_pos ht)]
      exact mul_le_mul (thinningScale_le_two htone) hω (norm_nonneg _) (by norm_num)
    · simp only [retainedArray, hi, Bool.false_eq_true, ↓reduceIte, norm_zero]
      positivity
  rw [ae_iff]
  unfold bernoulliArrayLaw bernoulliMixtureLaw
  rw [Measure.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro mask _
  rw [Measure.smul_apply, smul_eq_mul, (ae_iff.mp (hmap mask)), mul_zero]

/-- A pointwise fourth-product bound retaining the coordinate moments rather
than replacing them by a moment of the maximum norm. -/
theorem abs_four_product_le_fourth_mean (a b c d : ℝ) :
    |a * b * c * d| ≤ (a ^ 4 + b ^ 4 + c ^ 4 + d ^ 4) / 4 := by
  have h₁ : 2 * (a * b) ^ 2 ≤ a ^ 4 + b ^ 4 := by
    nlinarith only [sq_nonneg (a ^ 2 - b ^ 2)]
  have h₂ : 2 * (c * d) ^ 2 ≤ c ^ 4 + d ^ 4 := by
    nlinarith only [sq_nonneg (c ^ 2 - d ^ 2)]
  have h₃ : 2 * |a * b * c * d| ≤ (a * b) ^ 2 + (c * d) ^ 2 := by
    calc
      _ = 2 * |a * b| * |c * d| := by simp only [abs_mul]; ring
      _ ≤ |a * b| ^ 2 + |c * d| ^ 2 := by nlinarith only [sq_nonneg (|a * b| - |c * d|)]
      _ = _ := by rw [sq_abs, sq_abs]
  nlinarith only [h₁, h₂, h₃]

theorem integral_abs_four_product_le_fourth_mean
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) (a b c d : Ω → ℝ)
    (hprod : Integrable (fun ω => a ω * b ω * c ω * d ω) μ)
    (ha : Integrable (fun ω => a ω ^ 4) μ) (hb : Integrable (fun ω => b ω ^ 4) μ)
    (hc : Integrable (fun ω => c ω ^ 4) μ) (hd : Integrable (fun ω => d ω ^ 4) μ) :
    (∫ ω, |a ω * b ω * c ω * d ω| ∂μ) ≤
      ((∫ ω, a ω ^ 4 ∂μ) + (∫ ω, b ω ^ 4 ∂μ) +
        (∫ ω, c ω ^ 4 ∂μ) + (∫ ω, d ω ^ 4 ∂μ)) / 4 := by
  have h := integral_mono_ae hprod.abs ((((ha.add hb).add hc).add hd).div_const 4)
    (ae_of_all _ (fun ω => abs_four_product_le_fourth_mean (a ω) (b ω) (c ω) (d ω)))
  change (∫ ω, |a ω * b ω * c ω * d ω| ∂μ) ≤
    (∫ ω, (a ω ^ 4 + b ω ^ 4 + c ω ^ 4 + d ω ^ 4) / 4 ∂μ) at h
  rw [integral_div,
    integral_add (f := fun ω => a ω ^ 4 + b ω ^ 4 + c ω ^ 4) (g := fun ω => d ω ^ 4)
      ((ha.add hb).add hc) hd,
    integral_add (f := fun ω => a ω ^ 4 + b ω ^ 4) (g := fun ω => c ω ^ 4)
      (ha.add hb) hc,
    integral_add ha hb] at h
  exact h

theorem coordinate_fourth_sum_le_gamma4 {Ω : Type u} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j : Fin p) :
    (∑ i, ∫ ω, (ξ i ω j) ^ 4 ∂μ) ≤ gamma4 μ ξ := by
  apply (Finset.le_fold_max _).mpr
  exact Or.inr ⟨j, Finset.mem_univ _, le_rfl⟩

/-- The total mixed fourth absolute moment is bounded by `gamma4` without
moving a maximum inside expectation and without a dimension factor. -/
theorem summed_abs_fourth_product_le_gamma4
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) (j k l m : Fin p) :
    (∑ i, ∫ ω, |ξ i ω j * ξ i ω k * ξ i ω l * ξ i ω m| ∂μ) ≤ gamma4 μ ξ := by
  have hcoord (i : Fin n) (a : Fin p) : ∀ᵐ ω ∂μ, |ξ i ω a| ≤ δ := by
    filter_upwards [hbound i] with ω hω
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ i ω) a).trans hω
  have hpow (i : Fin n) (a : Fin p) : Integrable (fun ω => ξ i ω a ^ 4) μ :=
    integrable_coordinate_pow_of_bounded hξ hcoord i a 4
  have hprod (i : Fin n) :
      Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l * ξ i ω m) μ := by
    apply (integrable_const (δ ^ 4)).mono'
      (((((measurable_pi_apply j).comp (hξ i)).mul
        ((measurable_pi_apply k).comp (hξ i))).mul
        ((measurable_pi_apply l).comp (hξ i))).mul
        ((measurable_pi_apply m).comp (hξ i))).aestronglyMeasurable
    filter_upwards [hcoord i j, hcoord i k, hcoord i l, hcoord i m] with ω hj hk hl hm
    simp only [Real.norm_eq_abs, abs_mul, Function.comp_apply]
    calc
      _ ≤ δ * δ * δ * δ := by gcongr
      _ = _ := by ring
  calc
    _ ≤ ∑ i, ((∫ ω, ξ i ω j ^ 4 ∂μ) + (∫ ω, ξ i ω k ^ 4 ∂μ) +
        (∫ ω, ξ i ω l ^ 4 ∂μ) + (∫ ω, ξ i ω m ^ 4 ∂μ)) / 4 := by
      apply Finset.sum_le_sum
      intro i _
      exact integral_abs_four_product_le_fourth_mean μ _ _ _ _
        (hprod i) (hpow i j) (hpow i k) (hpow i l) (hpow i m)
    _ = ((∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) + (∑ i, ∫ ω, ξ i ω k ^ 4 ∂μ) +
        (∑ i, ∫ ω, ξ i ω l ^ 4 ∂μ) + (∑ i, ∫ ω, ξ i ω m ^ 4 ∂μ)) / 4 := by
      simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ _ := by
      linarith only [coordinate_fourth_sum_le_gamma4 μ ξ j,
        coordinate_fourth_sum_le_gamma4 μ ξ k, coordinate_fourth_sum_le_gamma4 μ ξ l,
        coordinate_fourth_sum_le_gamma4 μ ξ m]

/-- Every finite coordinate monomial of a bounded measurable observation is
integrable. Repeated coordinates are permitted. -/
theorem integrable_bounded_coordinate_product
    {Ω : Type u} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Ω → Vector p)
    (hξ : Measurable ξ) {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (J : Fin r → Fin p) : Integrable (fun ω => ∏ a, ξ ω (J a)) μ := by
  apply (integrable_const (δ ^ r)).mono'
    (Finset.measurable_prod Finset.univ
      (fun a _ => (measurable_pi_apply (J a)).comp hξ)).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  have hcoord (a : Fin r) : |ξ ω (J a)| ≤ δ := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ ω) (J a)).trans hω
  have hprod : (∏ a : Fin r, |ξ ω (J a)|) ≤ ∏ _a : Fin r, δ :=
    Finset.prod_le_prod (fun a _ => abs_nonneg (ξ ω (J a))) (fun a _ => hcoord a)
  simpa only [Real.norm_eq_abs, Finset.abs_prod, Finset.prod_const, Function.comp_apply,
    Finset.card_univ, Fintype.card_fin] using
    hprod

theorem continuous_shiftIntegral_of_bounded {p : ℕ}
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (G : Vector p → ℝ) (hG : Continuous G) (C : ℝ)
    (hbound : ∀ x, ‖G x‖ ≤ C) : Continuous (shiftIntegral ν G) := by
  apply continuous_of_dominated (bound := fun _ => C)
  · intro x
    exact (hG.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  · intro x
    exact ae_of_all _ (fun z => hbound (x + z))
  · exact integrable_const C
  · exact ae_of_all _ (fun z => hG.comp (continuous_id.add continuous_const))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)
variable (ν : Measure (Vector p)) [IsProbabilityMeasure ν]

theorem continuous_convolution : Continuous (s.convolution ν) :=
  continuous_shiftIntegral_of_bounded ν s.F s.continuous_F 1 s.norm_F_le_one

theorem continuous_convolutionFirstDerivative (j : Fin p) :
    Continuous (fun x => s.convolutionFirstDerivative ν x j) := by
  simp_rw [s.convolutionFirstDerivative_eq_integral]
  exact continuous_shiftIntegral_of_bounded ν (fun x => s.coordinateDerivativeF x j)
    (s.continuous_firstDerivative j) (1 / s.bandwidth) (fun x => s.norm_firstDerivative_le x j)

private theorem F_line_derivative_eq_sum (x y : Vector p) (t : ℝ) :
    -(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y =
      ∑ j, y j * s.coordinateDerivativeF (line x y t) j := by
  rw [(s.weights (line x y t)).directionalMean_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [s.coordinateDerivativeF_eq]
  ring

/-- Actual directional differentiation commutes with probability convolution. -/
theorem hasDerivAt_convolution_line_sum (x y : Vector p) (t : ℝ) :
    HasDerivAt (fun r => s.convolution ν (line x y r))
      (∑ j, y j * s.convolutionFirstDerivative ν (line x y t) j) t := by
  have hFmeas (r : ℝ) : AEStronglyMeasurable
      (fun z : Vector p => s.F (line x y r + z)) ν :=
    (s.continuous_F.comp (continuous_const.add continuous_id)).aestronglyMeasurable
  have hdmeas : AEStronglyMeasurable
      (fun z : Vector p => -(s.F (line x y t + z) / s.bandwidth) *
        (s.weights (line x y t + z)).directionalMean y) ν := by
    have hshift : Continuous (fun z : Vector p => line x y t + z) :=
      continuous_const.add continuous_id
    apply Continuous.aestronglyMeasurable
    apply Continuous.mul
    · exact (((s.continuous_F.comp hshift).div_const _).neg)
    · rw [show (fun z : Vector p => (s.weights (line x y t + z)).directionalMean y) =
          (fun z => ∑ j, (s.weights (line x y t + z)).v j * y j) by
        funext z; exact (s.weights _).directionalMean_eq y]
      exact continuous_finset_sum _ (fun j _ =>
        ((s.continuous_v j).comp hshift).mul continuous_const)
  have hi := s.integrable_F_shift ν (line x y t)
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (bound := fun _ : Vector p => ‖y‖ / s.bandwidth) (ε := 1)
    (F := fun r z => s.F (line x y r + z))
    (F' := fun r z => -(s.F (line x y r + z) / s.bandwidth) *
      (s.weights (line x y r + z)).directionalMean y)
    (x₀ := t) (by norm_num)
    (Filter.Eventually.of_forall hFmeas) hi hdmeas
    (ae_of_all _ (fun z r _ => by
      simpa only [Real.norm_eq_abs, line_add_shift] using
        s.abs_F_line_derivative_le (x + z) y r))
    (integrable_const _) (ae_of_all _ (fun z r _ => by
      simpa only [line_add_shift] using s.hasDerivAt_F_line (x + z) y r))
  have heq :
      (∫ z, -(s.F (line x y t + z) / s.bandwidth) *
        (s.weights (line x y t + z)).directionalMean y ∂ν) =
      ∑ j, y j * s.convolutionFirstDerivative ν (line x y t) j := by
    have hpoint (z : Vector p) :
        -(s.F (line x y t + z) / s.bandwidth) *
          (s.weights (line x y t + z)).directionalMean y =
        ∑ j, y j * s.coordinateDerivativeF (line x y t + z) j := by
      simpa only [line_zero] using s.F_line_derivative_eq_sum (line x y t + z) y 0
    simp_rw [hpoint]
    rw [integral_finset_sum Finset.univ (fun j _ =>
      (s.integrable_firstDerivative_shift ν (line x y t) j).const_mul (y j))]
    simp_rw [integral_const_mul, s.convolutionFirstDerivative_eq_integral]
  rw [heq] at hd
  exact hd.2

theorem norm_convolution_le_one (x : Vector p) : ‖s.convolution ν x‖ ≤ 1 :=
  norm_shiftIntegral_le ν s.F 1 s.norm_F_le_one x

private theorem abs_convolution_directional_derivative_le
    (x y : Vector p) {δ : ℝ} (hy : ‖y‖ ≤ δ) :
    |∑ j, y j * s.convolutionFirstDerivative ν x j| ≤
      (p : ℝ) * δ / s.bandwidth := by
  calc
    _ ≤ ∑ j, |y j * s.convolutionFirstDerivative ν x j| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin p, δ * (1 / s.bandwidth) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul]
      have hcoord : |y j| ≤ δ := by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm y j).trans hy
      exact mul_le_mul
        hcoord
        (by simpa only [Real.norm_eq_abs] using s.norm_convolutionFirstDerivative_le ν x j)
        (abs_nonneg _) (le_trans (norm_nonneg _) hy)
    _ = _ := by simp; ring

/-- The translation integral before mixing the retained and zero summand. -/
noncomputable def translatedConvolution {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (a : ℝ) : ℝ :=
  ∫ ω, s.convolution ν (line x (ξ ω) a) ∂μ

/-- Actual amplitude differentiation with all analytic assumptions discharged
by measurable bounded observations and the checked convolution derivatives. -/
theorem hasDerivAt_translatedConvolution {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → Vector p)
    (hξ : Measurable ξ) {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) :
    HasDerivAt (s.translatedConvolution ν μ ξ x)
      (∫ ω, ∑ j, ξ ω j * s.convolutionFirstDerivative ν (line x (ξ ω) a) j ∂μ) a := by
  have hline (r : ℝ) : Measurable (fun ω => line x (ξ ω) r) := by
    change Measurable (fun ω => x + r • ξ ω)
    exact measurable_const.add (measurable_const.smul hξ)
  have hmeas (r : ℝ) : AEStronglyMeasurable
      (fun ω => s.convolution ν (line x (ξ ω) r)) μ :=
    ((s.continuous_convolution ν).measurable.comp (hline r)).aestronglyMeasurable
  have hDmeas : AEStronglyMeasurable
      (fun ω => ∑ j, ξ ω j * s.convolutionFirstDerivative ν (line x (ξ ω) a) j) μ := by
    apply Measurable.aestronglyMeasurable
    exact Finset.measurable_sum Finset.univ (fun j _ =>
      ((measurable_pi_apply j).comp hξ).mul
        (((s.continuous_convolutionFirstDerivative ν j).measurable).comp (hline a)))
  have hi : Integrable (fun ω => s.convolution ν (line x (ξ ω) a)) μ :=
    (integrable_const (1 : ℝ)).mono' (hmeas a)
      (ae_of_all _ (fun ω => s.norm_convolution_le_one ν _))
  have hd := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := μ) (bound := fun _ : Ω => (p : ℝ) * δ / s.bandwidth) (ε := 1)
    (F := fun r ω => s.convolution ν (line x (ξ ω) r))
    (F' := fun r ω => ∑ j, ξ ω j *
      s.convolutionFirstDerivative ν (line x (ξ ω) r) j)
    (x₀ := a) (by norm_num) (Filter.Eventually.of_forall hmeas) hi hDmeas
    (hbound.mono (fun ω hω r _ => by
      simpa only [Real.norm_eq_abs] using
        s.abs_convolution_directional_derivative_le ν (line x (ξ ω) r) (ξ ω) hω))
    (integrable_const _) (ae_of_all _ (fun ω r _ => s.hasDerivAt_convolution_line_sum ν x (ξ ω) r))
  exact hd.2

/-- The actual one-summand Bernoulli translation operator, holding the
convolution kernel fixed while its retention probability and amplitude vary. -/
noncomputable def bernoulliTranslation {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  (1 - thinningProbability t) * s.convolution ν x +
    thinningProbability t * s.translatedConvolution ν μ ξ x (thinningScale t)

theorem hasDerivAt_bernoulliTranslation {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Ω → Vector p)
    (hξ : Measurable ξ) {δ : ℝ} (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (s.bernoulliTranslation ν μ ξ x)
      (((t - 3) / (1 + t) ^ 3) *
          (s.translatedConvolution ν μ ξ x (thinningScale t) - s.convolution ν x) +
        thinningProbability t * ∫ ω, ∑ j, ξ ω j *
          s.convolutionFirstDerivative ν (line x (ξ ω) (thinningScale t)) j ∂μ) t := by
  have hq := hasDerivAt_thinningProbability ht
  have htrans := (s.hasDerivAt_translatedConvolution ν μ ξ hξ hbound x
    (thinningScale t)).comp t (hasDerivAt_thinningScale t)
  have hd := (((hasDerivAt_const t (1 : ℝ)).sub hq).mul_const
    (s.convolution ν x)).add (hq.mul htrans)
  convert hd using 1
  dsimp
  ring

omit [IsProbabilityMeasure ν] in
theorem convolutionTranslationD1_smul (x y : Vector p) (a : ℝ) :
    s.convolutionTranslationD1 ν x (a • y) = a * s.convolutionTranslationD1 ν x y := by
  unfold convolutionTranslationD1
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

omit [IsProbabilityMeasure ν] in
theorem convolutionTranslationD2_smul (x y : Vector p) (a : ℝ) :
    s.convolutionTranslationD2 ν x (a • y) = a ^ 2 * s.convolutionTranslationD2 ν x y := by
  unfold convolutionTranslationD2
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

omit [IsProbabilityMeasure ν] in
theorem convolutionTranslationD3_smul (x y : Vector p) (a : ℝ) :
    s.convolutionTranslationD3 ν x (a • y) = a ^ 3 * s.convolutionTranslationD3 ν x y := by
  unfold convolutionTranslationD3
  simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  apply Finset.sum_congr rfl
  intro l _
  ring

omit [IsProbabilityMeasure ν] in
theorem integrable_convolutionTranslationD1_observation
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) :
    Integrable (fun ω => s.convolutionTranslationD1 ν x (ξ ω)) μ := by
  unfold convolutionTranslationD1
  apply integrable_finset_sum
  intro j _
  have hi : Integrable (fun ω => ξ ω j) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => j)
  exact hi.const_mul _

omit [IsProbabilityMeasure ν] in
theorem integrable_convolutionTranslationD2_observation
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) :
    Integrable (fun ω => s.convolutionTranslationD2 ν x (ξ ω)) μ := by
  unfold convolutionTranslationD2
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  have hi : Integrable (fun ω => ξ ω j * ξ ω k) μ := by
    simpa [Fin.prod_univ_succ] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k] : Fin 2 → Fin p)
  simpa only [mul_assoc] using hi.const_mul (s.convolutionSecondDerivative ν x j k)

omit [IsProbabilityMeasure ν] in
theorem integrable_convolutionTranslationD3_observation
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) :
    Integrable (fun ω => s.convolutionTranslationD3 ν x (ξ ω)) μ := by
  unfold convolutionTranslationD3
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  have hi : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l] : Fin 3 → Fin p)
  simpa only [mul_assoc] using hi.const_mul (s.convolutionThirdDerivative ν x j k l)

omit [IsProbabilityMeasure ν] in
theorem integral_convolutionTranslationD1_centered
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0) (x : Vector p) :
    (∫ ω, s.convolutionTranslationD1 ν x (ξ ω) ∂μ) = 0 := by
  have hi (j : Fin p) : Integrable (fun ω => ξ ω j) μ := by
    simpa only [Fin.prod_univ_one] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (fun _ : Fin 1 => j)
  unfold convolutionTranslationD1
  rw [integral_finset_sum Finset.univ (fun j _ => (hi j).const_mul _)]
  simp_rw [integral_const_mul, hcenter, mul_zero]
  exact Finset.sum_const_zero

omit [IsProbabilityMeasure ν] in
theorem integral_convolutionTaylor3_centered
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0) (x : Vector p) (a : ℝ) :
    (∫ ω, s.convolutionTaylor3 ν x (a • ξ ω) ∂μ) =
      s.convolution ν x + a ^ 2 / 2 *
          (∫ ω, s.convolutionTranslationD2 ν x (ξ ω) ∂μ) +
        a ^ 3 / 6 * (∫ ω, s.convolutionTranslationD3 ν x (ξ ω) ∂μ) := by
  let U₁ := fun ω => s.convolutionTranslationD1 ν x (ξ ω)
  let U₂ := fun ω => s.convolutionTranslationD2 ν x (ξ ω)
  let U₃ := fun ω => s.convolutionTranslationD3 ν x (ξ ω)
  have h₁ : Integrable U₁ μ := s.integrable_convolutionTranslationD1_observation ν μ ξ hξ hbound x
  have h₂ : Integrable U₂ μ := s.integrable_convolutionTranslationD2_observation ν μ ξ hξ hbound x
  have h₃ : Integrable U₃ μ := s.integrable_convolutionTranslationD3_observation ν μ ξ hξ hbound x
  have hzero : (∫ ω, U₁ ω ∂μ) = 0 :=
    s.integral_convolutionTranslationD1_centered ν μ ξ hξ hbound hcenter x
  have heq : (fun ω => s.convolutionTaylor3 ν x (a • ξ ω)) =
      (fun ω => s.convolution ν x + a * U₁ ω + (a ^ 2 * U₂ ω) / 2 +
        (a ^ 3 * U₃ ω) / 6) := by
    funext ω
    simp only [convolutionTaylor3, s.convolutionTranslationD1_smul,
      s.convolutionTranslationD2_smul, s.convolutionTranslationD3_smul]
    rfl
  rw [heq,
    integral_add (f := fun ω => s.convolution ν x + a * U₁ ω + (a ^ 2 * U₂ ω) / 2)
      (g := fun ω => (a ^ 3 * U₃ ω) / 6)
      (((integrable_const _).add (h₁.const_mul a)).add ((h₂.const_mul (a ^ 2)).div_const 2))
      ((h₃.const_mul (a ^ 3)).div_const 6),
    integral_add (f := fun ω => s.convolution ν x + a * U₁ ω)
      (g := fun ω => (a ^ 2 * U₂ ω) / 2)
      ((integrable_const _).add (h₁.const_mul a)) ((h₂.const_mul (a ^ 2)).div_const 2),
    integral_add (integrable_const _) (h₁.const_mul a)]
  simp only [integral_div, integral_const_mul, hzero, mul_zero, integral_const,
    measureReal_univ_eq_one, smul_eq_mul, one_mul, add_zero]
  dsimp [U₂, U₃]
  ring

omit [IsProbabilityMeasure ν] in
theorem integral_convolutionGradientTaylor2_centered
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ)
    (hcenter : ∀ j, (∫ ω, ξ ω j ∂μ) = 0) (x : Vector p) (a : ℝ) :
    (∫ ω, s.convolutionGradientTaylor2 ν x (ξ ω) a ∂μ) =
      a * (∫ ω, s.convolutionTranslationD2 ν x (ξ ω) ∂μ) +
        a ^ 2 / 2 * (∫ ω, s.convolutionTranslationD3 ν x (ξ ω) ∂μ) := by
  let U₁ := fun ω => s.convolutionTranslationD1 ν x (ξ ω)
  let U₂ := fun ω => s.convolutionTranslationD2 ν x (ξ ω)
  let U₃ := fun ω => s.convolutionTranslationD3 ν x (ξ ω)
  have h₁ : Integrable U₁ μ := s.integrable_convolutionTranslationD1_observation ν μ ξ hξ hbound x
  have h₂ : Integrable U₂ μ := s.integrable_convolutionTranslationD2_observation ν μ ξ hξ hbound x
  have h₃ : Integrable U₃ μ := s.integrable_convolutionTranslationD3_observation ν μ ξ hξ hbound x
  have hzero : (∫ ω, U₁ ω ∂μ) = 0 :=
    s.integral_convolutionTranslationD1_centered ν μ ξ hξ hbound hcenter x
  change (∫ ω, U₁ ω + a * U₂ ω + a ^ 2 * U₃ ω / 2 ∂μ) = _
  rw [integral_add (f := fun ω => U₁ ω + a * U₂ ω)
    (g := fun ω => a ^ 2 * U₃ ω / 2) (h₁.add (h₂.const_mul a))
    ((h₃.const_mul (a ^ 2)).div_const 2), integral_add h₁ (h₂.const_mul a)]
  simp only [integral_div, integral_const_mul, hzero, zero_add]
  dsimp [U₂, U₃]
  ring

noncomputable def observationSecondTerm {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) : ℝ :=
  ∫ ω, s.convolutionTranslationD2 ν x (ξ ω) ∂μ

noncomputable def observationThirdTerm {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) : ℝ :=
  ∫ ω, s.convolutionTranslationD3 ν x (ξ ω) ∂μ

omit [IsProbabilityMeasure ν] in
theorem observationThirdTerm_eq_tensor
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) :
    s.observationThirdTerm ν μ ξ x =
      ∑ j, ∑ k, ∑ l, (∫ ω, ξ ω j * ξ ω k * ξ ω l ∂μ) *
        s.convolutionThirdDerivative ν x j k l := by
  have hi (j k l : Fin p) : Integrable (fun ω => ξ ω j * ξ ω k * ξ ω l) μ := by
    simpa [Fin.prod_univ_succ, mul_assoc] using
      integrable_bounded_coordinate_product μ ξ hξ hbound (![j, k, l] : Fin 3 → Fin p)
  unfold observationThirdTerm convolutionTranslationD3
  have heq (ω : Ω) (j k l : Fin p) :
      s.convolutionThirdDerivative ν x j k l * ξ ω j * ξ ω k * ξ ω l =
      s.convolutionThirdDerivative ν x j k l * (ξ ω j * ξ ω k * ξ ω l) := by ring
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => integrable_finset_sum Finset.univ
      (fun l _ => (hi j k l).const_mul (s.convolutionThirdDerivative ν x j k l))))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => integrable_finset_sum Finset.univ
    (fun l _ => (hi j k l).const_mul (s.convolutionThirdDerivative ν x j k l)))]
  apply Finset.sum_congr rfl
  intro k _
  rw [integral_finset_sum Finset.univ
    (fun l _ => (hi j k l).const_mul (s.convolutionThirdDerivative ν x j k l))]
  apply Finset.sum_congr rfl
  intro l _
  rw [integral_const_mul]
  ring

omit [IsProbabilityMeasure ν] in
theorem sum_observationThirdTerm_eq_aggregate
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) (x : Vector p) :
    (∑ i, s.observationThirdTerm ν μ (ξ i) x) =
      ∑ j, ∑ k, ∑ l, (∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ) *
        s.convolutionThirdDerivative ν x j k l := by
  simp_rw [s.observationThirdTerm_eq_tensor ν μ _ (hξ _) (hbound _) x]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l _
  simp only [Finset.sum_mul]

omit [IsProbabilityMeasure ν] in
/-- The aggregate tensor is formed before absolute values, exactly preserving
cancellation between the original observations. -/
theorem abs_sum_observationThirdTerm_le_gamma3
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {δ : ℝ}
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ) (x : Vector p) :
    |∑ i, s.observationThirdTerm ν μ (ξ i) x| ≤
      gamma3 μ ξ * ∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative ν x j k l| := by
  rw [s.sum_observationThirdTerm_eq_aggregate ν μ ξ hξ hbound x]
  have hentry (j k l : Fin p) : |∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ| ≤
      gamma3 μ ξ := by
    apply (Finset.le_fold_max _).mpr
    exact Or.inr ⟨(j, k, l), Finset.mem_univ _, le_rfl⟩
  simp only [Finset.mul_sum]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro k _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro l _
  rw [abs_mul]
  exact mul_le_mul_of_nonneg_right (hentry j k l) (abs_nonneg _)

/-- The concrete residual after extracting the centered quadratic and cubic
Taylor terms from the actual one-observation derivative. Its fourth-order
bound uses centering and the Taylor theorems, not a comparison assumption. -/
noncomputable def oneObservationTaylorResidual {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) (ξ : Ω → Vector p) (x : Vector p) (t : ℝ) : ℝ :=
  ((t - 3) / (1 + t) ^ 3) *
      (s.translatedConvolution ν μ ξ x (thinningScale t) - s.convolution ν x -
        thinningScale t ^ 2 / 2 * s.observationSecondTerm ν μ ξ x -
        thinningScale t ^ 3 / 6 * s.observationThirdTerm ν μ ξ x) +
    thinningProbability t *
      ((∫ ω, ∑ j, ξ ω j *
          s.convolutionFirstDerivative ν (line x (ξ ω) (thinningScale t)) j ∂μ) -
        thinningScale t * s.observationSecondTerm ν μ ξ x -
        thinningScale t ^ 2 / 2 * s.observationThirdTerm ν μ ξ x)

/-- The actual translation derivative has the computed coefficients `−1/2`
and `−t/3`, with both moment contractions evaluated at the same point. -/
theorem hasDerivAt_bernoulliTranslation_taylor
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Ω → Vector p) (hξ : Measurable ξ) {δ : ℝ}
    (hbound : ∀ᵐ ω ∂μ, ‖ξ ω‖ ≤ δ) (x : Vector p) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (s.bernoulliTranslation ν μ ξ x)
      (-(s.observationSecondTerm ν μ ξ x) / 2 -
        t / 3 * s.observationThirdTerm ν μ ξ x +
        s.oneObservationTaylorResidual ν μ ξ x t) t := by
  have hd := s.hasDerivAt_bernoulliTranslation ν μ ξ hξ hbound x ht
  convert hd using 1
  unfold oneObservationTaylorResidual thinningProbability thinningScale
  have hn : 1 + t ≠ 0 := by linarith
  field_simp [hn]
  ring

end FaceSmoother
end RectangleCLT
