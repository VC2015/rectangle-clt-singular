import RectangleCLT.GaussianNormalMap
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! Genuine Gaussian maximum laws and smooth-test-to-interval limits.
The final test-bound implication is a reusable analytic implication;
the intrinsic Gaussian boundary proof must separately discharge its
smooth-test hypothesis. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def gaussianAffineMaximum {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty
    (fun α => faceDot (w α) x - a α)

def activeGaussianBranch {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) : Fin m :=
  Classical.choose (Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
    Finset.univ_nonempty (fun α => faceDot (w α) x - a α))

theorem activeGaussianBranch_attains {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) :
    gaussianAffineMaximum w a x = faceDot (w (activeGaussianBranch w a x)) x -
      a (activeGaussianBranch w a x) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
    Finset.univ_nonempty (fun α => faceDot (w α) x - a α))).2

theorem affineBranch_le_gaussianAffineMaximum {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (x : Vector r) (α : Fin m) :
    faceDot (w α) x - a α ≤ gaussianAffineMaximum w a x :=
  Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
    (f := fun α => faceDot (w α) x - a α) (Finset.mem_univ α)

theorem continuous_faceDot_left {r : ℕ} (u : Vector r) : Continuous (faceDot u) := by
  unfold faceDot
  exact continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))

theorem continuous_gaussianAffineMaximum {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) : Continuous (gaussianAffineMaximum w a) := by
  exact Continuous.finset_sup'_apply Finset.univ_nonempty
    (fun α _ => (continuous_faceDot_left (w α)).sub continuous_const)

def faceDotLinear {r : ℕ} (u : Vector r) : Vector r →ₗ[ℝ] ℝ where
  toFun := faceDot u
  map_add' x y := by simp [faceDot, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by simp [faceDot, Finset.mul_sum, mul_left_comm, mul_comm]

/-- Every proper affine hyperplane has zero actual standard Gaussian
measure, by absolute continuity with respect to finite-dimensional volume. -/
theorem standardGaussian_affine_hyperplane_zero {r : ℕ}
    (u : Vector r) (hu : u ≠ 0) (c : ℝ) :
    standardGaussian r {x | faceDot u x = c} = 0 := by
  let H : AffineSubspace ℝ (Vector r) :=
    (affineSpan ℝ ({c} : Set ℝ)).comap (faceDotLinear u).toAffineMap
  have hH (x : Vector r) : x ∈ H ↔ faceDot u x = c := by
    simp [H, AffineSubspace.mem_affineSpan_singleton, faceDotLinear]
  have hproper : H ≠ ⊤ := by
    intro ht
    have hz : (0 : Vector r) ∈ H := by rw [ht]; trivial
    have hc : c = 0 := by simpa only [faceDot, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, eq_comm] using (hH 0).mp hz
    apply hu
    funext j
    have hj : Pi.single j (1 : ℝ) ∈ H := by rw [ht]; trivial
    have he := (hH _).mp hj
    rw [faceDot_comm] at he
    simpa [faceDot, Pi.single_apply, ite_mul, hc] using he
  have hvol : volume (H : Set (Vector r)) = 0 := Measure.addHaar_affineSubspace volume H hproper
  have hac : standardGaussian r ≪ (volume : Measure (Vector r)) := by
    rw [standardGaussian_eq_withDensity]
    exact withDensity_absolutelyContinuous _ _
  have he : (H : Set (Vector r)) = {x | faceDot u x = c} := Set.ext hH
  rw [← he]
  exact hac hvol

theorem gaussianAffineMaximum_level_zero {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (hw : ∀ α, w α ≠ 0) (c : ℝ) :
    standardGaussian r {x | gaussianAffineMaximum w a x = c} = 0 := by
  have hsub : {x | gaussianAffineMaximum w a x = c} ⊆
      ⋃ α : Fin m, {x | faceDot (w α) x = c + a α} := by
    intro x hx
    apply mem_iUnion.mpr
    refine ⟨activeGaussianBranch w a x, ?_⟩
    have he := activeGaussianBranch_attains w a x
    change gaussianAffineMaximum w a x = c at hx
    change faceDot (w (activeGaussianBranch w a x)) x = _
    linarith
  exact measure_mono_null hsub
    (measure_iUnion_null (fun α => standardGaussian_affine_hyperplane_zero (w α) (hw α) (c + a α)))

theorem gaussianAffineMaximum_noAtoms {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ) (hw : ∀ α, w α ≠ 0) :
    NoAtoms ((standardGaussian r).map (gaussianAffineMaximum w a)) := by
  constructor
  intro c
  rw [Measure.map_apply (continuous_gaussianAffineMaximum w a).measurable (measurableSet_singleton c)]
  exact gaussianAffineMaximum_level_zero w a hw c

theorem gaussian_affine_branches_tie_zero {r : ℕ} (u v : Vector r) (huv : u ≠ v) (a b : ℝ) :
    standardGaussian r {x | faceDot u x - a = faceDot v x - b} = 0 := by
  have he : {x | faceDot u x - a = faceDot v x - b} =
      {x | faceDot (u - v) x = a - b} := by
    ext x
    have hd : faceDot (u - v) x = faceDot u x - faceDot v x := by
      simp [faceDot, sub_mul, Finset.sum_sub_distrib]
    simp only [mem_setOf_eq, hd]
    constructor <;> intro h <;> linarith
  rw [he]
  exact standardGaussian_affine_hyperplane_zero (u - v) (sub_ne_zero.mpr huv) (a - b)

theorem gaussian_affine_branches_ae_distinct_rows_ne {m r : ℕ}
    (w : Fin m → Vector r) (a : Fin m → ℝ) :
    ∀ᵐ x ∂standardGaussian r, ∀ α β : Fin m, w α ≠ w β →
      faceDot (w α) x - a α ≠ faceDot (w β) x - a β := by
  apply ae_all_iff.mpr
  intro α
  apply ae_all_iff.mpr
  intro β
  by_cases hab : w α = w β
  · exact ae_of_all _ (fun _ h => False.elim (h hab))
  · have ht := gaussian_affine_branches_tie_zero (w α) (w β) hab (a α) (a β)
    have hr : ∀ᵐ x ∂standardGaussian r, faceDot (w α) x - a α ≠ faceDot (w β) x - a β := by
      simpa only [ae_iff, not_not] using ht
    exact hr.mono (fun _ hx _ => hx)

theorem gaussian_affine_branches_ae_pairwise_ne {m r : ℕ}
    (w : Fin m → Vector r) (a : Fin m → ℝ) (hw : Function.Injective w) :
    ∀ᵐ x ∂standardGaussian r, ∀ α β : Fin m, α ≠ β →
      faceDot (w α) x - a α ≠ faceDot (w β) x - a β :=
  (gaussian_affine_branches_ae_distinct_rows_ne w a).mono
    (fun _ hx α β hab => hx α β (fun he => hab (hw he)))

/-- The continuous flat-top density used by the genuine C1 ramps. -/
def gaussianIntervalRampDensity (a b ε x : ℝ) : ℝ :=
  max 0 (min 1 ((x - (a - ε)) / ε)) * max 0 (min 1 (((b + ε) - x) / ε))

theorem continuous_gaussianIntervalRampDensity (a b ε : ℝ) :
    Continuous (gaussianIntervalRampDensity a b ε) := by
  unfold gaussianIntervalRampDensity
  fun_prop

theorem gaussianIntervalRampDensity_nonneg (a b ε x : ℝ) :
    0 ≤ gaussianIntervalRampDensity a b ε x := mul_nonneg (le_max_left _ _) (le_max_left _ _)

theorem gaussianIntervalRampDensity_le_one (a b ε x : ℝ) :
    gaussianIntervalRampDensity a b ε x ≤ 1 := by
  have hl : max 0 (min 1 ((x - (a - ε)) / ε)) ≤ (1 : ℝ) :=
    max_le (by norm_num) (min_le_left _ _)
  have hr : max 0 (min 1 (((b + ε) - x) / ε)) ≤ (1 : ℝ) :=
    max_le (by norm_num) (min_le_left _ _)
  exact mul_le_one₀ hl (le_max_left _ _) hr

theorem gaussianIntervalRampDensity_eq_one {a b ε x : ℝ} (hε : 0 < ε) (hx : x ∈ Icc a b) :
    gaussianIntervalRampDensity a b ε x = 1 := by
  have hl : 1 ≤ (x - (a - ε)) / ε := (le_div_iff₀ hε).mpr (by linarith [hx.1])
  have hr : 1 ≤ ((b + ε) - x) / ε := (le_div_iff₀ hε).mpr (by linarith [hx.2])
  simp only [gaussianIntervalRampDensity, min_eq_left hl, min_eq_left hr, max_eq_right zero_le_one, mul_one]

theorem gaussianIntervalRampDensity_zero_left {a b ε x : ℝ} (hε : 0 < ε) (hx : x ≤ a - ε) :
    gaussianIntervalRampDensity a b ε x = 0 := by
  have hl : (x - (a - ε)) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  unfold gaussianIntervalRampDensity
  rw [max_eq_left ((min_le_right _ _).trans hl), zero_mul]

theorem gaussianIntervalRampDensity_zero_right {a b ε x : ℝ} (hε : 0 < ε) (hx : b + ε ≤ x) :
    gaussianIntervalRampDensity a b ε x = 0 := by
  have hr : ((b + ε) - x) / ε ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) hε.le
  unfold gaussianIntervalRampDensity
  rw [max_eq_left ((min_le_right _ _).trans hr), mul_zero]

theorem gaussianIntervalRampDensity_support_subset {a b ε : ℝ} (hε : 0 < ε) :
    Function.support (gaussianIntervalRampDensity a b ε) ⊆ Ioc (a - ε) (b + ε) := by
  intro x hx
  constructor
  · by_contra hn
    exact hx (gaussianIntervalRampDensity_zero_left hε (le_of_not_gt hn))
  · by_contra hn
    exact hx (gaussianIntervalRampDensity_zero_right hε (by linarith))

theorem integrable_gaussianIntervalRampDensity {a b ε : ℝ} (hε : 0 < ε) :
    Integrable (gaussianIntervalRampDensity a b ε) volume := by
  apply (continuous_gaussianIntervalRampDensity a b ε).integrable_of_hasCompactSupport
  exact HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    ((gaussianIntervalRampDensity_support_subset hε).trans Ioc_subset_Icc_self)

theorem integral_gaussianIntervalRampDensity_le {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    (∫ x, gaussianIntervalRampDensity a b ε x) ≤ b - a + 2 * ε := by
  rw [← intervalIntegral.integral_eq_integral_of_support_subset (gaussianIntervalRampDensity_support_subset hε)]
  have hm := intervalIntegral.integral_mono_on (μ := volume) (by linarith : a - ε ≤ b + ε)
    ((continuous_gaussianIntervalRampDensity a b ε).intervalIntegrable _ _)
    (continuous_const.intervalIntegrable _ _)
    (fun x _ => gaussianIntervalRampDensity_le_one a b ε x)
  simp only [intervalIntegral.integral_const, smul_eq_mul, mul_one] at hm
  convert hm using 1
  ring

def gaussianIntervalRamp (a b ε x : ℝ) : ℝ :=
  (∫ t in Iic x, gaussianIntervalRampDensity a b ε t) / (b - a + 2 * ε)

def gaussianIntervalRampDerivative (a b ε x : ℝ) : ℝ :=
  gaussianIntervalRampDensity a b ε x / (b - a + 2 * ε)

theorem gaussianIntervalRamp_hasDerivAt {a b ε : ℝ} (hε : 0 < ε) (x : ℝ) :
    HasDerivAt (gaussianIntervalRamp a b ε) (gaussianIntervalRampDerivative a b ε x) x := by
  have hi := integrable_gaussianIntervalRampDensity (a := a) (b := b) hε
  have he (y : ℝ) : (∫ t in Iic y, gaussianIntervalRampDensity a b ε t) =
      (∫ t in (a - ε)..y, gaussianIntervalRampDensity a b ε t) +
        ∫ t in Iic (a - ε), gaussianIntervalRampDensity a b ε t := by
    exact sub_eq_iff_eq_add.mp (intervalIntegral.integral_Iic_sub_Iic hi.integrableOn hi.integrableOn)
  have hc := continuous_gaussianIntervalRampDensity a b ε
  have hd := (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable (a - ε) x)
    hc.stronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt).add_const
      (∫ t in Iic (a - ε), gaussianIntervalRampDensity a b ε t)
  exact (hd.congr_of_eventuallyEq (Filter.Eventually.of_forall he)).div_const _

theorem gaussianIntervalRamp_range {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (x : ℝ) :
    0 ≤ gaussianIntervalRamp a b ε x ∧ gaussianIntervalRamp a b ε x ≤ 1 := by
  have hlen : 0 < b - a + 2 * ε := by linarith
  have hi := integrable_gaussianIntervalRampDensity (a := a) (b := b) hε
  have hnonneg : 0 ≤ ∫ t in Iic x, gaussianIntervalRampDensity a b ε t :=
    integral_nonneg (gaussianIntervalRampDensity_nonneg a b ε)
  refine ⟨div_nonneg hnonneg hlen.le, (div_le_one hlen).mpr ?_⟩
  exact (setIntegral_le_integral hi (ae_of_all _ (gaussianIntervalRampDensity_nonneg a b ε))).trans
    (integral_gaussianIntervalRampDensity_le hab hε)

theorem gaussianIntervalRampDerivative_continuous (a b ε : ℝ) :
    Continuous (gaussianIntervalRampDerivative a b ε) :=
  (continuous_gaussianIntervalRampDensity a b ε).div_const _

theorem gaussianIntervalRampDerivative_nonneg {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) (x : ℝ) :
    0 ≤ gaussianIntervalRampDerivative a b ε x :=
  div_nonneg (gaussianIntervalRampDensity_nonneg _ _ _ _) (by linarith)

theorem gaussianIntervalRampDerivative_bounded {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    ∃ D : ℝ, ∀ x, |gaussianIntervalRampDerivative a b ε x| ≤ D := by
  refine ⟨1 / (b - a + 2 * ε), fun x => ?_⟩
  rw [abs_of_nonneg (gaussianIntervalRampDerivative_nonneg hab hε x)]
  exact div_le_div_of_nonneg_right (gaussianIntervalRampDensity_le_one _ _ _ _) (by linarith)

theorem gaussianIntervalRamp_monotone {a b ε : ℝ} (hab : a ≤ b) (hε : 0 < ε) :
    Monotone (gaussianIntervalRamp a b ε) :=
  monotone_of_hasDerivAt_nonneg (gaussianIntervalRamp_hasDerivAt hε)
    (gaussianIntervalRampDerivative_nonneg hab hε)

/-- A universal inequality for genuine bounded nondecreasing C1 tests
implies the exact closed-interval probability bound. The approximating
tests are actual primitives of compactly supported continuous densities;
their derivatives dominate the interval indicator up to a width tending
to `b-a`. This implication contains no Gaussian concentration claim until
its smooth-test premise is discharged. -/
theorem interval_probability_le_of_smooth_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (M : ℝ)
    (hTest : ∀ ψ dψ : ℝ → ℝ, (∀ x, HasDerivAt ψ (dψ x) x) → Continuous dψ →
      Monotone ψ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∃ D : ℝ, ∀ x, |dψ x| ≤ D) → (∫ ω, dψ (F ω) ∂μ) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (F ⁻¹' Icc a b) ≤ (b - a) * M := by
  have hM : 0 ≤ M := by
    have hz := hTest (fun _ => 0) (fun _ => 0) (fun x => hasDerivAt_const x 0)
      continuous_const (fun _ _ _ => le_rfl) (fun _ => ⟨le_rfl, by norm_num⟩)
      ⟨0, fun _ => by simp⟩
    simpa only [integral_zero] using hz
  have hS : MeasurableSet (F ⁻¹' Icc a b) := measurableSet_Icc.preimage hF
  have heps (ε : ℝ) (hε : 0 < ε) : μ.real (F ⁻¹' Icc a b) ≤ (b - a + 2 * ε) * M := by
    let d := gaussianIntervalRampDerivative a b ε
    let w := gaussianIntervalRampDensity a b ε
    let len := b - a + 2 * ε
    have hlen : 0 < len := by dsimp only [len]; linarith
    have ht := hTest (gaussianIntervalRamp a b ε) d (gaussianIntervalRamp_hasDerivAt hε)
      (gaussianIntervalRampDerivative_continuous a b ε) (gaussianIntervalRamp_monotone hab hε)
      (gaussianIntervalRamp_range hab hε) (gaussianIntervalRampDerivative_bounded hab hε)
    have hiw : Integrable (fun ω => w (F ω)) μ := by
      apply (integrable_const (1 : ℝ)).mono'
        ((continuous_gaussianIntervalRampDensity a b ε).measurable.comp hF).aestronglyMeasurable
      exact ae_of_all _ fun ω => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussianIntervalRampDensity_nonneg a b ε (F ω))]
        exact gaussianIntervalRampDensity_le_one a b ε (F ω)
    have hid : Integrable (fun ω => d (F ω)) μ := by
      apply (integrable_const (1 / len)).mono'
        ((gaussianIntervalRampDerivative_continuous a b ε).measurable.comp hF).aestronglyMeasurable
      exact ae_of_all _ fun ω => by
        simp only [Function.comp_apply]
        rw [Real.norm_eq_abs, abs_of_nonneg (gaussianIntervalRampDerivative_nonneg hab hε (F ω))]
        exact div_le_div_of_nonneg_right (gaussianIntervalRampDensity_le_one a b ε (F ω)) hlen.le
    have hiI : Integrable ((F ⁻¹' Icc a b).indicator (fun _ => (1 : ℝ))) μ :=
      (integrable_const (1 : ℝ)).indicator hS
    have hdom (ω : Ω) : (F ⁻¹' Icc a b).indicator (fun _ => (1 : ℝ)) ω ≤ w (F ω) := by
      by_cases hω : ω ∈ F ⁻¹' Icc a b
      · rw [Set.indicator_of_mem hω]
        exact le_of_eq (gaussianIntervalRampDensity_eq_one hε hω).symm
      · rw [Set.indicator_of_not_mem hω]
        exact gaussianIntervalRampDensity_nonneg _ _ _ _
    have hm := integral_mono hiI hiw hdom
    have heI : (∫ ω, (F ⁻¹' Icc a b).indicator (fun _ => (1 : ℝ)) ω ∂μ) =
        μ.real (F ⁻¹' Icc a b) := by
      simpa only [Pi.one_apply] using (integral_indicator_one (μ := μ) hS)
    rw [heI] at hm
    have he : (∫ ω, w (F ω) ∂μ) = len * ∫ ω, d (F ω) ∂μ := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ fun ω => by
        dsimp only [d, w, gaussianIntervalRampDerivative, len]
        field_simp
    exact hm.trans (he.le.trans (mul_le_mul_of_nonneg_left ht hlen.le))
  apply le_of_forall_pos_le_add
  intro η hη
  let ε := η / (2 * (M + 1))
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have he : 2 * ε * (M + 1) = η := by
    dsimp only [ε]
    field_simp
    ring
  have hb := heps ε hε
  nlinarith

/-- The two-sided shell has exactly width `2s`. -/
theorem centered_interval_probability_le_of_smooth_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (M : ℝ)
    (hTest : ∀ ψ dψ : ℝ → ℝ, (∀ x, HasDerivAt ψ (dψ x) x) → Continuous dψ →
      Monotone ψ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∃ D : ℝ, ∀ x, |dψ x| ≤ D) → (∫ ω, dψ (F ω) ∂μ) ≤ M)
    {t s : ℝ} (hs : 0 ≤ s) :
    μ.real (F ⁻¹' Icc (t - s) (t + s)) ≤ (2 * s) * M := by
  have hh := interval_probability_le_of_smooth_tests μ F hF M hTest (by linarith : t - s ≤ t + s)
  convert hh using 1
  ring

/-- The same estimate for actual distribution-function increments. This
uses the real probabilities of the two half-lines and allows their atoms;
the closed-interval estimate itself controls both endpoints. -/
theorem cdf_increment_le_of_smooth_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (M : ℝ)
    (hTest : ∀ ψ dψ : ℝ → ℝ, (∀ x, HasDerivAt ψ (dψ x) x) → Continuous dψ →
      Monotone ψ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∃ D : ℝ, ∀ x, |dψ x| ≤ D) → (∫ ω, dψ (F ω) ∂μ) ≤ M)
    {a b : ℝ} (hab : a ≤ b) :
    μ.real (F ⁻¹' Iic b) - μ.real (F ⁻¹' Iic a) ≤ (b - a) * M := by
  have hs : F ⁻¹' Iic b ⊆ (F ⁻¹' Iic a) ∪ (F ⁻¹' Icc a b) := by
    intro ω hω
    by_cases hwa : F ω ≤ a
    · exact Or.inl hwa
    · exact Or.inr ⟨(lt_of_not_ge hwa).le, hω⟩
  have hb := (measureReal_mono (μ := μ) hs).trans (measureReal_union_le (μ := μ) _ _)
  have hi := interval_probability_le_of_smooth_tests μ F hF M hTest hab
  linarith

theorem centered_cdf_increment_le_of_smooth_tests
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F : Ω → ℝ) (hF : Measurable F) (M : ℝ)
    (hTest : ∀ ψ dψ : ℝ → ℝ, (∀ x, HasDerivAt ψ (dψ x) x) → Continuous dψ →
      Monotone ψ → (∀ x, 0 ≤ ψ x ∧ ψ x ≤ 1) →
      (∃ D : ℝ, ∀ x, |dψ x| ≤ D) → (∫ ω, dψ (F ω) ∂μ) ≤ M)
    {t s : ℝ} (hs : 0 ≤ s) :
    μ.real (F ⁻¹' Iic (t + s)) - μ.real (F ⁻¹' Iic (t - s)) ≤ (2 * s) * M := by
  have hh := cdf_increment_le_of_smooth_tests μ F hF M hTest (by linarith : t - s ≤ t + s)
  convert hh using 1
  ring

end
end RectangleCLT.Companion.SplitV4
