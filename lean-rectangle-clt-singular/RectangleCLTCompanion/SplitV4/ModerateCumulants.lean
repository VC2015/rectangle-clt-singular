import RectangleCLT.ScalarBerryEsseen
import RectangleCLTCompanion.WeightedTailComparison
import Mathlib.Probability.Moments.Tilted
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine bounded-scalar Esscher calculus for the iid-free moderate-tail lemma. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Ω → ℝ} {δ : ℝ}

theorem moderate_integrable_bounded (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) :
    Integrable X μ := by
  exact (integrable_const δ).mono' hX.aestronglyMeasurable
    (by simpa only [Real.norm_eq_abs] using hbound)

theorem moderate_integrable_exp (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply (integrable_const (Real.exp (|t| * δ))).mono'
    (measurable_const.mul hX |>.exp.aestronglyMeasurable)
  filter_upwards [hbound] with ω hω
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
  apply Real.exp_le_exp.mpr
  exact (le_abs_self (t * X ω)).trans (by rw [abs_mul]; exact mul_le_mul_of_nonneg_left hω (abs_nonneg _))

theorem moderate_integrableExpSet (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) :
    integrableExpSet X μ = univ := by
  ext t
  simp only [mem_univ, iff_true]
  exact moderate_integrable_exp hX hbound t

theorem moderate_mem_interior (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    t ∈ interior (integrableExpSet X μ) := by rw [moderate_integrableExpSet hX hbound, interior_univ]; trivial

def moderateScalarTilt (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : Measure Ω := μ.tilted (fun ω => t * X ω)

theorem moderateScalarTilt_probability (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    IsProbabilityMeasure (moderateScalarTilt μ X t) :=
  isProbabilityMeasure_tilted (moderate_integrable_exp hX hbound t)

theorem moderateScalarTilt_bound (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    ∀ᵐ ω ∂moderateScalarTilt μ X t, |X ω| ≤ δ :=
  (tilted_absolutelyContinuous μ (fun ω => t * X ω)).ae_le hbound

def moderateTiltMoment (μ : Measure Ω) (X : Ω → ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (∫ ω, X ω ^ k * Real.exp (t * X ω) ∂μ) / mgf X μ t

def moderateTiltMean (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ := moderateTiltMoment μ X 1 t

def moderateTiltVariance (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  moderateTiltMoment μ X 2 t - moderateTiltMean μ X t ^ 2

def moderateTiltThird (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  moderateTiltMoment μ X 3 t - 3 * moderateTiltMoment μ X 2 t * moderateTiltMean μ X t +
    2 * moderateTiltMean μ X t ^ 3

def moderateTiltFourthCumulant (μ : Measure Ω) (X : Ω → ℝ) (t : ℝ) : ℝ :=
  moderateTiltMoment μ X 4 t - 4 * moderateTiltMoment μ X 3 t * moderateTiltMean μ X t -
    3 * moderateTiltMoment μ X 2 t ^ 2 +
    12 * moderateTiltMoment μ X 2 t * moderateTiltMean μ X t ^ 2 -
    6 * moderateTiltMean μ X t ^ 4

theorem moderateTiltMoment_eq_integral (k : ℕ) (t : ℝ) :
    moderateTiltMoment μ X k t = ∫ ω, X ω ^ k ∂moderateScalarTilt μ X t := by
  rw [moderateScalarTilt, integral_tilted_mul_eq_mgf, moderateTiltMoment, ← integral_div]
  congr 1
  funext ω
  simp only [smul_eq_mul]
  ring

theorem hasDerivAt_moderateTiltMoment (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ)
    (k : ℕ) (t : ℝ) :
    HasDerivAt (moderateTiltMoment μ X k)
      (moderateTiltMoment μ X (k + 1) t - moderateTiltMoment μ X k t * moderateTiltMean μ X t) t := by
  have ht := moderate_mem_interior hX hbound t
  have hmgf : mgf X μ t ≠ 0 := (mgf_pos (moderate_integrable_exp hX hbound t)).ne'
  have hh := (hasDerivAt_integral_pow_mul_exp_real ht k).div (hasDerivAt_mgf ht) hmgf
  convert hh using 1
  · unfold moderateTiltMean moderateTiltMoment
    simp only [pow_one]
    field_simp
    ring

theorem hasDerivAt_moderateCGF (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ)
    (t : ℝ) : HasDerivAt (cgf X μ) (moderateTiltMean μ X t) t := by
  have hmgf := (hasDerivAt_mgf (moderate_mem_interior hX hbound t)).log
    (mgf_pos (moderate_integrable_exp hX hbound t)).ne'
  simpa only [cgf, moderateTiltMean, moderateTiltMoment, pow_one] using hmgf

theorem hasDerivAt_moderateTiltMean (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ)
    (t : ℝ) : HasDerivAt (moderateTiltMean μ X) (moderateTiltVariance μ X t) t := by
  simpa only [moderateTiltMean, moderateTiltVariance, ← pow_two] using
    hasDerivAt_moderateTiltMoment hX hbound 1 t

theorem hasDerivAt_moderateTiltVariance (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ)
    (t : ℝ) : HasDerivAt (moderateTiltVariance μ X) (moderateTiltThird μ X t) t := by
  have hh := (hasDerivAt_moderateTiltMoment hX hbound 2 t).sub
    ((hasDerivAt_moderateTiltMean hX hbound t).pow 2)
  convert hh using 1
  unfold moderateTiltThird moderateTiltVariance moderateTiltMean
  ring

theorem hasDerivAt_moderateTiltThird (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ)
    (t : ℝ) : HasDerivAt (moderateTiltThird μ X) (moderateTiltFourthCumulant μ X t) t := by
  have hm := hasDerivAt_moderateTiltMean hX hbound t
  have hh := ((hasDerivAt_moderateTiltMoment hX hbound 3 t).sub
    (((hasDerivAt_moderateTiltMoment hX hbound 2 t).const_mul 3).mul hm)).add
      ((hm.pow 3).const_mul 2)
  convert hh using 1
  unfold moderateTiltFourthCumulant moderateTiltVariance moderateTiltMean
  ring


theorem moderateTiltMean_eq_deriv (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    moderateTiltMean μ X t = deriv (cgf X μ) t := (hasDerivAt_moderateCGF hX hbound t).deriv.symm

theorem moderateTiltVariance_eq_iteratedDeriv (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    moderateTiltVariance μ X t = iteratedDeriv 2 (cgf X μ) t := by
  have heq : deriv (cgf X μ) = moderateTiltMean μ X :=
    funext (fun u => (hasDerivAt_moderateCGF hX hbound u).deriv)
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, heq]
  exact (hasDerivAt_moderateTiltMean hX hbound t).deriv.symm

theorem moderateTiltMean_eq_integral (t : ℝ) :
    moderateTiltMean μ X t = ∫ ω, X ω ∂moderateScalarTilt μ X t := by
  simpa only [moderateTiltMean, pow_one] using moderateTiltMoment_eq_integral (μ := μ) (X := X) 1 t

theorem moderateTiltMoment_zero (k : ℕ) :
    moderateTiltMoment μ X k 0 = ∫ ω, X ω ^ k ∂μ := by
  simp [moderateTiltMoment, mgf_zero]

theorem moderate_integrable_pow (hX : Measurable X) (hδ : 0 ≤ δ)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (k : ℕ) : Integrable (fun ω => X ω ^ k) μ := by
  apply moderate_integrable_bounded (hX.pow_const k)
  filter_upwards [hbound] with ω hω
  rw [abs_pow]
  exact pow_le_pow_left₀ (abs_nonneg _) hω k

theorem moderate_memLp_two (hX : Measurable X) (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) : MemLp X 2 μ :=
  (memLp_top_of_bound hX.aestronglyMeasurable δ
    (by simpa only [Real.norm_eq_abs] using hbound)).mono_exponent le_top

theorem moderateTiltVariance_eq_variance (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    moderateTiltVariance μ X t = variance X (moderateScalarTilt μ X t) := by
  exact (moderateTiltVariance_eq_iteratedDeriv hX hbound t).trans
    (variance_tilted_mul (moderate_mem_interior hX hbound t)).symm

theorem moderateTiltMean_abs_le (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) : |moderateTiltMean μ X t| ≤ δ := by
  letI := moderateScalarTilt_probability hX hbound t
  rw [moderateTiltMean_eq_integral]
  simpa only [Real.norm_eq_abs, measureReal_univ_eq_one, mul_one] using
    norm_integral_le_of_norm_le_const (μ := moderateScalarTilt μ X t) (f := X)
      (by simpa only [Real.norm_eq_abs] using moderateScalarTilt_bound hbound t)

theorem moderateTilt_centered_bound (hX : Measurable X)
    (hbound : ∀ᵐ ω ∂μ, |X ω| ≤ δ) (t : ℝ) :
    ∀ᵐ ω ∂moderateScalarTilt μ X t, |X ω - moderateTiltMean μ X t| ≤ 2 * δ := by
  filter_upwards [moderateScalarTilt_bound hbound t] with ω hω
  exact (abs_sub _ _).trans (by linarith [moderateTiltMean_abs_le hX hbound t])

end
end RectangleCLT.Companion.SplitV4
