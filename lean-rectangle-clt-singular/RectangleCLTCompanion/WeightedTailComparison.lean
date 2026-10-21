import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-! A strict-tail expectation comparison, including probability measures
with atoms. The proof uses layer cake, so no continuity of either law
and no unproved Stieltjes integration formula is needed. -/

open MeasureTheory Set

namespace RectangleCLT.Companion

noncomputable section

theorem lower_layercake_comparison (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {f g : ℝ → ℝ} (hf : Measurable f) (hg : Measurable g)
    (hf0 : ∀ x, 0 ≤ f x) (hg0 : ∀ x, 0 ≤ g x)
    (hf1 : ∀ x, f x ≤ 1) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ}
    (hlevel : ∀ u ∈ Ioc (0 : ℝ) 1,
      |μ.real {x | u ≤ f x} - ν.real {x | u ≤ g x}| ≤ ε) :
    |(∫ x, f x ∂μ) - ∫ x, g x ∂ν| ≤ ε := by
  have hfi : Integrable f μ := (integrable_const (1 : ℝ)).mono'
    hf.aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hf0 x)] using hf1 x))
  have hgi : Integrable g ν := (integrable_const (1 : ℝ)).mono'
    hg.aestronglyMeasurable (ae_of_all _ (fun x => by
      simpa only [Real.norm_eq_abs, abs_of_nonneg (hg0 x)] using hg1 x))
  rw [hfi.integral_eq_integral_Ioc_meas_le (ae_of_all _ hf0) (ae_of_all _ hf1),
    hgi.integral_eq_integral_Ioc_meas_le (ae_of_all _ hg0) (ae_of_all _ hg1)]
  have hi (κ : Measure ℝ) [IsProbabilityMeasure κ] (h : ℝ → ℝ) :
      IntegrableOn (fun u => κ.real {x | u ≤ h x}) (Ioc (0 : ℝ) 1) := by
    have hm : Measurable (fun u => κ.real {x | u ≤ h x}) :=
      (show Antitone (fun u => κ.real {x | u ≤ h x}) from
        fun u v huv => measureReal_mono (fun x hx => huv.trans hx)).measurable
    apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro u
    rw [Real.norm_eq_abs, abs_of_nonneg measureReal_nonneg]
    exact (measureReal_mono (subset_univ _)).trans_eq measureReal_univ_eq_one
  rw [← integral_sub (hi μ f) (hi ν g)]
  calc
    _ ≤ ∫ u in Ioc (0 : ℝ) 1,
        |μ.real {x | u ≤ f x} - ν.real {x | u ≤ g x}| := abs_integral_le_integral_abs
    _ ≤ ∫ _ in Ioc (0 : ℝ) 1, ε := by
      apply integral_mono_ae ((hi μ f).sub (hi ν g)).abs (integrable_const ε)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
      exact hlevel u hu
    _ = ε := by simp

def lowerStrictTailWeight (s y : ℝ) : ℝ :=
  if 0 < y then Real.exp (-s * y) else 0

theorem lowerStrictTailWeight_measurable (s : ℝ) :
    Measurable (lowerStrictTailWeight s) := by
  unfold lowerStrictTailWeight
  exact Measurable.ite (measurableSet_lt measurable_const measurable_id)
    ((measurable_const.mul measurable_id).exp) measurable_const

theorem lowerStrictTailWeight_nonneg (s y : ℝ) :
    0 ≤ lowerStrictTailWeight s y := by
  unfold lowerStrictTailWeight
  split_ifs <;> positivity

theorem lowerStrictTailWeight_le_one {s : ℝ} (hs : 0 ≤ s) (y : ℝ) :
    lowerStrictTailWeight s y ≤ 1 := by
  unfold lowerStrictTailWeight
  split_ifs with hy
  · exact Real.exp_le_one_iff.mpr (by nlinarith)
  · norm_num

theorem lowerStrictTailWeight_superlevel {s u : ℝ} (hs : 0 < s) (hu : 0 < u) :
    {y | u ≤ lowerStrictTailWeight s y} = Ioc 0 (-Real.log u / s) := by
  ext y
  simp only [mem_setOf_eq, mem_Ioc, lowerStrictTailWeight]
  by_cases hy : 0 < y
  · simp only [if_pos hy, hy, true_and, if_true]
    rw [← Real.log_le_iff_le_exp hu, le_div_iff₀ hs]
    constructor <;> intro hh <;> nlinarith
  · simp [hy, not_le.mpr hu]

theorem lower_cdf_Ioc_comparison (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε : ℝ} (hε : 0 ≤ ε)
    (hcdf : ∀ x, |μ.real (Iic x) - ν.real (Iic x)| ≤ ε)
    (a b : ℝ) : |μ.real (Ioc a b) - ν.real (Ioc a b)| ≤ 2 * ε := by
  by_cases hab : a ≤ b
  · have hset : Ioc a b = Iic b \ Iic a := by ext x; simp [and_comm]
    rw [hset, measureReal_diff (Iic_subset_Iic.mpr hab) measurableSet_Iic,
      measureReal_diff (Iic_subset_Iic.mpr hab) measurableSet_Iic]
    have ha := abs_le.mp (hcdf a)
    have hb := abs_le.mp (hcdf b)
    apply abs_le.mpr
    constructor <;> linarith
  · simp [Ioc_eq_empty_of_le (le_of_not_ge hab), hε]

/-- Kolmogorov distance controls the exponentially weighted strict tail
by twice that distance, even for discrete or lattice-valued laws. -/
theorem lower_strict_weighted_tail_comparison (μ ν : Measure ℝ)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    {ε s : ℝ} (hε : 0 ≤ ε) (hs : 0 < s)
    (hcdf : ∀ x, |μ.real (Iic x) - ν.real (Iic x)| ≤ ε) :
    |(∫ y, lowerStrictTailWeight s y ∂μ) -
      ∫ y, lowerStrictTailWeight s y ∂ν| ≤ 2 * ε := by
  apply lower_layercake_comparison μ ν
    (lowerStrictTailWeight_measurable s) (lowerStrictTailWeight_measurable s)
    (lowerStrictTailWeight_nonneg s) (lowerStrictTailWeight_nonneg s)
    (lowerStrictTailWeight_le_one hs.le) (lowerStrictTailWeight_le_one hs.le)
  intro u hu
  rw [lowerStrictTailWeight_superlevel hs hu.1]
  exact lower_cdf_Ioc_comparison μ ν hε hcdf 0 _

end

end RectangleCLT.Companion
