import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.Basic

/-! A genuine uniform L1 derivative budget controls increments of the
averaged function. Fubini on each compact time interval discharges the
interchange; no pointwise uniform domination of the derivatives is assumed.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem averaged_increment_le_of_uniform_L1_derivative
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (F D : ℝ → Ω → ℝ) (hD : Measurable (Function.uncurry D))
    (hFi : ∀ t, Integrable (F t) μ) (hDi : ∀ t, Integrable (D t) μ)
    (hDc : ∀ ω, Continuous (fun t => D t ω))
    (hDeriv : ∀ ω t, HasDerivAt (fun s => F s ω) (D t ω) t)
    {B : ℝ} (hB : ∀ t, (∫ ω, |D t ω| ∂μ) ≤ B) (a c : ℝ) :
    |(∫ ω, F c ω ∂μ) - ∫ ω, F a ω ∂μ| ≤ B * |c - a| := by
  have hordered (a c : ℝ) (hac : a ≤ c) :
      |(∫ ω, F c ω ∂μ) - ∫ ω, F a ω ∂μ| ≤ B * (c - a) := by
    let τ : Measure ℝ := volume.restrict (Icc a c)
    letI : IsFiniteMeasure τ := ⟨by
      change volume.restrict (Icc a c) univ < ⊤
      rw [Measure.restrict_apply_univ]
      exact isCompact_Icc.measure_lt_top⟩
    have hnmeas : Measurable (fun t => ∫ ω, ‖D t ω‖ ∂μ) :=
      hD.norm.stronglyMeasurable.integral_prod_right'.measurable
    have hni : Integrable (fun t => ∫ ω, ‖D t ω‖ ∂μ) τ := by
      apply (integrable_const B).mono' hnmeas.aestronglyMeasurable
      exact ae_of_all _ (fun t => by
        rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg (fun ω => norm_nonneg _))]
        simpa only [Real.norm_eq_abs] using hB t)
    have hji : Integrable (Function.uncurry D) (τ.prod μ) :=
      (integrable_prod_iff hD.aestronglyMeasurable).mpr ⟨ae_of_all _ hDi, hni⟩
    have hFTC (ω : Ω) : F c ω - F a ω = ∫ t in Icc a c, D t ω := by
      have hh := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (fun t _ => hDeriv ω t) ((hDc ω).intervalIntegrable a c)
      rw [intervalIntegral.integral_of_le hac, ← integral_Icc_eq_integral_Ioc] at hh
      exact hh.symm
    have he : (∫ ω, F c ω ∂μ) - ∫ ω, F a ω ∂μ = ∫ t, ∫ ω, D t ω ∂μ ∂τ := by
      rw [← integral_sub (hFi c) (hFi a)]
      change (∫ ω, F c ω - F a ω ∂μ) = _
      simp_rw [hFTC]
      exact (integral_integral_swap hji).symm
    rw [he]
    calc
      _ ≤ ∫ t, ‖∫ ω, D t ω ∂μ‖ ∂τ := by
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun t => ∫ ω, D t ω ∂μ) (μ := τ)
      _ ≤ ∫ _t, B ∂τ := integral_mono hji.integral_prod_left.norm (integrable_const B) (fun t => by
        exact (norm_integral_le_integral_norm (D t)).trans (by simpa only [Real.norm_eq_abs] using hB t))
      _ = B * (c - a) := by
        change (∫ _t in Icc a c, B) = _
        rw [setIntegral_const, measureReal_def, Real.volume_Icc,
          ENNReal.toReal_ofReal (sub_nonneg.mpr hac), smul_eq_mul]
        ring
  by_cases hac : a ≤ c
  · simpa only [abs_of_nonneg (sub_nonneg.mpr hac)] using hordered a c hac
  · have hca := le_of_not_ge hac
    have hh := hordered c a hca
    rw [abs_sub_comm] at hh
    rw [abs_of_nonpos (sub_nonpos.mpr hca)]
    convert hh using 1 <;> ring

end

end RectangleCLT.Companion.SplitV4
