import RectangleCLTCompanion.RademacherTailLimit
import RectangleCLTCompanion.RademacherCriticalDimension
import RectangleCLTCompanion.LowerMaxCDFLimits

/-! # The nonzero critical discrepancy for independent Rademacher coordinates -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def rademacherCriticalDiscrepancy (a : ℝ) : ℝ :=
  Real.exp (-Real.exp (-a^2/3)) - Real.exp (-1)

lemma rademacherCriticalDiscrepancy_pos {a : ℝ} (ha : 0 < a) :
    0 < rademacherCriticalDiscrepancy a := by
  unfold rademacherCriticalDiscrepancy
  apply sub_pos.mpr
  apply Real.exp_lt_exp.mpr
  have he : Real.exp (-a^2/3) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith [sq_pos_of_pos ha]
  linarith

lemma tendsto_rademacherCritical_maximum_CDF {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => lowerCoordinateCDF 1 n (normalMaxThreshold (p n))^(p n))
      atTop (𝓝 (Real.exp (-Real.exp (-a^2/3)))) := by
  have hh := tendsto_maximum_CDF_of_normal_tail_ratio (criticalDimension_tendsto ha hcrit)
    (tendsto_rademacherCritical_tail_ratio ha hcrit)
  simpa only [sub_sub_cancel] using hh

lemma tendsto_rademacherCritical_maximum_discrepancy {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n => lowerCoordinateCDF 1 n (normalMaxThreshold (p n))^(p n) - Real.exp (-1))
      atTop (𝓝 (rademacherCriticalDiscrepancy a)) :=
  (tendsto_rademacherCritical_maximum_CDF ha hcrit).sub_const _

lemma tendsto_rademacherCriticalDimension_maximum_discrepancy {a : ℝ} (ha : 0 < a) :
    Tendsto (fun n =>
      lowerCoordinateCDF 1 n (normalMaxThreshold (rademacherCriticalDimension a n))^
        (rademacherCriticalDimension a n) - Real.exp (-1))
      atTop (𝓝 (rademacherCriticalDiscrepancy a)) :=
  tendsto_rademacherCritical_maximum_discrepancy ha
    (tendsto_log_rademacherCriticalDimension_div_sqrt ha)

end

end RectangleCLT.Companion
