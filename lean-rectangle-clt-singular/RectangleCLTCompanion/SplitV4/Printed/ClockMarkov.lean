import RectangleCLTCompanion.SplitV4.Printed.ClockMean
import Mathlib.Probability.Moments.Basic

/-! The printed expectation-to-Markov transition for the genuine maximum
random-threshold radius, separate from the older direct clock cutoff. -/
open MeasureTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def expectedClockCutoff (p : ℕ) (h : ℝ) : ℝ := 16*h*dimensionLog p

theorem randomThresholdRadius_nonneg {p : ℕ} {h : ℝ} (hh : 0 ≤ h)
    (e : ℝ × (Face p → ℝ)) : 0 ≤ randomThresholdRadius p h e :=
  mul_nonneg hh (clockLogMaximum_nonneg p e)

theorem measurable_randomThresholdRadius (p : ℕ) (h : ℝ) :
    Measurable (randomThresholdRadius p h) := (measurable_clockLogMaximum p).const_mul h

theorem expectedClockCutoff_pos {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 < h) :
    0 < expectedClockCutoff p h :=
  mul_pos (mul_pos (by norm_num) hh) (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp))

theorem randomThresholdRadius_markov {p : ℕ} (hp : 1 ≤ p) {h d : ℝ}
    (hh : 0 ≤ h) (hd : 0 < d) :
    (exponentialRectangleLaw p).real {e | d < randomThresholdRadius p h e} ≤
      (∫ e, randomThresholdRadius p h e ∂exponentialRectangleLaw p)/d := by
  have hm := mul_meas_ge_le_integral_of_nonneg
    (ae_of_all _ (randomThresholdRadius_nonneg hh)) (integrable_randomThresholdRadius hp h) d
  have hsub : (exponentialRectangleLaw p).real {e | d < randomThresholdRadius p h e} ≤
      (exponentialRectangleLaw p).real {e | d ≤ randomThresholdRadius p h e} := by
    have hset : {e : ℝ × (Face p → ℝ) | d < randomThresholdRadius p h e} ⊆
        {e : ℝ × (Face p → ℝ) | d ≤ randomThresholdRadius p h e} := by
      intro e he
      change d < randomThresholdRadius p h e at he
      change d ≤ randomThresholdRadius p h e
      exact le_of_lt he
    exact measureReal_mono hset
  apply (le_div_iff₀ hd).mpr
  nlinarith [mul_le_mul_of_nonneg_left hsub hd.le]

theorem expectedClockCutoff_bad_le {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 < h) :
    (exponentialRectangleLaw p).real
      {e | expectedClockCutoff p h < randomThresholdRadius p h e} ≤ 1/4 := by
  have hm := randomThresholdRadius_markov hp hh.le (expectedClockCutoff_pos hp hh)
  have hmean := integral_randomThresholdRadius_le_log hp hh.le
  apply hm.trans
  apply (div_le_iff₀ (expectedClockCutoff_pos hp hh)).mpr
  dsimp [expectedClockCutoff]
  nlinarith

theorem expectedClockCutoff_add_mean_le {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 ≤ h) :
    expectedClockCutoff p h+(∫ e, randomThresholdRadius p h e ∂exponentialRectangleLaw p) ≤
      20*h*dimensionLog p := by
  have hm := integral_randomThresholdRadius_le_log hp hh
  dsimp [expectedClockCutoff]
  nlinarith

end
end RectangleCLT.Companion.SplitV4.Printed
