import Mathlib.Probability.Distributions.Gaussian
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic

/-! Scope check for frozen A.1, lines 1848--1852 and 1872--1877.
The displayed derivative orders must be positive. If order zero is
included, even the exact one-face standard Gaussian smoother contradicts
the averaged estimate as the positive bandwidth decreases. This file
records that counterexample; it does not modify the manuscript. -/

open MeasureTheory ProbabilityTheory

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The literal one-face formula with unit normal and zero threshold. -/
def singleFaceSmoother (h x : ℝ) : ℝ := 1/(1+Real.exp (x/h))

theorem singleFaceSmoother_pos (h x : ℝ) : 0 < singleFaceSmoother h x := by
  unfold singleFaceSmoother
  positivity

theorem singleFaceSmoother_le_one (h x : ℝ) : singleFaceSmoother h x ≤ 1 := by
  unfold singleFaceSmoother
  exact (div_le_one (by positivity)).mpr (by linarith [Real.exp_pos (x/h)])

theorem singleFaceSmoother_reflection (h x : ℝ) :
    singleFaceSmoother h x+singleFaceSmoother h (-x) = 1 := by
  unfold singleFaceSmoother
  rw [neg_div, Real.exp_neg]
  have hp := Real.exp_pos (x/h)
  field_simp
  <;> ring

theorem integrable_singleFaceSmoother (μ : Measure ℝ) [IsFiniteMeasure μ] (h : ℝ) :
    Integrable (singleFaceSmoother h) μ := by
  have hm : Measurable (singleFaceSmoother h) := by unfold singleFaceSmoother; fun_prop
  apply (integrable_const (1 : ℝ)).mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_pos (singleFaceSmoother_pos _ _)]
    exact singleFaceSmoother_le_one _ _

theorem gaussianReal_standard_reflection :
    (gaussianReal 0 1).map (fun x : ℝ => -x) = gaussianReal 0 1 := by
  simpa using (gaussianReal_map_const_mul (μ := 0) (v := 1) (-1))

/-- The left side of the asserted order-zero averaged estimate is 1/2,
for every positive bandwidth (indeed for every real bandwidth). -/
theorem integral_singleFaceSmoother_standardGaussian (h : ℝ) :
    (∫ x, singleFaceSmoother h x ∂gaussianReal 0 1) = 1/2 := by
  have hm : Measurable (singleFaceSmoother h) := by unfold singleFaceSmoother; fun_prop
  have he := integral_map (μ := gaussianReal 0 1) measurable_neg.aemeasurable hm.aestronglyMeasurable
  rw [gaussianReal_standard_reflection] at he
  have hi := integrable_singleFaceSmoother (gaussianReal 0 1) h
  have hin : Integrable (fun x => singleFaceSmoother h (-x)) (gaussianReal 0 1) := by
    have hpoint : (fun x => singleFaceSmoother h (-x)) = fun x => 1-singleFaceSmoother h x := by
      funext x
      linarith [singleFaceSmoother_reflection h x]
    rw [hpoint]
    exact (integrable_const _).sub hi
  have hs := integral_add hi hin
  simp_rw [singleFaceSmoother_reflection] at hs
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hs
  linarith

/-- No constant uniform in the positive bandwidth can give A.1's printed
averaged bound at derivative order zero. Any fixed nonnegative sqrt-log
factor can be absorbed into C, so the failure is independent of its
dimension convention. The Gaussian has centered unit face variance. -/
theorem no_uniform_zero_order_averaged_bound :
    ¬ ∃ C : ℝ, 0 ≤ C ∧ ∀ h : ℝ, 0 < h →
      (∫ x, singleFaceSmoother h x ∂gaussianReal 0 1) ≤ C*h := by
  rintro ⟨C,hC,hbound⟩
  let h := 1/(4*(C+1))
  have hh : 0 < h := by dsimp [h]; positivity
  have hb := hbound h hh
  rw [integral_singleFaceSmoother_standardGaussian] at hb
  have hd : 0 < 4*(C+1) := by positivity
  have hc : C*h < 1/2 := by
    dsimp [h]
    rw [mul_one_div, div_lt_iff₀ hd]
    linarith
  linarith

/-- The order-zero local envelope is false as well: with T=1/(C+1),
F=1/(1+T), the claimed F≤C F(1−F) fails. These are genuine positive
logistic weights, with one face and finite threshold log(C+1). -/
theorem zero_order_local_envelope_fails {C : ℝ} (hC : 0 ≤ C) :
    let F := singleFaceSmoother 1 (-Real.log (C+1))
    ¬ F ≤ C*F*(1-F) := by
  dsimp only
  have hp : 0 < C+1 := by linarith
  have hd : 0 < C+2 := by linarith
  have hf : singleFaceSmoother 1 (-Real.log (C+1)) = (C+1)/(C+2) := by
    unfold singleFaceSmoother
    rw [div_one, Real.exp_neg, Real.exp_log hp]
    field_simp [ne_of_gt hp, ne_of_gt hd]
    <;> ring
  rw [hf]
  have hh : C*((C+1)/(C+2))*(1-(C+1)/(C+2)) < (C+1)/(C+2) := by
    have hcomp : 1-(C+1)/(C+2) = 1/(C+2) := by field_simp; ring
    have hratio : C/(C+2) < 1 := (div_lt_one hd).mpr (by linarith)
    have hmul := mul_lt_mul_of_pos_left hratio (div_pos hp hd)
    rw [hcomp]
    convert hmul using 1 <;> ring
  exact not_le.mpr hh

end
end RectangleCLT.Companion.SplitV4.Printed
