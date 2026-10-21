import RectangleCLTCompanion.RademacherCumulants

/-! # Exact Esscher parameters for a Rademacher observation -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

lemma rademacherTiltParameter_pos {u : ℝ} (hu : u ∈ Ioo (0 : ℝ) 1) :
    0 < rademacherTiltParameter u := by
  unfold rademacherTiltParameter
  have hp := Real.log_pos (show 1 < 1+u by linarith [hu.1])
  have hm := Real.log_neg (show 0 < 1-u by linarith [hu.2])
    (show 1-u < 1 by linarith [hu.1])
  linarith

lemma exp_two_rademacherTiltParameter {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Real.exp (2 * rademacherTiltParameter u) = (1+u)/(1-u) := by
  have hp : 0 < 1+u := by linarith [hu.1]
  have hm : 0 < 1-u := by linarith [hu.2]
  rw [show 2*rademacherTiltParameter u = Real.log (1+u)-Real.log (1-u) by
    unfold rademacherTiltParameter; ring, Real.exp_sub, Real.exp_log hp, Real.exp_log hm]

lemma lowerTiltProbability_rademacher {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    lowerTiltProbability 1 (rademacherTiltParameter u) = (1+u)/2 := by
  let t := rademacherTiltParameter u
  have hm : 1-u ≠ 0 := by linarith [hu.2]
  have he2 : (1-u) * (Real.exp t)^2 = 1+u := by
    have hh := exp_two_rademacherTiltParameter hu
    rw [show 2*rademacherTiltParameter u = t+t by dsimp [t]; ring, Real.exp_add] at hh
    have he := (eq_div_iff hm).mp hh
    nlinarith [he]
  have heinv : Real.exp t * Real.exp (-t) = 1 := by
    rw [← Real.exp_add]
    simp
  unfold lowerTiltProbability lowerTiltNormalizer
  simp only [one_pow, mul_one, one_mul, inv_one, mul_neg_one]
  apply (div_eq_iff (by positivity : Real.exp t + Real.exp (-t) ≠ 0)).mpr
  apply (mul_right_cancel₀ (Real.exp_ne_zero t))
  have hpoly : Real.exp t * Real.exp t = ((1+u)/2 * (Real.exp t + Real.exp (-t))) * Real.exp t := by
    calc
      _ = (1+u)/2 * ((Real.exp t)^2 + 1) := by nlinarith [he2]
      _ = _ := by rw [← heinv]; ring
  exact hpoly

lemma lowerTiltMean_rademacher {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    lowerTiltMean 1 (rademacherTiltParameter u) = u := by
  unfold lowerTiltMean
  rw [lowerTiltProbability_rademacher hu]
  norm_num
  ring

lemma lowerTiltVariance_rademacher {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    lowerTiltVariance 1 (rademacherTiltParameter u) = 1-u^2 := by
  unfold lowerTiltVariance
  rw [lowerTiltProbability_rademacher hu]
  norm_num
  ring

lemma rademacher_mgf_tilt {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    mgf id (lowerTwoPointLaw 1) (rademacherTiltParameter u) =
      Real.exp (rademacherTiltParameter u)/(1+u) := by
  rw [lowerTwoPointLaw_mgf]
  have hp : 1+u ≠ 0 := by linarith [hu.1]
  have hq := lowerTiltProbability_rademacher hu
  unfold lowerTiltProbability at hq
  have hn := (lowerTiltNormalizer_pos 1 (rademacherTiltParameter u)).ne'
  norm_num only [one_pow] at *
  field_simp at hq ⊢
  nlinarith

lemma log_rademacher_mgf_tilt {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Real.log (mgf id (lowerTwoPointLaw 1) (rademacherTiltParameter u)) =
      rademacherTiltParameter u - Real.log (1+u) := by
  rw [rademacher_mgf_tilt hu, Real.log_div (Real.exp_ne_zero _) (by linarith [hu.1]), Real.log_exp]

lemma rademacher_esscher_exponent {u : ℝ} (hu : u ∈ Ioo (-1 : ℝ) 1) :
    Real.log (mgf id (lowerTwoPointLaw 1) (rademacherTiltParameter u)) -
      rademacherTiltParameter u * u = -rademacherRateFunction u := by
  rw [log_rademacher_mgf_tilt hu, rademacherRateFunction_legendre]
  ring

end

end RectangleCLT.Companion
