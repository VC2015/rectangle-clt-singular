import RectangleCLTCompanion.LowerTiltTaylorEstimates
import Mathlib.Topology.Order.IntermediateValue

/-! The tilt parameter is solved from the actual mean, with quantitative
bounds uniform in the envelope. No saddlepoint root is assumed. -/

open Set

namespace RectangleCLT.Companion

noncomputable section

lemma lowerTilt_small_exp {B u : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1) {t : ℝ} (ht : t ≤ 2 * u) :
    Real.exp (2 * B * t) ≤ Real.exp 4 := by
  have he : 1 ≤ Real.exp (4 : ℝ) := Real.one_le_exp (by norm_num)
  have hBu : 0 ≤ B * u := mul_nonneg (by linarith) hu
  have hBu1 : B * u ≤ 1 := by nlinarith
  apply Real.exp_le_exp.mpr
  have hBt := mul_le_mul_of_nonneg_left ht (by linarith : (0 : ℝ) ≤ 2 * B)
  nlinarith

lemma exists_lowerTiltMean_eq {B u : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1) :
    ∃ t ∈ Icc (0 : ℝ) (2 * u), lowerTiltMean B t = u := by
  have hBp : 0 < B := by linarith
  have he := lowerTilt_small_exp hB hu hsmall (le_rfl : 2*u ≤ 2*u)
  have hm := (lowerTiltMean_sub_self hB (by positivity : 0 ≤ 2*u)).trans
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left he (by positivity)) (sq_nonneg (2*u)))
  have hmlo := (abs_le.mp hm).1
  have hupp : u ≤ lowerTiltMean B (2*u) := by
    have hh := mul_le_mul_of_nonneg_right hsmall hu
    nlinarith [Real.exp_pos (4 : ℝ)]
  have hcont : Continuous (lowerTiltMean B) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_lowerTiltMean B t).continuousAt)
  exact intermediate_value_Icc (by linarith) hcont.continuousOn
    ⟨by simpa only [lowerTiltMean_zero hBp.ne'] using hu, hupp⟩

noncomputable def lowerInverseTilt (B u : ℝ) : ℝ := by
  classical
  exact if h : ∃ t ∈ Icc (0 : ℝ) (2*u), lowerTiltMean B t = u then Classical.choose h else 0

lemma lowerInverseTilt_spec {B u : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1) :
    lowerInverseTilt B u ∈ Icc (0 : ℝ) (2*u) ∧
      lowerTiltMean B (lowerInverseTilt B u) = u := by
  classical
  have hh := exists_lowerTiltMean_eq hB hu hsmall
  rw [lowerInverseTilt, dif_pos hh]
  exact Classical.choose_spec hh

lemma lowerTiltMean_root_sub_self {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (2*u)) (hroot : lowerTiltMean B t = u) :
    |t-u| ≤ 8 * Real.exp 4 * B * u^2 := by
  have he := lowerTilt_small_exp hB hu hsmall ht.2
  have hm := (lowerTiltMean_sub_self hB ht.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left he (by linarith : (0 : ℝ) ≤ 2*B))
      (pow_le_pow_left₀ ht.1 ht.2 2) (sq_nonneg t) (by positivity))
  rw [hroot, abs_sub_comm] at hm
  convert hm using 1 <;> ring

lemma lowerTiltMean_root_variance_bounds {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (2*u)) :
    |lowerTiltVariance B t - 1| ≤ 4 * Real.exp 4 * B * u ∧
      1/2 ≤ lowerTiltVariance B t ∧ lowerTiltVariance B t ≤ 3/2 := by
  have he := lowerTilt_small_exp hB hu hsmall ht.2
  have hv := (lowerTiltVariance_sub_one hB ht.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left he (by linarith : (0 : ℝ) ≤ 2*B))
      ht.2 ht.1 (by positivity))
  have hv' : |lowerTiltVariance B t - 1| ≤ 4 * Real.exp 4 * B * u := by
    convert hv using 1 <;> ring
  refine ⟨hv', ?_, ?_⟩ <;> have hh := abs_le.mp hv' <;> nlinarith

lemma lowerTiltMean_root_sqrtVariance {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (2*u)) (hroot : lowerTiltMean B t = u) :
    |t * Real.sqrt (lowerTiltVariance B t) - u| ≤ 16 * Real.exp 4 * B * u^2 := by
  have hBp : 0 < B := by linarith
  have hv0 := (lowerTiltVariance_pos hBp t).le
  have hsd : |Real.sqrt (lowerTiltVariance B t) - 1| ≤ |lowerTiltVariance B t - 1| := by
    have hh : (Real.sqrt (lowerTiltVariance B t) - 1) *
        (Real.sqrt (lowerTiltVariance B t) + 1) = lowerTiltVariance B t - 1 := by
      nlinarith [Real.sq_sqrt hv0]
    calc
      _ ≤ |Real.sqrt (lowerTiltVariance B t) - 1| *
          (Real.sqrt (lowerTiltVariance B t) + 1) :=
        le_mul_of_one_le_right (abs_nonneg _) (by linarith [Real.sqrt_nonneg (lowerTiltVariance B t)])
      _ = _ := by rw [← abs_of_nonneg (by positivity : 0 ≤ Real.sqrt (lowerTiltVariance B t) + 1),
        ← abs_mul, hh]
  have hv := (lowerTiltMean_root_variance_bounds hB hu hsmall ht).1
  have hm := lowerTiltMean_root_sub_self hB hu hsmall ht hroot
  calc
    _ = |(t-u) + t * (Real.sqrt (lowerTiltVariance B t) - 1)| := by congr 1; ring
    _ ≤ |t-u| + |t * (Real.sqrt (lowerTiltVariance B t) - 1)| := abs_add _ _
    _ ≤ 8 * Real.exp 4 * B * u^2 + 2*u * (4 * Real.exp 4 * B * u) := by
      rw [abs_mul, abs_of_nonneg ht.1]
      exact add_le_add hm (mul_le_mul ht.2 (hsd.trans hv) (abs_nonneg _) (by positivity))
    _ = _ := by ring

lemma lowerTiltMean_root_pos {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 < u)
    (ht : 0 ≤ t) (hroot : lowerTiltMean B t = u) : 0 < t := by
  apply lt_of_le_of_ne ht
  intro hh
  have hBp : 0 < B := by linarith
  rw [← hh, lowerTiltMean_zero hBp.ne'] at hroot
  linarith

def lowerInverseRemainderConstant : ℝ := 1000 * (1 + Real.exp 4)^2

lemma lowerInverseRemainderConstant_pos : 0 < lowerInverseRemainderConstant := by
  unfold lowerInverseRemainderConstant
  positivity

lemma lowerTiltMean_root_cgf {B u t : ℝ} (hB : 1 ≤ B) (hu : 0 ≤ u)
    (hsmall : 100 * Real.exp 4 * (B * u) ≤ 1)
    (ht : t ∈ Icc (0 : ℝ) (2*u)) (hroot : lowerTiltMean B t = u) :
    |ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t*u + u^2/2 -
      (B-B⁻¹)*u^3/6| ≤ lowerInverseRemainderConstant * B^2 * u^4 := by
  have hBp : 0 < B := by linarith
  have ht0 : 0 ≤ t := ht.1
  have he := lowerTilt_small_exp hB hu hsmall ht.2
  have hm := lowerTiltMean_root_sub_self hB hu hsmall ht hroot
  have hE : 0 ≤ Real.exp (4 : ℝ) := (Real.exp_pos _).le
  have hk0 : 0 ≤ B-B⁻¹ := by
    have hh := (inv_le_one_of_one_le₀ hB).trans hB
    linarith
  have hkB : |B-B⁻¹| ≤ B := by rw [abs_of_nonneg hk0]; linarith [inv_pos.mpr hBp]
  have hc := (lowerTwoPointLaw_cgf_cubic hB ht.1).trans
    (mul_le_mul (mul_le_mul_of_nonneg_left he (by positivity : 0 ≤ 4*B^2))
      (pow_le_pow_left₀ ht.1 ht.2 4) (pow_nonneg ht.1 4) (by positivity))
  have hc' : |ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t^2/2 -
      (B-B⁻¹)*t^3/6| ≤ 64 * Real.exp 4 * B^2 * u^4 := by
    convert hc using 1 <;> ring
  have hs : (t-u)^2 ≤ 64 * (Real.exp 4)^2 * B^2 * u^4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hm 2
    simpa only [sq_abs] using hh.trans_eq (by ring)
  have hcube : |t^3-u^3| ≤ 56 * Real.exp 4 * B * u^4 := by
    have hfac : |t^3-u^3| = |t-u| * |t^2+t*u+u^2| := by
      rw [← abs_mul]
      congr 1
      ring
    rw [hfac, abs_of_nonneg (by positivity : 0 ≤ t^2+t*u+u^2)]
    have hsq2 : t^2 ≤ 4*u^2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr ht.2) (by positivity : 0 ≤ 2*u+t)]
    have hh : t^2+t*u+u^2 ≤ 7*u^2 := by
      nlinarith [mul_le_mul_of_nonneg_right ht.2 hu]
    exact (mul_le_mul hm hh (by positivity) (by positivity)).trans_eq (by ring)
  have hkterm : |(B-B⁻¹)*(t^3-u^3)/6| ≤ (56/6 : ℝ) * Real.exp 4 * B^2 * u^4 := by
    rw [abs_div, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 6)]
    exact (div_le_div_of_nonneg_right (mul_le_mul hkB hcube (abs_nonneg _) hBp.le)
      (by norm_num)).trans_eq (by ring)
  have hsplit : ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t*u + u^2/2 -
      (B-B⁻¹)*u^3/6 =
      (ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t^2/2 - (B-B⁻¹)*t^3/6) +
      (t-u)^2/2 + (B-B⁻¹)*(t^3-u^3)/6 := by ring
  rw [hsplit]
  have hsum : |ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t^2/2 -
      (B-B⁻¹)*t^3/6 + (t-u)^2/2 + (B-B⁻¹)*(t^3-u^3)/6| ≤
      |ProbabilityTheory.cgf id (lowerTwoPointLaw B) t - t^2/2 - (B-B⁻¹)*t^3/6| +
      |(t-u)^2/2| + |(B-B⁻¹)*(t^3-u^3)/6| :=
    (abs_add _ _).trans (add_le_add_right (abs_add _ _) _)
  apply hsum.trans
  rw [abs_div, abs_of_nonneg (sq_nonneg (t-u)), abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
  have hnum : 64*Real.exp (4 : ℝ) + 32*(Real.exp 4)^2 + (56/6 : ℝ)*Real.exp 4 ≤
      lowerInverseRemainderConstant := by unfold lowerInverseRemainderConstant; nlinarith
  calc
    _ ≤ 64 * Real.exp 4 * B^2 * u^4 +
        (64*(Real.exp 4)^2*B^2*u^4)/2 + (56/6 : ℝ)*Real.exp 4*B^2*u^4 :=
      add_le_add (add_le_add hc' (div_le_div_of_nonneg_right hs (by norm_num))) hkterm
    _ = (64*Real.exp 4 + 32*(Real.exp 4)^2 + (56/6 : ℝ)*Real.exp 4) * (B^2*u^4) := by ring
    _ ≤ _ := by
      convert mul_le_mul_of_nonneg_right hnum (by positivity : 0 ≤ B^2*u^4) using 1 <;> ring

end

end RectangleCLT.Companion
