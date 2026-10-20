import RectangleCLT.SmootherStability
import RectangleCLTCompanion.Statement
import Mathlib.Analysis.SpecificLimits.Normed

/-! Exact finite selector-weight translation from Appendix B of the companion.
All identities concern the actual rational rectangle smoother. -/

open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

/-- The multiplicative exponential weight increment of one signed face. -/
def translationIncrement (f : Face p) (v : Vector p) : ℝ :=
  Real.exp (FaceSmoother.normalDot f v / s.bandwidth) - 1

/-- The normalized denominator increment, summed over the actual face family. -/
def translationZ (x v : Vector p) : ℝ :=
  ∑ f ∈ s.faces, s.pi x f * translationIncrement s f v

private theorem sum_weights_faces_eq (x : Vector p) :
    (∑ f ∈ s.faces, (s.weights x).weight f) = (s.weights x).T := by
  classical
  unfold FaceWeights.T
  apply Finset.sum_subset (Finset.subset_univ _)
  intro f _ hf
  simp only [FaceSmoother.weights, hf, if_false]

/-- Exact change of the denominator before normalization. -/
theorem translationZ_eq_denominator_difference (x v : Vector p) :
    translationZ s x v =
      ((s.weights (x + v)).T - (s.weights x).T) / (1 + (s.weights x).T) := by
  classical
  unfold translationZ translationIncrement FaceSmoother.pi FaceWeights.pi
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div]
  congr 1
  simp_rw [mul_sub, mul_one]
  rw [Finset.sum_sub_distrib, sum_weights_faces_eq]
  congr 1
  rw [← sum_weights_faces_eq s (x + v)]
  apply Finset.sum_congr rfl
  intro f _
  exact (s.weight_shift_eq f x v).symm

/-- The normalized denominator multiplier is the ratio of the actual positive
selector denominators. -/
theorem one_add_translationZ_eq_ratio (x v : Vector p) :
    1 + translationZ s x v =
      (1 + (s.weights (x + v)).T) / (1 + (s.weights x).T) := by
  rw [translationZ_eq_denominator_difference]
  field_simp [ne_of_gt (s.weights x).denominator_pos]

theorem one_add_translationZ_pos (x v : Vector p) : 0 < 1 + translationZ s x v := by
  rw [one_add_translationZ_eq_ratio]
  exact div_pos (s.weights (x + v)).denominator_pos (s.weights x).denominator_pos

/-- Translation of the actual null-face probability. -/
theorem F_translation (x v : Vector p) :
    s.F (x + v) = s.F x / (1 + translationZ s x v) := by
  rw [one_add_translationZ_eq_ratio]
  unfold FaceSmoother.F FaceWeights.F
  field_simp [ne_of_gt (s.weights x).denominator_pos,
    ne_of_gt (s.weights (x + v)).denominator_pos]

/-- Translation of every actual face probability, including omitted faces
whose normalized weight is zero. -/
theorem pi_translation (x v : Vector p) (f : Face p) :
    s.pi (x + v) f =
      s.pi x f * Real.exp (FaceSmoother.normalDot f v / s.bandwidth) /
        (1 + translationZ s x v) := by
  rw [one_add_translationZ_eq_ratio]
  unfold FaceSmoother.pi FaceWeights.pi
  rw [s.weight_shift_eq]
  field_simp [ne_of_gt (s.weights x).denominator_pos,
    ne_of_gt (s.weights (x + v)).denominator_pos]

/-- Appendix B's exact product formula. Repeated face indices are permitted;
the reciprocal power is written as division by the natural power `k+1`. -/
theorem F_mul_prod_pi_translation {k : ℕ} (faces : Fin k → Face p) (x v : Vector p) :
    s.F (x + v) * (∏ i, s.pi (x + v) (faces i)) =
      s.F x * (∏ i, s.pi x (faces i)) *
        Real.exp ((∑ i, FaceSmoother.normalDot (faces i) v) / s.bandwidth) /
          (1 + translationZ s x v) ^ (k + 1) := by
  rw [F_translation]
  simp_rw [pi_translation]
  rw [Finset.prod_div_distrib, Finset.prod_mul_distrib, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  have he : (∏ i, Real.exp (FaceSmoother.normalDot (faces i) v / s.bandwidth)) =
      Real.exp ((∑ i, FaceSmoother.normalDot (faces i) v) / s.bandwidth) := by
    rw [Finset.sum_div, Real.exp_sum]
  rw [he, pow_succ]
  field_simp [ne_of_gt (one_add_translationZ_pos s x v)]
  ring

private theorem abs_exp_sub_one_le {a R : ℝ} (ha : |a| ≤ R) :
    |Real.exp a - 1| ≤ Real.exp R - 1 := by
  apply abs_le.mpr
  constructor
  · have h₁ := Real.add_one_le_exp a
    have h₂ := Real.add_one_le_exp R
    linarith [(abs_le.mp ha).1]
  · exact sub_le_sub_right (Real.exp_le_exp.mpr (abs_le.mp ha).2) 1

/-- Every face increment obeys the same dimension-free norm bound. -/
theorem abs_translationIncrement_le {v : Vector p} {r : ℝ}
    (hv : ‖v‖ ≤ r) (f : Face p) :
    |translationIncrement s f v| ≤ Real.exp (r / s.bandwidth) - 1 := by
  apply abs_exp_sub_one_le
  rw [abs_div, abs_of_pos s.bandwidth_pos]
  exact div_le_div_of_nonneg_right (FaceSmoother.abs_normalDot_le_of_norm_le f hv)
    s.bandwidth_pos.le

/-- The total normalized increment has the same bound because the face
probabilities have mass at most one, including the omitted null face. -/
theorem abs_translationZ_le (x : Vector p) {v : Vector p} {r : ℝ}
    (hr : 0 ≤ r) (hv : ‖v‖ ≤ r) :
    |translationZ s x v| ≤ Real.exp (r / s.bandwidth) - 1 := by
  classical
  let η := Real.exp (r / s.bandwidth) - 1
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp (div_nonneg hr s.bandwidth_pos.le))
  have hpisum : (∑ f ∈ s.faces, s.pi x f) ≤ 1 := by
    have hsub : (∑ f ∈ s.faces, s.pi x f) ≤ ∑ f, s.pi x f :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
        (fun f _ _ => (s.weights x).pi_nonneg f)
    have hnorm := (s.weights x).normalization
    have hF := (s.weights x).F_pos
    exact hsub.trans (by change (∑ f, (s.weights x).pi f) ≤ 1; linarith)
  calc
    _ ≤ ∑ f ∈ s.faces, |s.pi x f * translationIncrement s f v| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ f ∈ s.faces, s.pi x f * |translationIncrement s f v| := by
      apply Finset.sum_congr rfl
      intro f _
      have hpi : 0 ≤ s.pi x f := (s.weights x).pi_nonneg f
      rw [abs_mul, abs_of_nonneg hpi]
    _ ≤ ∑ f ∈ s.faces, s.pi x f * η := by
      apply Finset.sum_le_sum
      intro f _
      exact mul_le_mul_of_nonneg_left (abs_translationIncrement_le s hv f)
        ((s.weights x).pi_nonneg f)
    _ = (∑ f ∈ s.faces, s.pi x f) * η := (Finset.sum_mul _ _ _).symm
    _ ≤ 1 * η := mul_le_mul_of_nonneg_right hpisum hη
    _ = _ := one_mul η

/-- A concrete small-radius condition gives the domain for a future
absolutely convergent reciprocal-binomial expansion. -/
theorem abs_translationZ_lt_one (x : Vector p) {v : Vector p} {r : ℝ}
    (hr : 0 ≤ r) (hv : ‖v‖ ≤ r) (hsmall : r / s.bandwidth < Real.log 2) :
    |translationZ s x v| < 1 := by
  have he := Real.exp_lt_exp.mpr hsmall
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  exact (abs_translationZ_le s x hr hv).trans_lt (by linarith)

private theorem translated_choose_eq (k ℓ : ℕ) : (k + ℓ).choose ℓ = (ℓ + k).choose k := by
  rw [Nat.add_comm k ℓ]
  exact Nat.choose_symm_add

/-- The actual reciprocal-binomial expansion in Appendix B. Its convergence
condition is discharged by the concrete norm restriction on the shift. -/
theorem hasSum_translationZ_binomial (k : ℕ) (x : Vector p) {v : Vector p} {r : ℝ}
    (hr : 0 ≤ r) (hv : ‖v‖ ≤ r) (hsmall : r / s.bandwidth < Real.log 2) :
    HasSum (fun ℓ : ℕ => (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
      translationZ s x v ^ ℓ) (1 / (1 + translationZ s x v) ^ (k + 1)) := by
  have hz := abs_translationZ_lt_one s x hr hv hsmall
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one k
    (r := -translationZ s x v) (by simpa only [norm_neg, Real.norm_eq_abs] using hz)
  have hs' : HasSum (fun ℓ : ℕ => ((ℓ + k).choose k : ℝ) * (-translationZ s x v) ^ ℓ)
      (1 / (1 + translationZ s x v) ^ (k + 1)) := by
    simpa only [sub_neg_eq_add] using hs
  convert hs' using 1
  funext ℓ
  rw [translated_choose_eq, neg_pow]
  ring

/-- Absolute convergence is quantitative: the total absolute coefficient
mass is exactly the positive reciprocal-binomial sum. -/
theorem hasSum_abs_translationZ_binomial (k : ℕ) (x : Vector p) {v : Vector p} {r : ℝ}
    (hr : 0 ≤ r) (hv : ‖v‖ ≤ r) (hsmall : r / s.bandwidth < Real.log 2) :
    HasSum (fun ℓ : ℕ => |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
      translationZ s x v ^ ℓ|) (1 / (1 - |translationZ s x v|) ^ (k + 1)) := by
  have hz := abs_translationZ_lt_one s x hr hv hsmall
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one k
    (r := |translationZ s x v|) (by simpa only [Real.norm_eq_abs, abs_abs] using hz)
  convert hs using 1
  funext ℓ
  rw [translated_choose_eq]
  have hc : (0 : ℝ) ≤ ((ℓ + k).choose k : ℝ) := Nat.cast_nonneg _
  simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, abs_of_nonneg hc, one_mul]

/-- Uniform absolute-series bound throughout the prescribed max-norm ball. -/
theorem tsum_abs_translationZ_binomial_le (k : ℕ) (x : Vector p) {v : Vector p} {r : ℝ}
    (hr : 0 ≤ r) (hv : ‖v‖ ≤ r) (hsmall : r / s.bandwidth < Real.log 2) :
    (∑' ℓ : ℕ, |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * translationZ s x v ^ ℓ|) ≤
      1 / (2 - Real.exp (r / s.bandwidth)) ^ (k + 1) := by
  rw [(hasSum_abs_translationZ_binomial s k x hr hv hsmall).tsum_eq]
  have he := Real.exp_lt_exp.mpr hsmall
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
  have hd : 0 < 2 - Real.exp (r / s.bandwidth) := sub_pos.mpr he
  have hz := abs_translationZ_le s x hr hv
  have hden : 2 - Real.exp (r / s.bandwidth) ≤ 1 - |translationZ s x v| := by linarith
  exact one_div_le_one_div_of_le (pow_pos hd (k + 1)) (pow_le_pow_left₀ hd.le hden (k + 1))

end

end RectangleCLT.Companion
