import RectangleCLT.GaussianTubeFaceBounds

/-! One explicit constant for all fourth-order Gaussian soft-face moments.
These bounds cover every compatible active tuple, with the exact factorial
normalization supplied by the actual augmented tubes. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

def fourthFaceConstant : ℝ := 4096 * Real.exp 208

theorem fourthFaceConstant_pos : 0 < fourthFaceConstant := by
  unfold fourthFaceConstant
  positivity

theorem fourth_face_scalar_bound {L : ℝ} (hL : 0 ≤ L) {q k : ℕ}
    (hq : q ≤ 4) (hqk : q + k = 4) :
    (2 : ℝ) ^ k * (q : ℝ) ^ q * (Real.sqrt L) ^ (q + k) *
      Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) ≤ fourthFaceConstant * L ^ 2 := by
  have hk : k ≤ 4 := by omega
  have htwo : (2 : ℝ) ^ k ≤ 16 := by
    exact (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hk).trans_eq (by norm_num)
  have hqreal : (q : ℝ) ≤ 4 := by exact_mod_cast hq
  have hqpow : (q : ℝ) ^ q ≤ 256 :=
    ((pow_le_pow_left₀ (Nat.cast_nonneg q) hqreal q).trans
      (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 4) hq)).trans_eq (by norm_num)
  have hprod : (2 : ℝ) ^ k * (q : ℝ) ^ q ≤ 4096 :=
    (mul_le_mul htwo hqpow (pow_nonneg (Nat.cast_nonneg q) q) (by norm_num)).trans_eq (by norm_num)
  have hkreal : (k : ℝ) ≤ 4 := by exact_mod_cast hk
  have he : Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) ≤ Real.exp 208 := by
    apply Real.exp_le_exp.mpr
    have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    nlinarith [mul_nonneg (sub_nonneg.mpr hkreal) (show (0 : ℝ) ≤ 6 + k by linarith)]
  have hp : (Real.sqrt L) ^ (q + k) = L ^ 2 := by
    rw [hqk, show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt hL]
  rw [hp]
  calc
    _ = ((2 : ℝ) ^ k * (q : ℝ) ^ q *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2)) * L ^ 2 := by ring
    _ ≤ (4096 * Real.exp 208) * L ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul hprod he (Real.exp_nonneg _) (by norm_num)) (sq_nonneg L)
    _ = _ := rfl

theorem sum_ordered_fourth_faceMoment_le {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {a₄ : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (k : ℕ) (hqk : q + k = 4) :
    (∑ S : OrderedFaceTuples s.faces q, faceMoment S.val s A r k) ≤
      fourthFaceConstant * (dimensionLog p) ^ 2 := by
  rw [sum_ordered_faceMoment_eq_factorial]
  have hd (T : CompatibleFaceSets s.faces q) :=
    normalMatrix_gram_det_isUnit (compatibleSetTuple T) A (hQ.mono hq) ha₄
  have hh := sum_faceMoment_le s A r hp hq0 hq (by norm_num : (0 : ℝ) < 1) hdiag hd k
  simp only [Real.sqrt_one, one_pow, mul_one] at hh
  exact hh.trans (fourth_face_scalar_bound (L := dimensionLog p)
    (le_trans zero_le_one (log_exp_mul_nat_ge_one hp)) hq hqk)

/-- Localized fourth-order ordered face moments for a genuine bounded
independent base. The covariance lower bound is tested only on at most four
coordinates of the Gaussian factor. -/
theorem sum_ordered_fourth_shiftedFaceMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n q : ℕ} {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hq0 : 0 < q) (hq : q ≤ 4) {a₄ : ℝ}
    (hQ : LocalCovarianceLower (A * A.transpose) 4 a₄) (ha₄ : 0 < a₄)
    (hA : ∀ j, (A * A.transpose) j j = 1) (k : ℕ) (hqk : q + k = 4) :
    (∑ S : OrderedFaceTuples s.faces q,
      shiftedFaceMoment μ S.val s A (sumVector ξ) k) ≤
      fourthFaceConstant * 1073741824 * (dimensionLog p) ^ 2 *
        (1 + η * Real.sqrt (dimensionLog p)) / Real.sqrt v := by
  rw [sum_ordered_shiftedFaceMoment_eq_factorial]
  have hd (T : CompatibleFaceSets s.faces q) :=
    normalMatrix_gram_det_isUnit (compatibleSetTuple T) A (hQ.mono hq) ha₄
  have hh := sum_shiftedFaceMoment_le h hp hv hdiag s A (by norm_num : (0 : ℝ) < 1) hA
    hq0 hq hd k
  simp only [Real.sqrt_one, one_pow, mul_one] at hh
  have hfactor : 0 ≤ 1073741824 * (1 + η * Real.sqrt (dimensionLog p)) / Real.sqrt v :=
    div_nonneg (mul_nonneg (by norm_num)
      (by nlinarith [mul_nonneg h.delta_nonneg (Real.sqrt_nonneg (dimensionLog p))])) (Real.sqrt_nonneg v)
  have hscalar := mul_le_mul_of_nonneg_right
    (fourth_face_scalar_bound (L := dimensionLog p)
      (le_trans zero_le_one (log_exp_mul_nat_ge_one hp)) hq hqk) hfactor
  apply hh.trans
  convert hscalar using 1 <;> ring

end
end RectangleCLT.GaussianTube
