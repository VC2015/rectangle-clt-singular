import RectangleCLT.GlobalDerivativeHermite
import RectangleCLT.GaussianFourthStability
import RectangleCLT.GaussianFourthSupCounting

/-! Positive full-dual score moments for actual Gaussian derivatives.
The full eigenvalue enters through the score variance. No Gaussian
derivative bound or central limit estimate is assumed in these lemmas. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem integrable_fullGaussianScorePolynomial {p : ℕ}
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (k : ℕ) :
    Integrable (fun z => (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k)
      (standardGaussian p) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  let rows : Fin p → Fin p → ℝ := fun j l => Real.sqrt ν * fullGaussianDual A j l
  let R : Vector p → ℝ := fun z => ‖normalizedFullGaussianScoreFamily A ν z‖
  have hRm : Measurable R := (measurable_linearProjectionFamily rows).norm
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from hp)
  have hcard : 2 * (p : ℝ) ≤ Real.exp (2 * dimensionLog p) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
    calc
      2 * (p : ℝ) ≤ Real.exp 1 * (p : ℝ) := mul_le_mul_of_nonneg_right he hp₀.le
      _ = Real.exp (dimensionLog p) := by
        rw [dimensionLog, Real.exp_log (mul_pos (Real.exp_pos 1) hp₀)]
      _ ≤ Real.exp (2 * dimensionLog p) := Real.exp_le_exp.mpr (by linarith)
  have hh := projectionMaximum_weighted_moment_le rows
    (normalized_fullGaussianDual_normSq_le_one A hν hlower) R hRm
    (fun z => norm_nonneg _) hL (by simpa only [Fintype.card_fin] using hcard)
    (d := 1) (by intro z; exact le_of_eq (by simp only [R, rows,
      normalizedFullGaussianScoreFamily, one_mul])) le_rfl k
  apply hh.1.mono' ((measurable_const.add hRm).pow_const k).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (by positivity) k)]
    exact le_mul_of_one_le_left (pow_nonneg (by positivity) k)
      (Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _)
        (Real.sqrt_nonneg _)))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The positive full-score moment has no active Gram determinant. -/
def fullDualGaussianSoftFaceMoment (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (x : Vector p) (S : Finset (Face p)) (k : ℕ) : ℝ :=
  ∫ z, (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k *
    s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p

theorem fullDualGaussianSoftFaceMoment_nonneg
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p)
    (S : Finset (Face p)) (k : ℕ) :
    0 ≤ s.fullDualGaussianSoftFaceMoment A ν x S k :=
  integral_nonneg fun z => mul_nonneg (pow_nonneg (by positivity) k)
    (s.softFaceWeight_nonneg S _)

theorem integrable_fullDualGaussianSoftFaceMoment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (k : ℕ) :
    Integrable (fun z => (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k *
      s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
  simpa only [mul_comm] using
    (integrable_fullGaussianScorePolynomial hp A hν hlower k).bdd_mul
      (s.integrable_softFaceWeight_gaussian A S x).aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩

@[simp] theorem fullDualGaussianSoftFaceMoment_zero
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (x : Vector p) (S : Finset (Face p)) :
    s.fullDualGaussianSoftFaceMoment A ν x S 0 =
      ∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p := by
  simp only [fullDualGaussianSoftFaceMoment, pow_zero, one_mul]

theorem fullDualGaussianSoftFaceMoment_mono (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) {j k : ℕ} (hjk : j ≤ k) :
    s.fullDualGaussianSoftFaceMoment A ν x S j ≤
      s.fullDualGaussianSoftFaceMoment A ν x S k := by
  apply integral_mono
    (s.integrable_fullDualGaussianSoftFaceMoment hp A hν hlower x S j)
    (s.integrable_fullDualGaussianSoftFaceMoment hp A hν hlower x S k)
  intro z
  exact mul_le_mul_of_nonneg_right
    (pow_le_pow_right₀ (le_add_of_nonneg_right
      (norm_nonneg (normalizedFullGaussianScoreFamily A ν z))) hjk)
    (s.softFaceWeight_nonneg S _)

theorem fullDualGaussianSoftFaceMoment_shift_le_exp_nine (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (hS : S.card ≤ 4) (k : ℕ)
    {z : Vector p} {r : ℝ} (hz : ‖z‖ ≤ r) (hr : r ≤ s.bandwidth) :
    s.fullDualGaussianSoftFaceMoment A ν (x + z) S k ≤
      Real.exp 9 * s.fullDualGaussianSoftFaceMoment A ν x S k := by
  unfold fullDualGaussianSoftFaceMoment
  rw [← integral_const_mul]
  apply integral_mono
    (s.integrable_fullDualGaussianSoftFaceMoment hp A hν hlower (x + z) S k)
    ((s.integrable_fullDualGaussianSoftFaceMoment hp A hν hlower x S k).const_mul _)
  intro w
  have hh := mul_le_mul_of_nonneg_left
    (s.softFaceWeight_shift_le_exp_nine S hS (A.mulVec w + x) hz hr)
    (pow_nonneg (by positivity : 0 ≤ 1 +
      ‖normalizedFullGaussianScoreFamily A ν w‖) k)
  simpa only [add_assoc, mul_left_comm] using hh

/-- Products of any finite number of actual full-dual Gaussian scores are
controlled by one positive score maximum moment, before any summation over
faces or coordinate indices. -/
theorem abs_fullDual_score_product_integral_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (k : ℕ) (j : Fin k → Fin p) :
    |∫ z, (∏ i, faceDot (fullGaussianDual A (j i)) z) *
      s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p| ≤
      (Real.sqrt ν)⁻¹ ^ k * s.fullDualGaussianSoftFaceMoment A ν x S k := by
  let D := (Real.sqrt ν)⁻¹
  have hD : 0 ≤ D := inv_nonneg.mpr (Real.sqrt_nonneg ν)
  have hpoint (z : Vector p) :
      |(∏ i, faceDot (fullGaussianDual A (j i)) z) *
          s.softFaceWeight S (A.mulVec z + x)| ≤
        D ^ k * ((1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k *
          s.softFaceWeight S (A.mulVec z + x)) := by
    have hrow (i : Fin k) : |faceDot (fullGaussianDual A (j i)) z| ≤
        D * (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) := by
      calc
        _ ≤ ‖normalizedFullGaussianScoreFamily A ν z‖ / Real.sqrt ν :=
          abs_faceDot_fullGaussianDual_le_scoreMaximum A hν z (j i)
        _ ≤ _ := by
          dsimp only [D]
          rw [div_eq_mul_inv, mul_comm _ (Real.sqrt ν)⁻¹]
          exact mul_le_mul_of_nonneg_left (by linarith) hD
    rw [abs_mul, Finset.abs_prod, abs_of_nonneg (s.softFaceWeight_nonneg S _)]
    have hh := Finset.prod_le_prod (s := Finset.univ) (fun i _ => abs_nonneg
      (faceDot (fullGaussianDual A (j i)) z)) (fun i _ => hrow i)
    have heq : (∏ _i : Fin k, D * (1 + ‖normalizedFullGaussianScoreFamily A ν z‖)) =
        D ^ k * (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k := by
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, mul_pow]
    rw [heq] at hh
    exact (mul_le_mul_of_nonneg_right hh (s.softFaceWeight_nonneg S _)).trans_eq (by ring)
  have hmajor : Integrable (fun z => D ^ k *
      ((1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k *
        s.softFaceWeight S (A.mulVec z + x))) (standardGaussian p) :=
    (s.integrable_fullDualGaussianSoftFaceMoment hp A hν hlower x S k).const_mul _
  calc
    _ ≤ ∫ z, |(∏ i, faceDot (fullGaussianDual A (j i)) z) *
        s.softFaceWeight S (A.mulVec z + x)| ∂standardGaussian p :=
      abs_integral_le_integral_abs
    _ ≤ ∫ z, D ^ k * ((1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k *
        s.softFaceWeight S (A.mulVec z + x)) ∂standardGaussian p := by
      apply integral_mono_of_nonneg (ae_of_all _ (fun _ => abs_nonneg _)) hmajor
      exact ae_of_all _ hpoint
    _ = _ := by rw [integral_const_mul]; rfl

theorem abs_softFaceDirectional_fullDual_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (j : Fin p) :
    |∫ z, s.softFaceDirectional S (coordinateDirection j) (A.mulVec z + x)
      ∂standardGaussian p| ≤
      (Real.sqrt ν)⁻¹ * s.fullDualGaussianSoftFaceMoment A ν x S 1 := by
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  rw [s.softFaceDirectional_gaussian_fullDual A hd S j x]
  have hh := s.abs_fullDual_score_product_integral_le hp A hν hlower x S 1
    (fun _ => j)
  simpa only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, pow_one] using hh

theorem abs_softFaceCoordinateSecond_fullDual_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) :
    |∫ z, s.softFaceCoordinateSecond S j (A.mulVec z + x) ∂standardGaussian p| ≤
      2 * (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  have hD2 : (Real.sqrt ν)⁻¹ ^ 2 = 1 / ν := by
    rw [inv_pow, Real.sq_sqrt hν.le, one_div]
  have hI := s.abs_fullDual_score_product_integral_le hp A hν hlower x S 2
    (fun _ => j)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hI
  have hI' : |∫ z, faceDot (fullGaussianDual A j) z *
      (faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x))
      ∂standardGaussian p| ≤
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
    simpa only [mul_assoc] using hI
  have hcov := abs_faceDot_fullGaussianDual_le_inv A hν hlower j j
  have hM0 := s.fullDualGaussianSoftFaceMoment_mono hp A hν hlower x S
    (by decide : 0 ≤ 2)
  have hM0non := s.fullDualGaussianSoftFaceMoment_nonneg A ν x S 0
  have hterm : |faceDot (fullGaussianDual A j) (fullGaussianDual A j)| *
      s.fullDualGaussianSoftFaceMoment A ν x S 0 ≤
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
    rw [hD2]
    exact mul_le_mul hcov hM0 hM0non (one_div_nonneg.mpr hν.le)
  rw [s.softFaceCoordinateSecond_gaussian_fullDual A hd S j hj x]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, ← s.fullDualGaussianSoftFaceMoment_zero A ν x S,
    abs_of_nonneg hM0non]
  calc
    _ ≤ (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 +
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 :=
      add_le_add hI' hterm
    _ = _ := by ring

theorem abs_softFaceMixedSecond_fullDual_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (j k : Fin p)
    (hj : j ∈ S.image Prod.fst) (hk : k ∈ S.image Prod.fst) :
    |∫ z, s.softFaceMixedSecond S j k (A.mulVec z + x) ∂standardGaussian p| ≤
      2 * (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  have hD2 : (Real.sqrt ν)⁻¹ ^ 2 = 1 / ν := by
    rw [inv_pow, Real.sq_sqrt hν.le, one_div]
  have hI := s.abs_fullDual_score_product_integral_le hp A hν hlower x S 2 ![k, j]
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, Matrix.cons_val_zero,
    Matrix.cons_val_succ, mul_one] at hI
  have hI' : |∫ z, faceDot (fullGaussianDual A k) z *
      (faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x))
      ∂standardGaussian p| ≤
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
    simpa only [mul_assoc] using hI
  have hcov := abs_faceDot_fullGaussianDual_le_inv A hν hlower k j
  have hM0 := s.fullDualGaussianSoftFaceMoment_mono hp A hν hlower x S
    (by decide : 0 ≤ 2)
  have hM0non := s.fullDualGaussianSoftFaceMoment_nonneg A ν x S 0
  have hterm : |faceDot (fullGaussianDual A k) (fullGaussianDual A j)| *
      s.fullDualGaussianSoftFaceMoment A ν x S 0 ≤
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 := by
    rw [hD2]
    exact mul_le_mul hcov hM0 hM0non (one_div_nonneg.mpr hν.le)
  rw [s.softFaceMixedSecond_gaussian_fullDual A hd S j k hj hk x]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, ← s.fullDualGaussianSoftFaceMoment_zero A ν x S,
    abs_of_nonneg hM0non]
  calc
    _ ≤ (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 +
        (Real.sqrt ν)⁻¹ ^ 2 * s.fullDualGaussianSoftFaceMoment A ν x S 2 :=
      add_le_add hI' hterm
    _ = _ := by ring

theorem abs_softFaceCoordinateThird_fullDual_le_moment (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (x : Vector p) (S : Finset (Face p)) (j : Fin p)
    (hj : j ∈ S.image Prod.fst) :
    |∫ z, s.softFaceCoordinateThird S j (A.mulVec z + x) ∂standardGaussian p| ≤
      4 * (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 3 := by
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  have hD2 : (Real.sqrt ν)⁻¹ ^ 2 = 1 / ν := by
    rw [inv_pow, Real.sq_sqrt hν.le, one_div]
  have hI := s.abs_fullDual_score_product_integral_le hp A hν hlower x S 3
    (fun _ => j)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one] at hI
  have hI' : |∫ z, faceDot (fullGaussianDual A j) z *
      (faceDot (fullGaussianDual A j) z * (faceDot (fullGaussianDual A j) z *
        s.softFaceWeight S (A.mulVec z + x))) ∂standardGaussian p| ≤
      (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 3 := by
    simpa only [mul_assoc] using hI
  have hI1 := s.abs_fullDual_score_product_integral_le hp A hν hlower x S 1
    (fun _ => j)
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one, pow_one] at hI1
  have hcov := abs_faceDot_fullGaussianDual_le_inv A hν hlower j j
  have hM1 := s.fullDualGaussianSoftFaceMoment_mono hp A hν hlower x S
    (by decide : 1 ≤ 3)
  have hM1non := s.fullDualGaussianSoftFaceMoment_nonneg A ν x S 1
  have hterm : 3 * |faceDot (fullGaussianDual A j) (fullGaussianDual A j)| *
      |∫ z, faceDot (fullGaussianDual A j) z * s.softFaceWeight S (A.mulVec z + x)
        ∂standardGaussian p| ≤
      3 * (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 3 := by
    calc
      _ ≤ 3 * (Real.sqrt ν)⁻¹ ^ 2 * ((Real.sqrt ν)⁻¹ *
          s.fullDualGaussianSoftFaceMoment A ν x S 1) := by
        apply mul_le_mul
        · exact mul_le_mul_of_nonneg_left (by simpa only [hD2] using hcov) (by norm_num)
        · exact hI1
        · exact abs_nonneg _
        · positivity
      _ = 3 * (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 1 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hM1 (by positivity)
  rw [s.softFaceCoordinateThird_gaussian_fullDual A hd S j hj x]
  refine (abs_sub _ _).trans ?_
  rw [abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  calc
    _ ≤ (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 3 +
        3 * (Real.sqrt ν)⁻¹ ^ 3 * s.fullDualGaussianSoftFaceMoment A ν x S 3 :=
      add_le_add hI' hterm
    _ = _ := by ring

end FaceSmoother

end

end RectangleCLT
