import RectangleCLTCompanion.MatrixReduction
import RectangleCLT.GaussianTriple

/-! Coefficient matrices for translated-base restoration.  The second moments
are genuine Bochner-integrable moments; a covariance budget alone would not
exclude the default value of an undefined integral. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ}

/-- Fresh-array expectation of the signed rank-one coefficient matrices. -/
def restorationCoefficient (μ : Measure Ω) (Z : Fin n → Ω → Vector r)
    (c : Fin n → Ω → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∑ i, ∫ a, c i a * (Z i a j * Z i a k) ∂μ

theorem matrixQuadratic_rankOne_eq_square (z u : Vector r) :
    matrixQuadratic (rankOne z) u = (faceDot u z) ^ 2 := by
  simp only [matrixQuadratic, rankOne, faceDot, pow_two,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem restorationCoefficient_symmetric (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) :
    (restorationCoefficient μ Z c).transpose = restorationCoefficient μ Z c := by
  ext j k
  simp only [Matrix.transpose_apply, restorationCoefficient]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun a => by ring)

/-- A bounded measurable coefficient preserves the actual second moments. -/
theorem integrable_restorationCoefficient_entry (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b) (i : Fin n) (j k : Fin r) :
    Integrable (fun a => c i a * (Z i a j * Z i a k)) μ := by
  exact (hZ i j k).bdd_mul (hc i) ⟨b, fun a => by
    simpa only [Real.norm_eq_abs] using hb i a⟩

/-- Finite sums and genuine integrals commute in the quadratic form. -/
theorem matrixQuadratic_integral (μ : Measure Ω)
    (B : Ω → Matrix (Fin r) (Fin r) ℝ)
    (hB : ∀ j k, Integrable (fun a => B a j k) μ) (u : Vector r) :
    matrixQuadratic (fun j k => ∫ a, B a j k ∂μ) u =
      ∫ a, matrixQuadratic (B a) u ∂μ := by
  unfold matrixQuadratic
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      ((hB j k).const_mul (u j)).mul_const (u k)))]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ =>
    ((hB j k).const_mul (u j)).mul_const (u k))]
  simp only [integral_mul_const, integral_const_mul]

theorem integrable_faceDot_sq (μ : Measure Ω) (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun a => Z a j * Z a k) μ) (u : Vector r) :
    Integrable (fun a => (faceDot u (Z a)) ^ 2) μ := by
  have h := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      ((hZ j k).const_mul (u j)).mul_const (u k)))
  convert h using 1
  funext a
  exact (matrixQuadratic_rankOne_eq_square (Z a) u).symm

theorem integrable_weighted_faceDot_sq (μ : Measure Ω)
    (Z : Ω → Vector r) (c : Ω → ℝ) {b : ℝ}
    (hZ : ∀ j k, Integrable (fun a => Z a j * Z a k) μ)
    (hc : AEStronglyMeasurable c μ) (hb : ∀ a, |c a| ≤ b) (u : Vector r) :
    Integrable (fun a => c a * (faceDot u (Z a)) ^ 2) μ :=
  (integrable_faceDot_sq μ Z hZ u).bdd_mul hc
    ⟨b, fun a => by simpa only [Real.norm_eq_abs] using hb a⟩

/-- Exact scalar form of the coefficient matrix.  No independence between
the multiplier and the repeated direction is required. -/
theorem matrixQuadratic_restorationCoefficient (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b) (u : Vector r) :
    matrixQuadratic (restorationCoefficient μ Z c) u =
      ∑ i, ∫ a, c i a * (faceDot u (Z i a)) ^ 2 ∂μ := by
  have hp (i : Fin n) (a : Ω) :
      matrixQuadratic (fun j k => c i a * (Z i a j * Z i a k)) u =
        c i a * (faceDot u (Z i a)) ^ 2 := by
    rw [← matrixQuadratic_rankOne_eq_square]
    simp only [matrixQuadratic, rankOne, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  calc
    _ = ∑ i, matrixQuadratic
        (fun j k => ∫ a, c i a * (Z i a j * Z i a k) ∂μ) u := by
      unfold matrixQuadratic restorationCoefficient
      simp only [Finset.mul_sum, Finset.sum_mul]
      calc
        _ = ∑ j, ∑ i, ∑ k,
            (u j * ∫ a, c i a * (Z i a j * Z i a k) ∂μ) * u k := by
          apply Finset.sum_congr rfl
          intro j _
          exact Finset.sum_comm
        _ = _ := Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [matrixQuadratic_integral μ _
        (fun j k => integrable_restorationCoefficient_entry μ Z c hZ hc hb i j k) u]
      simp_rw [hp]

/-- The pointwise quadratic covariance budget survives arbitrary bounded
fresh-array multipliers.  The estimate has no dimension factor. -/
theorem abs_matrixQuadratic_restorationCoefficient_le (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b K : ℝ}
    (hZ : ∀ i j k, Integrable (fun a => Z i a j * Z i a k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ)
    (hb : ∀ i a, |c i a| ≤ b) (hb0 : 0 ≤ b)
    (hbudget : ∀ u : Vector r,
      ∑ i, ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ ≤ K * vectorNormSq u)
    (u : Vector r) :
    |matrixQuadratic (restorationCoefficient μ Z c) u| ≤
      (b * K) * vectorNormSq u := by
  rw [matrixQuadratic_restorationCoefficient μ Z c hZ hc hb]
  calc
    _ ≤ ∑ i, |∫ a, c i a * (faceDot u (Z i a)) ^ 2 ∂μ| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, b * ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ := by
      apply Finset.sum_le_sum
      intro i _
      have hi := integrable_weighted_faceDot_sq μ (Z i) (c i)
        (hZ i) (hc i) (hb i) u
      calc
        _ ≤ ∫ a, |c i a * (faceDot u (Z i a)) ^ 2| ∂μ := abs_integral_le_integral_abs
        _ ≤ ∫ a, b * (faceDot u (Z i a)) ^ 2 ∂μ := by
          apply integral_mono_ae hi.abs ((integrable_faceDot_sq μ (Z i) (hZ i) u).const_mul b)
          exact Filter.Eventually.of_forall (fun a => by
            dsimp only
            rw [abs_mul, abs_of_nonneg (sq_nonneg (faceDot u (Z i a)))]
            exact mul_le_mul_of_nonneg_right (hb i a) (sq_nonneg _))
        _ = _ := integral_const_mul _ _
    _ = b * (∑ i, ∫ a, (faceDot u (Z i a)) ^ 2 ∂μ) := (Finset.mul_sum ..).symm
    _ ≤ b * (K * vectorNormSq u) := mul_le_mul_of_nonneg_left (hbudget u) hb0
    _ = _ := by ring

end
end RectangleCLT.Companion
