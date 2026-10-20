import RectangleCLT.LocalStatement

/-!
# Positive coordinate scaling for rectangle approximation

Pulling back each interval treats every endpoint convention uniformly.
The Gaussian factor is transformed on its rows, so the comparison remains
with the concrete Gaussian law rather than an unspecified Gaussian vector.
-/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

def diagonalScale {p : ℕ} (d : Vector p) (x : Vector p) : Vector p :=
  fun j => d j * x j

theorem measurable_diagonalScale {p : ℕ} (d : Vector p) :
    Measurable (diagonalScale d) := by
  apply measurable_pi_lambda
  intro j
  exact measurable_const.mul (measurable_pi_apply j)

def scaledFactor {p : ℕ} (d : Vector p) (A : Matrix (Fin p) (Fin p) ℝ) :
    Matrix (Fin p) (Fin p) ℝ := fun j k => d j * A j k

theorem scaledFactor_mulVec {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) :
    (scaledFactor d A).mulVec x = diagonalScale d (A.mulVec x) := by
  ext j
  simp only [Matrix.mulVec, dotProduct, scaledFactor, diagonalScale,
    Finset.mul_sum, mul_assoc]

theorem gaussianLaw_map_diagonalScale {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (gaussianLaw A).map (diagonalScale d) = gaussianLaw (scaledFactor d A) := by
  unfold gaussianLaw
  rw [Measure.map_map (measurable_diagonalScale d) (measurable_mulVec A)]
  congr 1
  funext x
  exact (scaledFactor_mulVec d A x).symm

theorem diagonalScale_inverse {p : ℕ} (d : Vector p)
    (hd : ∀ j, d j ≠ 0) (x : Vector p) :
    diagonalScale (fun j => (d j)⁻¹) (diagonalScale d x) = x := by
  ext j
  simp only [diagonalScale, ← mul_assoc, inv_mul_cancel₀ (hd j), one_mul]

theorem scaledFactor_inverse {p : ℕ} (d : Vector p)
    (hd : ∀ j, d j ≠ 0) (A : Matrix (Fin p) (Fin p) ℝ) :
    scaledFactor d (scaledFactor (fun j => (d j)⁻¹) A) = A := by
  ext j k
  simp only [scaledFactor, ← mul_assoc, mul_inv_cancel₀ (hd j), one_mul]

theorem diagonalScale_inverse_right {p : ℕ} (d : Vector p)
    (hd : ∀ j, d j ≠ 0) (x : Vector p) :
    diagonalScale d (diagonalScale (fun j => (d j)⁻¹) x) = x := by
  ext j
  simp only [diagonalScale, ← mul_assoc, mul_inv_cancel₀ (hd j), one_mul]

theorem covariance_diagonalScale {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p) (d : Vector p) (j k : Fin p) :
    covariance μ (fun ω => diagonalScale d (W ω)) j k =
      d j * d k * covariance μ W j k := by
  simp only [covariance, diagonalScale]
  have hprod : (fun ω => d j * W ω j * (d k * W ω k)) =
      (fun ω => (d j * d k) * (W ω j * W ω k)) := by
    funext ω
    ring
  rw [hprod, integral_const_mul, integral_const_mul, integral_const_mul]
  ring

theorem scaledFactor_gram {p : ℕ} (d : Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (j k : Fin p) :
    (scaledFactor d A * (scaledFactor d A).transpose) j k =
      d j * d k * (A * A.transpose) j k := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, scaledFactor,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Coordinatewise linear rescaling preserves independence and centering.
The envelope is multiplied by a uniform bound for the coordinate scales. -/
theorem boundedIndependent_diagonalScale {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (d : Vector p) {M : ℝ} (hM : 0 ≤ M) (hd : ∀ j, |d j| ≤ M) :
    BoundedIndependentHypotheses μ
      (fun i ω => diagonalScale d (ξ i ω)) (M * δ) := by
  refine ⟨fun i => (measurable_diagonalScale d).comp (h.measurable i), ?_, ?_, ?_,
    mul_nonneg hM h.delta_nonneg⟩
  · exact h.independent.comp (fun _ => diagonalScale d)
      (fun _ => measurable_diagonalScale d)
  · intro i j
    simp only [diagonalScale, integral_const_mul, h.centered, mul_zero]
  · intro i
    filter_upwards [h.bounded i] with ω hω
    apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM h.delta_nonneg)).mpr
    intro j
    have hx : |ξ i ω j| ≤ δ := by
      simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (ξ i ω) j).trans hω
    simpa only [diagonalScale, Real.norm_eq_abs, abs_mul] using
      mul_le_mul (hd j) hx (abs_nonneg _) hM

theorem sumVector_diagonalScale {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (d : Vector p) (ω : Ω) :
    sumVector (fun i ω => diagonalScale d (ξ i ω)) ω =
      diagonalScale d (sumVector ξ ω) := by
  ext j
  simp only [sumVector, Finset.sum_apply, diagonalScale, Finset.mul_sum]

/-- Clipped marginal standard deviations bounded below by one half cost
at most a factor two in the observation envelope. -/
theorem boundedIndependent_standardize {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} {μ : Measure Ω} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ)
    (d : Vector p) (hd : ∀ j, (1 / 2 : ℝ) ≤ d j) :
    BoundedIndependentHypotheses μ
      (fun i ω => diagonalScale (fun j => (d j)⁻¹) (ξ i ω)) (2 * δ) := by
  apply boundedIndependent_diagonalScale h _ (by norm_num : (0 : ℝ) ≤ 2)
  intro j
  have hdp : 0 < d j := lt_of_lt_of_le (by norm_num) (hd j)
  rw [abs_of_pos (inv_pos.mpr hdp)]
  apply (inv_le_iff_one_le_mul₀ hdp).mpr
  linarith [hd j]

theorem covariance_standardize_diagonal {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p) (d : Vector p)
    (hd : ∀ j, d j ≠ 0) (hvar : ∀ j, covariance μ W j j = (d j) ^ 2) (j : Fin p) :
    covariance μ (fun ω => diagonalScale (fun k => (d k)⁻¹) (W ω)) j j = 1 := by
  rw [covariance_diagonalScale, hvar]
  field_simp [hd j]

end

end RectangleCLT.Companion

namespace RectangleCLT.Rect

open Companion

/-- Pullback under a nonnegative diagonal map is again a rectangle.
Strict positivity is only needed when an inverse map is used. -/
def pullbackDiagonal {p : ℕ} (R : Rect p) (d : Vector p)
    (hd : ∀ j, 0 ≤ d j) : Rect p where
  interval j := (fun x : ℝ => d j * x) ⁻¹' R.interval j
  ordConnected j := (R.ordConnected j).preimage_mono
    (fun _ _ h => mul_le_mul_of_nonneg_left h (hd j))
  measurable j := (R.measurable j).preimage (measurable_const.mul measurable_id)

@[simp] theorem carrier_pullbackDiagonal {p : ℕ} (R : Rect p) (d : Vector p)
    (hd : ∀ j, 0 ≤ d j) :
    (R.pullbackDiagonal d hd).carrier = diagonalScale d ⁻¹' R.carrier := rfl

end RectangleCLT.Rect

namespace RectangleCLT.Companion

noncomputable section

/-- Scaling both endpoints of a Gaussian comparison changes only the test
rectangle. This is exact and does not require boundary nullity or any
assumption on the rank of the covariance. -/
theorem rectangleError_diagonalScale {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p)
    (d : Vector p) (hd : ∀ j, 0 ≤ d j)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError μ (fun ω => diagonalScale d (W ω)) (scaledFactor d A) R =
      rectangleError μ W A (R.pullbackDiagonal d hd) := by
  unfold rectangleError
  rw [← gaussianLaw_map_diagonalScale d A]
  simp only [Measure.real,
    Measure.map_apply (measurable_diagonalScale d) R.measurableSet_carrier]
  rfl

/-- A uniform rectangle comparison transfers under every nonnegative
coordinate scaling. In particular it transfers under the positive
standardization and its inverse used after clipping. -/
theorem rectangleError_diagonalScale_le {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p)
    (d : Vector p) (hd : ∀ j, 0 ≤ d j)
    (A : Matrix (Fin p) (Fin p) ℝ) {B : ℝ}
    (hbound : ∀ R : Rect p, rectangleError μ W A R ≤ B) (R : Rect p) :
    rectangleError μ (fun ω => diagonalScale d (W ω)) (scaledFactor d A) R ≤ B := by
  rw [rectangleError_diagonalScale μ W d hd A R]
  exact hbound _

end

end RectangleCLT.Companion
