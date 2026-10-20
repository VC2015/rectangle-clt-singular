import RectangleCLT.SmootherDerivatives

/-! Actual mixed second coordinate derivatives of the rational smoother and
their summed absolute-value envelope. No shifted supremum or higher-order
Fréchet derivative assertion is made here. -/

open scoped BigOperators

namespace RectangleCLT
namespace FaceWeights

variable {p : ℕ} (w : FaceWeights p)

noncomputable def coordinateMass (j : Fin p) : ℝ :=
  w.pi (j, true) + w.pi (j, false)

noncomputable def diagonalMass (j k : Fin p) : ℝ :=
  if j = k then w.coordinateMass j else 0

theorem coordinateMass_nonneg (j : Fin p) : 0 ≤ w.coordinateMass j :=
  add_nonneg (w.pi_nonneg _) (w.pi_nonneg _)

theorem diagonalMass_nonneg (j k : Fin p) : 0 ≤ w.diagonalMass j k := by
  unfold diagonalMass
  split_ifs
  · exact w.coordinateMass_nonneg j
  · rfl

theorem sum_coordinateMass : ∑ j, w.coordinateMass j = w.theta := by
  rw [← w.sum_pi]
  simp [coordinateMass, Fintype.sum_prod_type, Fintype.sum_bool]

theorem sum_diagonalMass : ∑ j, ∑ k, w.diagonalMass j k = w.theta := by
  simp only [diagonalMass]
  simpa only [Finset.sum_ite_eq, Finset.mem_univ, if_true] using w.sum_coordinateMass

/-- The purely algebraic second derivative factor has total absolute mass at
most three times `theta`. -/
theorem sum_abs_second_factor_le :
    (∑ j, ∑ k, |2 * w.v j * w.v k - w.diagonalMass j k|) ≤ 3 * w.theta := by
  have hpoint (j k : Fin p) :
      |2 * w.v j * w.v k - w.diagonalMass j k| ≤
        2 * |w.v j| * |w.v k| + w.diagonalMass j k := by
    calc
      _ ≤ |2 * w.v j * w.v k| + |w.diagonalMass j k| := by
        simpa only [sub_zero, zero_sub, abs_neg] using
          abs_sub_le (2 * w.v j * w.v k) (0 : ℝ) (w.diagonalMass j k)
      _ = _ := by
        rw [abs_mul, abs_mul, abs_of_nonneg (w.diagonalMass_nonneg j k)]
        norm_num
  have hprod : (∑ j, ∑ k, 2 * |w.v j| * |w.v k|) =
      2 * (∑ j, |w.v j|) ^ 2 := by
    simp only [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
    ring
  have hA : 0 ≤ ∑ j, |w.v j| := Finset.sum_nonneg (fun j _ => abs_nonneg _)
  have hAone : (∑ j, |w.v j|) ≤ 1 := w.sum_abs_v_le_one
  have hAsq : (∑ j, |w.v j|) ^ 2 ≤ w.theta := by
    nlinarith [w.sum_abs_v_le_theta,
      mul_nonneg hA (sub_nonneg.mpr hAone)]
  calc
    _ ≤ ∑ j, ∑ k, (2 * |w.v j| * |w.v k| + w.diagonalMass j k) := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun k _ => hpoint j k)
    _ = 2 * (∑ j, |w.v j|) ^ 2 + w.theta := by
      simp_rw [Finset.sum_add_distrib]
      rw [hprod, w.sum_diagonalMass]
    _ ≤ 3 * w.theta := by linarith

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The coordinate first derivative is an actual ordinary derivative of `F`. -/
noncomputable def coordinateDerivativeF (x : Fin p → ℝ) (j : Fin p) : ℝ :=
  deriv (fun t => s.F (line x (coordinateDirection j) t)) 0

theorem coordinateDerivativeF_eq (x : Fin p → ℝ) (j : Fin p) :
    s.coordinateDerivativeF x j = -(s.F x / s.bandwidth) * (s.weights x).v j :=
  s.deriv_F_coordinate x j

theorem hasDerivAt_v_coordinate_line (x y : Fin p → ℝ) (j : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.v (line x y r) j)
      (((s.weights (line x y t)).coordinateMass j * y j -
        (s.weights (line x y t)).v j *
          (s.weights (line x y t)).directionalMean y) / s.bandwidth) t := by
  have hd := (s.hasDerivAt_pi_line (j, true) x y t).sub
    (s.hasDerivAt_pi_line (j, false) x y t)
  have heq :
      (s.pi (line x y t) (j, true) / s.bandwidth *
          (normalDot (j, true) y - (s.weights (line x y t)).directionalMean y) -
        s.pi (line x y t) (j, false) / s.bandwidth *
          (normalDot (j, false) y - (s.weights (line x y t)).directionalMean y)) =
        ((s.weights (line x y t)).coordinateMass j * y j -
          (s.weights (line x y t)).v j *
            (s.weights (line x y t)).directionalMean y) / s.bandwidth := by
    simp only [normalDot, Bool.false_eq_true, ↓reduceIte, pi,
      FaceWeights.coordinateMass, FaceWeights.v]
    ring
  rw [heq] at hd
  exact hd

/-- Differentiating an actual coordinate first derivative along any affine line. -/
theorem hasDerivAt_coordinateDerivativeF_line (x y : Fin p → ℝ)
    (j : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.coordinateDerivativeF (line x y r) j)
      ((s.F (line x y t) / s.bandwidth ^ 2) *
        (2 * (s.weights (line x y t)).v j *
            (s.weights (line x y t)).directionalMean y -
          (s.weights (line x y t)).coordinateMass j * y j)) t := by
  simp_rw [s.coordinateDerivativeF_eq]
  have hd := ((s.hasDerivAt_F_line x y t).div_const s.bandwidth).neg.mul
    (s.hasDerivAt_v_coordinate_line x y j t)
  have heq :
      (-((-(s.F (line x y t) / s.bandwidth) *
            (s.weights (line x y t)).directionalMean y) / s.bandwidth) *
          s.v (line x y t) j +
        (-(s.F (line x y t) / s.bandwidth)) *
          (((s.weights (line x y t)).coordinateMass j * y j -
              (s.weights (line x y t)).v j *
                (s.weights (line x y t)).directionalMean y) / s.bandwidth)) =
        (s.F (line x y t) / s.bandwidth ^ 2) *
          (2 * (s.weights (line x y t)).v j *
              (s.weights (line x y t)).directionalMean y -
            (s.weights (line x y t)).coordinateMass j * y j) := by
    unfold v
    field_simp [ne_of_gt s.bandwidth_pos]
    ring
  rw [heq] at hd
  exact hd

/-- An actual iterated mixed second coordinate derivative. -/
noncomputable def mixedSecondDerivativeF (x : Fin p → ℝ) (j k : Fin p) : ℝ :=
  deriv (fun t => s.coordinateDerivativeF (line x (coordinateDirection k) t) j) 0

theorem mixedSecondDerivativeF_eq (x : Fin p → ℝ) (j k : Fin p) :
    s.mixedSecondDerivativeF x j k =
      (s.F x / s.bandwidth ^ 2) *
        (2 * (s.weights x).v j * (s.weights x).v k -
          (s.weights x).diagonalMass j k) := by
  unfold mixedSecondDerivativeF
  have h := (s.hasDerivAt_coordinateDerivativeF_line x (coordinateDirection k) j 0).deriv
  by_cases hjk : j = k <;>
    simpa only [line_zero, directionalMean_coordinate, coordinateDirection,
      FaceWeights.diagonalMass, hjk, ↓reduceIte, mul_one, mul_zero] using h

theorem mixedSecondDerivativeF_symm (x : Fin p → ℝ) (j k : Fin p) :
    s.mixedSecondDerivativeF x j k = s.mixedSecondDerivativeF x k j := by
  rw [s.mixedSecondDerivativeF_eq, s.mixedSecondDerivativeF_eq]
  by_cases hjk : j = k
  · subst k
    rfl
  · simp only [FaceWeights.diagonalMass, hjk, Ne.symm hjk, ↓reduceIte]
    ring

/-- The pointwise second derivative envelope, with the explicit constant `3`. -/
theorem sum_abs_mixedSecondDerivativeF_le_variance (x : Fin p → ℝ) :
    (∑ j, ∑ k, |s.mixedSecondDerivativeF x j k|) ≤
      3 * s.F x * (1 - s.F x) / s.bandwidth ^ 2 := by
  have hc : 0 ≤ s.F x / s.bandwidth ^ 2 :=
    div_nonneg (s.F_pos x).le (sq_nonneg _)
  calc
    _ = (s.F x / s.bandwidth ^ 2) *
        (∑ j, ∑ k, |2 * (s.weights x).v j * (s.weights x).v k -
          (s.weights x).diagonalMass j k|) := by
      simp_rw [s.mixedSecondDerivativeF_eq, abs_mul, abs_of_nonneg hc]
      simp only [Finset.mul_sum]
    _ ≤ (s.F x / s.bandwidth ^ 2) * (3 * (s.weights x).theta) :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_abs_second_factor_le hc
    _ = 3 * s.F x * (1 - s.F x) / s.bandwidth ^ 2 := by
      change (s.F x / s.bandwidth ^ 2) * (3 * (1 - s.F x)) = _
      ring

end FaceSmoother
end RectangleCLT
