import RectangleCLT.Smoother
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-! Actual one-dimensional derivatives of the rectangle smoother along affine
lines. These theorems use `HasDerivAt`; the algebraic quantities are not merely
postulated to be derivatives. -/

open scoped BigOperators

namespace RectangleCLT
namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The affine line through `x` in direction `y`. -/
def line (x y : Fin p → ℝ) (t : ℝ) : Fin p → ℝ := fun j => x j + t * y j

@[simp] theorem line_zero (x y : Fin p → ℝ) : line x y 0 = x := by
  funext j
  simp only [line, zero_mul, add_zero]

theorem hasDerivAt_faceScore_line (f : Face p) (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.faceScore f (line x y r)) (normalDot f y) t := by
  have hc := (hasDerivAt_const t (x f.1)).add
    ((hasDerivAt_id t).mul_const (y f.1))
  cases hf : f.2
  · simpa [faceScore, normalDot, line, hf] using
      hc.neg.sub (hasDerivAt_const t (s.offsets f))
  · simpa [faceScore, normalDot, line, hf] using
      hc.sub (hasDerivAt_const t (s.offsets f))

theorem hasDerivAt_weight_line (f : Face p) (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => (s.weights (line x y r)).weight f)
      ((s.weights (line x y t)).weight f * normalDot f y / s.bandwidth) t := by
  classical
  by_cases hf : f ∈ s.faces
  · simpa [weights, hf, mul_div_assoc] using
      ((s.hasDerivAt_faceScore_line f x y t).div_const s.bandwidth).exp
  · simpa [weights, hf] using (hasDerivAt_const t (0 : ℝ))

/-- The first derivative of the unnormalized exponential sum. -/
theorem hasDerivAt_T_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => (s.weights (line x y r)).T)
      (∑ f, (s.weights (line x y t)).weight f * normalDot f y / s.bandwidth) t := by
  simpa only [FaceWeights.T] using
    HasDerivAt.sum (u := Finset.univ) (fun f _ => s.hasDerivAt_weight_line f x y t)

private theorem sum_weight_normal_eq (x y : Fin p → ℝ) :
    (∑ f, (s.weights x).weight f * normalDot f y) =
      (1 + (s.weights x).T) * (s.weights x).directionalMean y := by
  symm
  unfold FaceWeights.directionalMean
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro f _
  change (1 + (s.weights x).T) *
      ((s.weights x).weight f / (1 + (s.weights x).T) * normalDot f y) = _
  field_simp [ne_of_gt (s.weights x).denominator_pos]

theorem hasDerivAt_T_line_normalized (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => (s.weights (line x y r)).T)
      ((1 + (s.weights (line x y t)).T) *
        (s.weights (line x y t)).directionalMean y / s.bandwidth) t := by
  have heq :
      (∑ f, (s.weights (line x y t)).weight f * normalDot f y / s.bandwidth) =
        (1 + (s.weights (line x y t)).T) *
          (s.weights (line x y t)).directionalMean y / s.bandwidth := by
    rw [show (∑ f, (s.weights (line x y t)).weight f * normalDot f y / s.bandwidth) =
        (∑ f, (s.weights (line x y t)).weight f * normalDot f y) / s.bandwidth by
      simp only [div_eq_mul_inv, ← Finset.sum_mul]]
    rw [s.sum_weight_normal_eq]
  rw [← heq]
  exact s.hasDerivAt_T_line x y t

/-- The actual directional first derivative of the rational smoother. -/
theorem hasDerivAt_F_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.F (line x y r))
      (-(s.F (line x y t) / s.bandwidth) *
        (s.weights (line x y t)).directionalMean y) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).add
    (s.hasDerivAt_T_line_normalized x y t)
  have h := (hasDerivAt_const t (1 : ℝ)).div hd
    (ne_of_gt (s.weights (line x y t)).denominator_pos)
  have heq :
      (0 * (1 + (s.weights (line x y t)).T) - 1 *
        (0 + (1 + (s.weights (line x y t)).T) *
          (s.weights (line x y t)).directionalMean y / s.bandwidth)) /
          (1 + (s.weights (line x y t)).T) ^ 2 =
        -(s.F (line x y t) / s.bandwidth) *
          (s.weights (line x y t)).directionalMean y := by
    unfold F FaceWeights.F
    field_simp [ne_of_gt (s.weights (line x y t)).denominator_pos,
      ne_of_gt s.bandwidth_pos]
    ring
  simpa only [F, FaceWeights.F, heq] using h

/-- The actual derivative of each normalized face probability. -/
theorem hasDerivAt_pi_line (f : Face p) (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.pi (line x y r) f)
      ((s.pi (line x y t) f / s.bandwidth) *
        (normalDot f y - (s.weights (line x y t)).directionalMean y)) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).add
    (s.hasDerivAt_T_line_normalized x y t)
  have h := (s.hasDerivAt_weight_line f x y t).div hd
    (ne_of_gt (s.weights (line x y t)).denominator_pos)
  have heq :
      ((s.weights (line x y t)).weight f * normalDot f y / s.bandwidth *
          (1 + (s.weights (line x y t)).T) -
        (s.weights (line x y t)).weight f *
          (0 + (1 + (s.weights (line x y t)).T) *
            (s.weights (line x y t)).directionalMean y / s.bandwidth)) /
          (1 + (s.weights (line x y t)).T) ^ 2 =
        (s.pi (line x y t) f / s.bandwidth) *
          (normalDot f y - (s.weights (line x y t)).directionalMean y) := by
    unfold pi FaceWeights.pi
    field_simp [ne_of_gt (s.weights (line x y t)).denominator_pos,
      ne_of_gt s.bandwidth_pos]
    ring
  simpa only [pi, FaceWeights.pi, heq] using h

/-- The actual directional first derivative of the logarithmic potential. -/
theorem hasDerivAt_potential_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => s.potential (line x y r))
      ((s.weights (line x y t)).directionalMean y) t := by
  have hd := (hasDerivAt_const t (1 : ℝ)).add
    (s.hasDerivAt_T_line_normalized x y t)
  have h := (hd.log (ne_of_gt (s.weights (line x y t)).denominator_pos)).const_mul
    s.bandwidth
  have heq : s.bandwidth *
      ((0 + (1 + (s.weights (line x y t)).T) *
        (s.weights (line x y t)).directionalMean y / s.bandwidth) /
          (1 + (s.weights (line x y t)).T)) =
        (s.weights (line x y t)).directionalMean y := by
    field_simp [ne_of_gt (s.weights (line x y t)).denominator_pos,
      ne_of_gt s.bandwidth_pos]
    ring
  simpa only [potential, heq] using h

/-- Differentiating the directional mean gives the actual directional covariance
of the signed normals, divided by the bandwidth. -/
theorem hasDerivAt_directionalMean_line (x y : Fin p → ℝ) (t : ℝ) :
    HasDerivAt (fun r => (s.weights (line x y r)).directionalMean y)
      ((s.weights (line x y t)).directionalCovariance y / s.bandwidth) t := by
  let w := s.weights (line x y t)
  let m := w.directionalMean y
  let a := fun f : Face p => normalDot f y
  have heq : (∑ f, (w.pi f / s.bandwidth * (a f - m)) * a f) =
      w.directionalCovariance y / s.bandwidth := by
    calc
      _ = (∑ f, (w.pi f * a f ^ 2 - m * (w.pi f * a f))) / s.bandwidth := by
        simp only [div_eq_mul_inv, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro f _
        ring
      _ = _ := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
        change (w.directionalSecondMoment y - m * m) / s.bandwidth = _
        unfold FaceWeights.directionalCovariance
        dsimp [m]
        ring
  have hd := HasDerivAt.sum (u := Finset.univ)
    (fun f _ => (s.hasDerivAt_pi_line f x y t).mul_const (normalDot f y))
  change HasDerivAt (fun r => ∑ f, s.pi (line x y r) f * normalDot f y)
    (w.directionalCovariance y / s.bandwidth) t
  rw [← heq]
  exact hd

theorem deriv_potential_line (x y : Fin p → ℝ) (t : ℝ) :
    deriv (fun r => s.potential (line x y r)) t =
      (s.weights (line x y t)).directionalMean y :=
  (s.hasDerivAt_potential_line x y t).deriv

/-- The second ordinary derivative of the potential along an affine line. -/
theorem second_deriv_potential_line (x y : Fin p → ℝ) (t : ℝ) :
    deriv (fun r => deriv (fun u => s.potential (line x y u)) r) t =
      (s.weights (line x y t)).directionalCovariance y / s.bandwidth := by
  simp_rw [s.deriv_potential_line]
  exact (s.hasDerivAt_directionalMean_line x y t).deriv

theorem second_deriv_potential_line_nonneg (x y : Fin p → ℝ) (t : ℝ) :
    0 ≤ deriv (fun r => deriv (fun u => s.potential (line x y u)) r) t := by
  rw [s.second_deriv_potential_line]
  exact div_nonneg (FaceWeights.directionalCovariance_nonneg _ _) s.bandwidth_pos.le

/-- The `j`th coordinate direction. -/
def coordinateDirection (j : Fin p) : Fin p → ℝ := fun k => if k = j then 1 else 0

theorem directionalMean_coordinate (w : FaceWeights p) (j : Fin p) :
    w.directionalMean (coordinateDirection j) = w.v j := by
  rw [w.directionalMean_eq]
  simp [coordinateDirection]

theorem directionalCovariance_coordinate (w : FaceWeights p) (j : Fin p) :
    w.directionalCovariance (coordinateDirection j) = w.covarianceDiagonal j := by
  unfold FaceWeights.directionalCovariance
  rw [directionalMean_coordinate, w.directionalSecondMoment_eq]
  simp [coordinateDirection, FaceWeights.covarianceDiagonal]

/-- Actual coordinate first derivatives of the rational smoother. -/
theorem deriv_F_coordinate (x : Fin p → ℝ) (j : Fin p) :
    deriv (fun t => s.F (line x (coordinateDirection j) t)) 0 =
      -(s.F x / s.bandwidth) * (s.weights x).v j := by
  simpa only [line_zero, directionalMean_coordinate] using
    (s.hasDerivAt_F_line x (coordinateDirection j) 0).deriv

/-- Actual coordinate first derivatives of the logarithmic potential. -/
theorem deriv_potential_coordinate (x : Fin p → ℝ) (j : Fin p) :
    deriv (fun t => s.potential (line x (coordinateDirection j) t)) 0 = s.v x j := by
  simpa only [line_zero, directionalMean_coordinate, v] using
    s.deriv_potential_line x (coordinateDirection j) 0

theorem second_deriv_potential_coordinate (x : Fin p → ℝ) (j : Fin p) :
    deriv (fun t => deriv (fun u => s.potential (line x (coordinateDirection j) u)) t) 0 =
      (s.weights x).covarianceDiagonal j / s.bandwidth := by
  rw [s.second_deriv_potential_line]
  simp only [line_zero, directionalCovariance_coordinate]

/-- Identification of the algebraic curvature with bandwidth times the sum of
actual second coordinate derivatives of the potential. -/
theorem bandwidth_mul_coordinate_trace (x : Fin p → ℝ) :
    s.bandwidth *
        (∑ j, deriv (fun t => deriv
          (fun u => s.potential (line x (coordinateDirection j) u)) t) 0) =
      s.kappa x := by
  simp_rw [s.second_deriv_potential_coordinate]
  calc
    _ = ∑ j, (s.weights x).covarianceDiagonal j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      field_simp [ne_of_gt s.bandwidth_pos]
    _ = s.kappa x := (s.weights x).covariance_trace_eq_kappa

/-- The first derivative envelope in the sharper Bernoulli-variance form. -/
theorem sum_abs_deriv_F_coordinate_le_variance (x : Fin p → ℝ) :
    (∑ j, |deriv (fun t => s.F (line x (coordinateDirection j) t)) 0|) ≤
      s.F x * (1 - s.F x) / s.bandwidth := by
  have hfrac : 0 ≤ s.F x / s.bandwidth := (div_pos (s.F_pos x) s.bandwidth_pos).le
  calc
    _ = (s.F x / s.bandwidth) * (∑ j, |(s.weights x).v j|) := by
      simp_rw [s.deriv_F_coordinate, abs_mul, abs_neg, abs_of_nonneg hfrac]
      rw [Finset.mul_sum]
    _ ≤ (s.F x / s.bandwidth) * (s.weights x).theta :=
      mul_le_mul_of_nonneg_left (s.weights x).sum_abs_v_le_theta hfrac
    _ = s.F x * (1 - s.F x) / s.bandwidth := by
      change (s.F x / s.bandwidth) * (1 - s.F x) = _
      ring

/-- The sum of the absolute actual first coordinate derivatives of `F` is
bounded by the pointwise curvature divided by the bandwidth. -/
theorem sum_abs_deriv_F_coordinate_le (x : Fin p → ℝ) :
    (∑ j, |deriv (fun t => s.F (line x (coordinateDirection j) t)) 0|) ≤
      s.kappa x / s.bandwidth := by
  have hk : s.F x * (1 - s.F x) ≤ s.kappa x := by
    have h := (s.weights x).kappa_ge_theta_mul_one_sub_theta
    simpa [F, FaceWeights.theta, kappa, mul_comm] using h
  exact (s.sum_abs_deriv_F_coordinate_le_variance x).trans
    (div_le_div_of_nonneg_right hk s.bandwidth_pos.le)

end FaceSmoother
end RectangleCLT
