import RectangleCLT.SmootherDerivatives

/-!
# Stability of the actual logarithmic smoother curvature

The variance-minimization representation gives the stronger factor `exp (2r/h)`.
The factor `exp (4r/h)` in the manuscript follows as a weaker corollary.
The null face, with probability `F`, is included throughout the comparison.
-/

open scoped BigOperators

namespace RectangleCLT
namespace FaceWeights

variable {p : ℕ}

/-- Squared distance from any center is the variance plus the squared distance
of that center from the mean, including the zero-normal face. -/
theorem directional_shifted_variance (w : FaceWeights p) (y : Fin p → ℝ) (u : ℝ) :
    w.F * u ^ 2 + ∑ f, w.pi f * (directionalValue f y - u) ^ 2 =
      w.directionalCovariance y + (w.directionalMean y - u) ^ 2 := by
  have hexpand : (∑ f, w.pi f * (directionalValue f y - u) ^ 2) =
      w.directionalSecondMoment y - 2 * u * w.directionalMean y + u ^ 2 * w.theta := by
    calc
      _ = ∑ f, (w.pi f * directionalValue f y ^ 2 -
          2 * u * (w.pi f * directionalValue f y) + u ^ 2 * w.pi f) := by
        apply Finset.sum_congr rfl
        intro f _
        ring
      _ = _ := by
        rw [Finset.sum_add_distrib, Finset.sum_sub_distrib,
          ← Finset.mul_sum, ← Finset.mul_sum, w.sum_pi]
        rfl
  rw [hexpand]
  unfold directionalCovariance theta
  ring

/-- Comparing every face probability, including the null face, compares the
covariance quadratic forms with the same factor. -/
theorem directionalCovariance_le_of_probabilities_le
    (w w' : FaceWeights p) (K : ℝ)
    (hF : w'.F ≤ K * w.F) (hpi : ∀ f, w'.pi f ≤ K * w.pi f)
    (y : Fin p → ℝ) : w'.directionalCovariance y ≤ K * w.directionalCovariance y := by
  let u := w.directionalMean y
  have hmin : w'.directionalCovariance y ≤
      w'.F * u ^ 2 + ∑ f, w'.pi f * (directionalValue f y - u) ^ 2 := by
    rw [w'.directional_shifted_variance]
    exact le_add_of_nonneg_right (sq_nonneg _)
  calc
    _ ≤ w'.F * u ^ 2 + ∑ f, w'.pi f * (directionalValue f y - u) ^ 2 := hmin
    _ ≤ (K * w.F) * u ^ 2 +
        ∑ f, (K * w.pi f) * (directionalValue f y - u) ^ 2 := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right hF (sq_nonneg u)
      · exact Finset.sum_le_sum fun f _ =>
          mul_le_mul_of_nonneg_right (hpi f) (sq_nonneg _)
    _ = K * (w.F * u ^ 2 + ∑ f, w.pi f * (directionalValue f y - u) ^ 2) := by
      simp only [mul_add, Finset.mul_sum, mul_assoc]
    _ = K * w.directionalCovariance y := by
      rw [w.directional_shifted_variance]
      simp only [u, sub_self, zero_pow (by decide : 2 ≠ 0), add_zero]

theorem kappa_le_of_probabilities_le (w w' : FaceWeights p) (K : ℝ)
    (hF : w'.F ≤ K * w.F) (hpi : ∀ f, w'.pi f ≤ K * w.pi f) :
    w'.kappa ≤ K * w.kappa := by
  rw [← w'.covariance_trace_eq_kappa, ← w.covariance_trace_eq_kappa, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [FaceSmoother.directionalCovariance_coordinate] using
    directionalCovariance_le_of_probabilities_le w w' K hF hpi
      (FaceSmoother.coordinateDirection j)

/-- An elementary normalized-weight comparison. This includes the null
weight `1`, so the multiplicative factor is required to be at least one. -/
theorem denominator_le_of_weights_le (w w' : FaceWeights p) (K : ℝ)
    (hK : 1 ≤ K) (hw : ∀ f, w.weight f ≤ K * w'.weight f) :
    1 + w.T ≤ K * (1 + w'.T) := by
  have hsum : w.T ≤ K * w'.T := by
    unfold T
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun f _ => hw f
  nlinarith

private theorem normalized_le {a a' D D' K : ℝ}
    (ha : 0 ≤ a) (hD : 0 < D) (hD' : 0 < D') (hK : 0 ≤ K)
    (hw : a' ≤ K * a) (hden : D ≤ K * D') :
    a' / D' ≤ K ^ 2 * (a / D) := by
  apply (div_le_iff₀ hD').mpr
  calc
    a' ≤ K * a := hw
    _ = (K * a / D) * D := by field_simp
    _ ≤ (K * a / D) * (K * D') :=
      mul_le_mul_of_nonneg_left hden (div_nonneg (mul_nonneg hK ha) hD.le)
    _ = K ^ 2 * (a / D) * D' := by ring

theorem pi_le_of_weights_le (w w' : FaceWeights p) (K : ℝ)
    (hK : 1 ≤ K) (hw : ∀ f, w'.weight f ≤ K * w.weight f)
    (hwrev : ∀ f, w.weight f ≤ K * w'.weight f) (f : Face p) :
    w'.pi f ≤ K ^ 2 * w.pi f := by
  exact normalized_le (w.nonneg f) w.denominator_pos w'.denominator_pos
    (by linarith) (hw f) (denominator_le_of_weights_le w w' K hK hwrev)

theorem F_le_of_weights_le (w w' : FaceWeights p) (K : ℝ)
    (hK : 1 ≤ K) (hwrev : ∀ f, w.weight f ≤ K * w'.weight f) :
    w'.F ≤ K ^ 2 * w.F := by
  exact normalized_le (by norm_num : (0 : ℝ) ≤ 1) w.denominator_pos
    w'.denominator_pos (by linarith) (by simpa using hK)
    (denominator_le_of_weights_le w w' K hK hwrev)

/-- The fixed null weight needs only one factor, rather than the two factors
needed for a variable face weight. -/
theorem F_le_of_weights_le_one_factor (w w' : FaceWeights p) (K : ℝ)
    (hK : 1 ≤ K) (hwrev : ∀ f, w.weight f ≤ K * w'.weight f) :
    w'.F ≤ K * w.F := by
  unfold F
  apply (div_le_iff₀ w'.denominator_pos).mpr
  calc
    1 = (1 / (1 + w.T)) * (1 + w.T) := by
      field_simp [ne_of_gt w.denominator_pos]
    _ ≤ (1 / (1 + w.T)) * (K * (1 + w'.T)) :=
      mul_le_mul_of_nonneg_left (denominator_le_of_weights_le w w' K hK hwrev)
        (one_div_nonneg.mpr w.denominator_pos.le)
    _ = K * (1 / (1 + w.T)) * (1 + w'.T) := by ring

end FaceWeights

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem normalDot_add (f : Face p) (x z : Fin p → ℝ) :
    normalDot f (x + z) = normalDot f x + normalDot f z := by
  cases hf : f.2 <;> simp [normalDot, hf, add_comm]

theorem abs_normalDot_le_of_norm_le (f : Face p) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : |normalDot f z| ≤ r := by
  have hr : 0 ≤ r := (norm_nonneg z).trans hz
  have hcoord := (pi_norm_le_iff_of_nonneg hr).mp hz f.1
  cases hf : f.2 <;> simpa [normalDot, hf, Real.norm_eq_abs] using hcoord

theorem weight_shift_eq (f : Face p) (x z : Fin p → ℝ) :
    (s.weights (x + z)).weight f =
      (s.weights x).weight f * Real.exp (normalDot f z / s.bandwidth) := by
  classical
  by_cases hf : f ∈ s.faces
  · simp only [weights, hf, ↓reduceIte, ← Real.exp_add]
    congr 1
    rw [faceScore, faceScore, normalDot_add]
    ring
  · simp [weights, hf]

theorem weight_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (f : Face p) :
    (s.weights (x + z)).weight f ≤
      Real.exp (r / s.bandwidth) * (s.weights x).weight f := by
  rw [s.weight_shift_eq]
  have hcoord := (abs_le.mp (abs_normalDot_le_of_norm_le f hz)).2
  have hexp := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right hcoord s.bandwidth_pos.le)
  simpa only [mul_comm] using
    mul_le_mul_of_nonneg_left hexp ((s.weights x).nonneg f)

theorem weight_le_shift (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (f : Face p) :
    (s.weights x).weight f ≤
      Real.exp (r / s.bandwidth) * (s.weights (x + z)).weight f := by
  have hneg : ‖-z‖ ≤ r := by simpa only [norm_neg] using hz
  simpa only [add_neg_cancel_right] using s.weight_shift_le (x + z) hneg f

private theorem one_le_shift_factor {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    1 ≤ Real.exp (r / s.bandwidth) :=
  Real.one_le_exp (div_nonneg ((norm_nonneg z).trans hz) s.bandwidth_pos.le)

private theorem shift_factor_sq (r : ℝ) :
    Real.exp (r / s.bandwidth) ^ 2 = Real.exp (2 * r / s.bandwidth) := by
  rw [pow_two, ← Real.exp_add]
  congr 1
  ring

/-- The null-face probability changes by at most one exponential factor. -/
theorem F_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.F (x + z) ≤ Real.exp (r / s.bandwidth) * s.F x :=
  FaceWeights.F_le_of_weights_le_one_factor (s.weights x) (s.weights (x + z))
    _ (s.one_le_shift_factor hz) (s.weight_le_shift x hz)

theorem F_le_shift (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.F x ≤ Real.exp (r / s.bandwidth) * s.F (x + z) :=
  FaceWeights.F_le_of_weights_le_one_factor (s.weights (x + z)) (s.weights x)
    _ (s.one_le_shift_factor hz) (s.weight_shift_le x hz)

/-- A normalized face probability changes by at most two exponential factors. -/
theorem pi_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (f : Face p) :
    s.pi (x + z) f ≤ Real.exp (2 * r / s.bandwidth) * s.pi x f := by
  simpa only [s.shift_factor_sq] using
    FaceWeights.pi_le_of_weights_le (s.weights x) (s.weights (x + z)) _
      (s.one_le_shift_factor hz) (s.weight_shift_le x hz) (s.weight_le_shift x hz) f

theorem pi_le_shift (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) (f : Face p) :
    s.pi x f ≤ Real.exp (2 * r / s.bandwidth) * s.pi (x + z) f := by
  simpa only [s.shift_factor_sq] using
    FaceWeights.pi_le_of_weights_le (s.weights (x + z)) (s.weights x) _
      (s.one_le_shift_factor hz) (s.weight_le_shift x hz) (s.weight_shift_le x hz) f

theorem theta_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) :
    s.theta (x + z) ≤ Real.exp (2 * r / s.bandwidth) * s.theta x := by
  change (s.weights (x + z)).theta ≤ _ * (s.weights x).theta
  rw [← FaceWeights.sum_pi, ← FaceWeights.sum_pi, Finset.mul_sum]
  exact Finset.sum_le_sum fun f _ => s.pi_shift_le x hz f

theorem theta_le_shift (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) :
    s.theta x ≤ Real.exp (2 * r / s.bandwidth) * s.theta (x + z) := by
  change (s.weights x).theta ≤ _ * (s.weights (x + z)).theta
  rw [← FaceWeights.sum_pi, ← FaceWeights.sum_pi, Finset.mul_sum]
  exact Finset.sum_le_sum fun f _ => s.pi_le_shift x hz f

private theorem F_shift_le_two (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.F (x + z) ≤ Real.exp (2 * r / s.bandwidth) * s.F x := by
  simpa only [s.shift_factor_sq] using
    FaceWeights.F_le_of_weights_le (s.weights x) (s.weights (x + z)) _
      (s.one_le_shift_factor hz) (s.weight_le_shift x hz)

private theorem F_le_shift_two (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.F x ≤ Real.exp (2 * r / s.bandwidth) * s.F (x + z) := by
  simpa only [s.shift_factor_sq] using
    FaceWeights.F_le_of_weights_le (s.weights (x + z)) (s.weights x) _
      (s.one_le_shift_factor hz) (s.weight_shift_le x hz)

theorem directionalCovariance_shift_le (x y : Fin p → ℝ)
    {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    (s.weights (x + z)).directionalCovariance y ≤
      Real.exp (2 * r / s.bandwidth) * (s.weights x).directionalCovariance y :=
  FaceWeights.directionalCovariance_le_of_probabilities_le
    (s.weights x) (s.weights (x + z)) _ (s.F_shift_le_two x hz)
    (s.pi_shift_le x hz) y

theorem directionalCovariance_le_shift (x y : Fin p → ℝ)
    {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    (s.weights x).directionalCovariance y ≤
      Real.exp (2 * r / s.bandwidth) * (s.weights (x + z)).directionalCovariance y :=
  FaceWeights.directionalCovariance_le_of_probabilities_le
    (s.weights (x + z)) (s.weights x) _ (s.F_le_shift_two x hz)
    (s.pi_le_shift x hz) y

private theorem exp_neg_mul_exp (r : ℝ) :
    Real.exp (-2 * r / s.bandwidth) * Real.exp (2 * r / s.bandwidth) = 1 := by
  rw [← Real.exp_add]
  convert Real.exp_zero using 1
  congr 1
  ring

/-- Stability of the positive Hessian quadratic form, with the stronger
factor two in the exponential. There is no restriction on the direction. -/
theorem directionalCovariance_stability (x y : Fin p → ℝ)
    {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    Real.exp (-2 * r / s.bandwidth) * (s.weights x).directionalCovariance y ≤
        (s.weights (x + z)).directionalCovariance y ∧
      (s.weights (x + z)).directionalCovariance y ≤
        Real.exp (2 * r / s.bandwidth) * (s.weights x).directionalCovariance y := by
  refine ⟨?_, s.directionalCovariance_shift_le x y hz⟩
  calc
    _ ≤ Real.exp (-2 * r / s.bandwidth) *
        (Real.exp (2 * r / s.bandwidth) *
          (s.weights (x + z)).directionalCovariance y) :=
      mul_le_mul_of_nonneg_left (s.directionalCovariance_le_shift x y hz)
        (Real.exp_nonneg _)
    _ = _ := by rw [← mul_assoc, s.exp_neg_mul_exp, one_mul]

theorem kappa_shift_le (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.kappa (x + z) ≤
      Real.exp (2 * r / s.bandwidth) * s.kappa x :=
  FaceWeights.kappa_le_of_probabilities_le
    (s.weights x) (s.weights (x + z)) _ (s.F_shift_le_two x hz) (s.pi_shift_le x hz)

theorem kappa_le_shift (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) : s.kappa x ≤
      Real.exp (2 * r / s.bandwidth) * s.kappa (x + z) :=
  FaceWeights.kappa_le_of_probabilities_le
    (s.weights (x + z)) (s.weights x) _ (s.F_le_shift_two x hz) (s.pi_le_shift x hz)

/-- Stability of the covariance trace (the curvature budget). -/
theorem kappa_stability (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) :
    Real.exp (-2 * r / s.bandwidth) * s.kappa x ≤ s.kappa (x + z) ∧
      s.kappa (x + z) ≤ Real.exp (2 * r / s.bandwidth) * s.kappa x := by
  refine ⟨?_, s.kappa_shift_le x hz⟩
  calc
    _ ≤ Real.exp (-2 * r / s.bandwidth) *
        (Real.exp (2 * r / s.bandwidth) * s.kappa (x + z)) :=
      mul_le_mul_of_nonneg_left (s.kappa_le_shift x hz) (Real.exp_nonneg _)
    _ = _ := by rw [← mul_assoc, s.exp_neg_mul_exp, one_mul]

/-- The exponent-four covariance stability used in the manuscript. -/
theorem directionalCovariance_stability_four (x y : Fin p → ℝ)
    {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    Real.exp (-4 * r / s.bandwidth) * (s.weights x).directionalCovariance y ≤
        (s.weights (x + z)).directionalCovariance y ∧
      (s.weights (x + z)).directionalCovariance y ≤
        Real.exp (4 * r / s.bandwidth) * (s.weights x).directionalCovariance y := by
  have hr := (norm_nonneg z).trans hz
  have hlow : -4 * r / s.bandwidth ≤ -2 * r / s.bandwidth := by
    exact div_le_div_of_nonneg_right (by nlinarith) s.bandwidth_pos.le
  have hupp : 2 * r / s.bandwidth ≤ 4 * r / s.bandwidth := by
    exact div_le_div_of_nonneg_right (by nlinarith) s.bandwidth_pos.le
  have h := s.directionalCovariance_stability x y hz
  exact ⟨(mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlow)
    ((s.weights x).directionalCovariance_nonneg y)).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hupp)
      ((s.weights x).directionalCovariance_nonneg y))⟩

theorem kappa_stability_four (x : Fin p → ℝ) {z : Fin p → ℝ} {r : ℝ}
    (hz : ‖z‖ ≤ r) :
    Real.exp (-4 * r / s.bandwidth) * s.kappa x ≤ s.kappa (x + z) ∧
      s.kappa (x + z) ≤ Real.exp (4 * r / s.bandwidth) * s.kappa x := by
  have hr := (norm_nonneg z).trans hz
  have hlow : -4 * r / s.bandwidth ≤ -2 * r / s.bandwidth := by
    exact div_le_div_of_nonneg_right (by nlinarith) s.bandwidth_pos.le
  have hupp : 2 * r / s.bandwidth ≤ 4 * r / s.bandwidth := by
    exact div_le_div_of_nonneg_right (by nlinarith) s.bandwidth_pos.le
  have h := s.kappa_stability x hz
  exact ⟨(mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlow)
    (s.weights x).kappa_nonneg).trans h.1,
    h.2.trans (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hupp)
      (s.weights x).kappa_nonneg)⟩

/-- The stability statement for actual second derivatives of the logarithmic
potential along arbitrary lines, rather than just a formal covariance tensor. -/
theorem second_deriv_potential_stability (x y : Fin p → ℝ)
    {z : Fin p → ℝ} {r : ℝ} (hz : ‖z‖ ≤ r) :
    Real.exp (-4 * r / s.bandwidth) *
        deriv (fun t => deriv (fun u => s.potential (line x y u)) t) 0 ≤
        deriv (fun t => deriv (fun u => s.potential (line (x + z) y u)) t) 0 ∧
      deriv (fun t => deriv (fun u => s.potential (line (x + z) y u)) t) 0 ≤
        Real.exp (4 * r / s.bandwidth) *
          deriv (fun t => deriv (fun u => s.potential (line x y u)) t) 0 := by
  simp only [s.second_deriv_potential_line, line_zero]
  have h := s.directionalCovariance_stability_four x y hz
  constructor
  · simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right h.1 s.bandwidth_pos.le
  · simpa only [mul_div_assoc] using
      div_le_div_of_nonneg_right h.2 s.bandwidth_pos.le

end FaceSmoother
end RectangleCLT
