import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Push

/-! The finite algebra behind the rational rectangle smoother. Curvature is
represented here by its explicit algebraic expression; this file does not
identify it with a second derivative. -/

open scoped BigOperators

namespace RectangleCLT

/-- Distinct signed coordinate faces; `true` denotes the positive normal. -/
abbrev Face (p : ℕ) := Fin p × Bool

/-- Nonnegative weights on distinct signed coordinate normals. Zero weights
allow a finite collection of faces to omit any of the `2p` normals. -/
structure FaceWeights (p : ℕ) where
  weight : Face p → ℝ
  nonneg : ∀ f, 0 ≤ weight f

namespace FaceWeights

variable {p : ℕ} (w : FaceWeights p)

noncomputable def T : ℝ := ∑ f, w.weight f
noncomputable def F : ℝ := 1 / (1 + w.T)
noncomputable def pi (f : Face p) : ℝ := w.weight f / (1 + w.T)
noncomputable def theta : ℝ := 1 - w.F
noncomputable def v (j : Fin p) : ℝ := w.pi (j, true) - w.pi (j, false)
noncomputable def normSq : ℝ := ∑ j, w.v j ^ 2
/-- The algebraic curvature quantity appearing in the endpoint estimate. -/
noncomputable def kappa : ℝ := w.theta - w.normSq

theorem T_nonneg : 0 ≤ w.T :=
  Finset.sum_nonneg (fun f _ => w.nonneg f)

theorem denominator_pos : 0 < 1 + w.T := by linarith [w.T_nonneg]

theorem F_pos : 0 < w.F := one_div_pos.mpr w.denominator_pos

theorem F_le_one : w.F ≤ 1 := by
  unfold F
  exact (div_le_one w.denominator_pos).2 (by linarith [w.T_nonneg])

theorem pi_nonneg (f : Face p) : 0 ≤ w.pi f :=
  div_nonneg (w.nonneg f) w.denominator_pos.le

theorem weight_le_T (f : Face p) : w.weight f ≤ w.T :=
  Finset.single_le_sum (fun g _ => w.nonneg g) (Finset.mem_univ f)

theorem sum_pi : ∑ f, w.pi f = w.theta := by
  unfold pi theta F
  simp only [div_eq_mul_inv, ← Finset.sum_mul]
  change w.T * (1 + w.T)⁻¹ = 1 - 1 * (1 + w.T)⁻¹
  field_simp [ne_of_gt w.denominator_pos]

theorem normalization : w.F + ∑ f, w.pi f = 1 := by
  rw [w.sum_pi]
  simp [theta]

theorem theta_nonneg : 0 ≤ w.theta := sub_nonneg.mpr w.F_le_one

theorem theta_lt_one : w.theta < 1 := by
  unfold theta
  linarith [w.F_pos]

theorem theta_eq_T_div : w.theta = w.T / (1 + w.T) := by
  rw [← w.sum_pi]
  simp only [pi, div_eq_mul_inv, ← Finset.sum_mul, T]

theorem pi_le_theta (f : Face p) : w.pi f ≤ w.theta := by
  rw [← w.sum_pi]
  exact Finset.single_le_sum (fun g _ => w.pi_nonneg g) (Finset.mem_univ f)

 private theorem sum_faces (g : Face p → ℝ) :
    ∑ f, g f = ∑ j : Fin p, (g (j, true) + g (j, false)) := by
  simp [Fintype.sum_prod_type, Fintype.sum_bool]

theorem sum_abs_v_le_theta : (∑ j, |w.v j|) ≤ w.theta := by
  calc
    _ ≤ ∑ j : Fin p, (w.pi (j, true) + w.pi (j, false)) := by
      apply Finset.sum_le_sum
      intro j _
      unfold v
      apply abs_le.mpr
      constructor <;> linarith [w.pi_nonneg (j, true), w.pi_nonneg (j, false)]
    _ = ∑ f, w.pi f := (sum_faces w.pi).symm
    _ = w.theta := w.sum_pi

theorem sum_abs_v_le_one : (∑ j, |w.v j|) ≤ 1 :=
  w.sum_abs_v_le_theta.trans w.theta_lt_one.le

/-- Opposite faces make a nonpositive cross term; distinct coordinate faces
have no cross term at all. -/
theorem normSq_le_sum_pi_sq : w.normSq ≤ ∑ f, w.pi f ^ 2 := by
  rw [sum_faces]
  unfold normSq
  apply Finset.sum_le_sum
  intro j _
  unfold v
  nlinarith [mul_nonneg (w.pi_nonneg (j, true)) (w.pi_nonneg (j, false))]

theorem normSq_le_theta_mul (b : ℝ) (hb : ∀ f, w.pi f ≤ b) :
    w.normSq ≤ w.theta * b := by
  calc
    w.normSq ≤ ∑ f, w.pi f ^ 2 := w.normSq_le_sum_pi_sq
    _ ≤ ∑ f, w.pi f * b := by
      apply Finset.sum_le_sum
      intro f _
      nlinarith [mul_nonneg (w.pi_nonneg f) (sub_nonneg.mpr (hb f))]
    _ = w.theta * b := by rw [← Finset.sum_mul, w.sum_pi]

theorem normSq_le_theta_sq : w.normSq ≤ w.theta ^ 2 := by
  simpa only [pow_two] using w.normSq_le_theta_mul w.theta w.pi_le_theta

theorem kappa_ge_theta_mul_one_sub_theta :
    w.theta * (1 - w.theta) ≤ w.kappa := by
  unfold kappa
  nlinarith [w.normSq_le_theta_sq]

theorem kappa_ge_theta_mul_one_sub (b : ℝ) (hb : ∀ f, w.pi f ≤ b) :
    w.theta * (1 - b) ≤ w.kappa := by
  unfold kappa
  nlinarith [w.normSq_le_theta_mul b hb]

theorem kappa_nonneg : 0 ≤ w.kappa :=
  (mul_nonneg w.theta_nonneg (by linarith [w.theta_lt_one])).trans
    w.kappa_ge_theta_mul_one_sub_theta

/-- A face with weight at most one has normalized weight at most one half. -/
theorem pi_le_half_of_weight_le_one (f : Face p) (hf : w.weight f ≤ 1) :
    w.pi f ≤ 1 / 2 := by
  unfold pi
  apply (div_le_iff₀ w.denominator_pos).2
  linarith [w.weight_le_T f]

theorem half_le_theta_of_one_le_T (hT : 1 ≤ w.T) : 1 / 2 ≤ w.theta := by
  rw [w.theta_eq_T_div]
  apply (le_div_iff₀ w.denominator_pos).2
  linarith

theorem half_lt_theta_of_one_lt_T (hT : 1 < w.T) : 1 / 2 < w.theta := by
  rw [w.theta_eq_T_div]
  apply (lt_div_iff₀ w.denominator_pos).2
  linarith

theorem error_inside (hw : ∀ f, w.weight f ≤ 1) : |w.F - 1| ≤ 2 * w.kappa := by
  have hk := w.kappa_ge_theta_mul_one_sub (1 / 2)
    (fun f => w.pi_le_half_of_weight_le_one f (hw f))
  rw [abs_of_nonpos (sub_nonpos.mpr w.F_le_one)]
  unfold theta at hk
  linarith

theorem error_outside (hT : 1 ≤ w.T) : |w.F - 0| ≤ 2 * w.kappa := by
  have ht := w.half_le_theta_of_one_le_T hT
  have hk := w.kappa_ge_theta_mul_one_sub_theta
  have hp := mul_nonneg (sub_nonneg.mpr ht) w.F_pos.le
  simp only [sub_zero, abs_of_pos w.F_pos]
  unfold theta at ht hk hp
  nlinarith

/-- The diagonal of the covariance matrix of the signed face normals and the
zero normal, with probabilities `pi` and `F`. -/
noncomputable def covarianceDiagonal (j : Fin p) : ℝ :=
  w.pi (j, true) + w.pi (j, false) - w.v j ^ 2

/-- The covariance trace is exactly the algebraic curvature quantity. This is
an algebraic identity, independent of differentiation. -/
theorem covariance_trace_eq_kappa : ∑ j, w.covarianceDiagonal j = w.kappa := by
  unfold covarianceDiagonal kappa normSq
  rw [Finset.sum_sub_distrib, ← sum_faces, w.sum_pi]

/-- Evaluation of a signed face normal on a test vector. -/
def directionalValue (f : Face p) (z : Fin p → ℝ) : ℝ :=
  if f.2 then z f.1 else -z f.1

noncomputable def directionalMean (z : Fin p → ℝ) : ℝ :=
  ∑ f, w.pi f * directionalValue f z

noncomputable def directionalSecondMoment (z : Fin p → ℝ) : ℝ :=
  ∑ f, w.pi f * directionalValue f z ^ 2

noncomputable def directionalCovariance (z : Fin p → ℝ) : ℝ :=
  w.directionalSecondMoment z - w.directionalMean z ^ 2

theorem directionalMean_eq (z : Fin p → ℝ) :
    w.directionalMean z = ∑ j, w.v j * z j := by
  unfold directionalMean
  rw [sum_faces]
  apply Finset.sum_congr rfl
  intro j _
  simp only [directionalValue, Bool.false_eq_true, ↓reduceIte, v]
  ring

theorem directionalSecondMoment_eq (z : Fin p → ℝ) :
    w.directionalSecondMoment z =
      ∑ j, (w.pi (j, true) + w.pi (j, false)) * z j ^ 2 := by
  unfold directionalSecondMoment
  rw [sum_faces]
  apply Finset.sum_congr rfl
  intro j _
  simp only [directionalValue, Bool.false_eq_true, ↓reduceIte]
  ring

/-- The variance decomposition includes the zero normal with mass `F`. -/
theorem directionalCovariance_eq_variance (z : Fin p → ℝ) :
    w.directionalCovariance z =
      w.F * w.directionalMean z ^ 2 +
        ∑ f, w.pi f * (directionalValue f z - w.directionalMean z) ^ 2 := by
  have hexpand :
      (∑ f, w.pi f * (directionalValue f z - w.directionalMean z) ^ 2) =
        w.directionalSecondMoment z -
          (2 * w.directionalMean z) * w.directionalMean z +
          w.directionalMean z ^ 2 * w.theta := by
    calc
      _ = ∑ f, (w.pi f * directionalValue f z ^ 2 -
          (2 * w.directionalMean z) * (w.pi f * directionalValue f z) +
          w.directionalMean z ^ 2 * w.pi f) := by
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

theorem directionalCovariance_nonneg (z : Fin p → ℝ) :
    0 ≤ w.directionalCovariance z := by
  rw [w.directionalCovariance_eq_variance]
  exact add_nonneg (mul_nonneg w.F_pos.le (sq_nonneg _))
    (Finset.sum_nonneg (fun f _ => mul_nonneg (w.pi_nonneg f) (sq_nonneg _)))

/-- Positive semidefiniteness of the explicit coordinate covariance quadratic
form. No identification with a Hessian is used in this algebraic statement. -/
theorem covariance_quadratic_nonneg (z : Fin p → ℝ) :
    0 ≤ (∑ j, (w.pi (j, true) + w.pi (j, false)) * z j ^ 2) -
      (∑ j, w.v j * z j) ^ 2 := by
  simpa only [directionalCovariance, w.directionalMean_eq,
    w.directionalSecondMoment_eq] using w.directionalCovariance_nonneg z

end FaceWeights

/-- A finite family of distinct signed coordinate faces and a positive smoothing
bandwidth. Rectangles with missing faces and empty face collections are allowed. -/
structure FaceSmoother (p : ℕ) where
  faces : Finset (Face p)
  offsets : Face p → ℝ
  bandwidth : ℝ
  bandwidth_pos : 0 < bandwidth

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- Evaluation of the signed coordinate normal at a point. -/
def normalDot (f : Face p) (x : Fin p → ℝ) : ℝ :=
  if f.2 then x f.1 else -x f.1

def faceScore (f : Face p) (x : Fin p → ℝ) : ℝ :=
  normalDot f x - s.offsets f

/-- Membership in the closed rectangle specified by the finite face family. -/
def Inside (x : Fin p → ℝ) : Prop := ∀ f ∈ s.faces, s.faceScore f x ≤ 0

noncomputable def weights (x : Fin p → ℝ) : FaceWeights p where
  weight f := if f ∈ s.faces then Real.exp (s.faceScore f x / s.bandwidth) else 0
  nonneg f := by split_ifs <;> positivity

noncomputable def F (x : Fin p → ℝ) : ℝ := (s.weights x).F
noncomputable def pi (x : Fin p → ℝ) (f : Face p) : ℝ := (s.weights x).pi f
noncomputable def theta (x : Fin p → ℝ) : ℝ := (s.weights x).theta
noncomputable def v (x : Fin p → ℝ) : Fin p → ℝ := (s.weights x).v
noncomputable def kappa (x : Fin p → ℝ) : ℝ := (s.weights x).kappa
noncomputable def potential (x : Fin p → ℝ) : ℝ :=
  s.bandwidth * Real.log (1 + (s.weights x).T)

noncomputable def indicator (x : Fin p → ℝ) : ℝ := by
  classical
  exact if s.Inside x then 1 else 0

theorem F_pos (x : Fin p → ℝ) : 0 < s.F x := (s.weights x).F_pos
theorem F_le_one (x : Fin p → ℝ) : s.F x ≤ 1 := (s.weights x).F_le_one

theorem inside_weights_le_one (x : Fin p → ℝ) (hx : s.Inside x) :
    ∀ f, (s.weights x).weight f ≤ 1 := by
  intro f
  by_cases hf : f ∈ s.faces
  · simp only [weights, hf, ↓reduceIte]
    apply Real.exp_le_one_iff.mpr
    exact div_nonpos_of_nonpos_of_nonneg (hx f hf) s.bandwidth_pos.le
  · simp [weights, hf]

theorem outside_one_lt_T (x : Fin p → ℝ) (hx : ¬s.Inside x) :
    1 < (s.weights x).T := by
  unfold Inside at hx
  push_neg at hx
  obtain ⟨f, hf, hscore⟩ := hx
  have hw : 1 < (s.weights x).weight f := by
    simp only [weights, hf, ↓reduceIte]
    exact Real.one_lt_exp_iff.mpr (div_pos hscore s.bandwidth_pos)
  exact hw.trans_le ((s.weights x).weight_le_T f)

theorem inside_pi_le_half (x : Fin p → ℝ) (hx : s.Inside x) (f : Face p) :
    s.pi x f ≤ 1 / 2 :=
  (s.weights x).pi_le_half_of_weight_le_one f (s.inside_weights_le_one x hx f)

theorem outside_half_lt_theta (x : Fin p → ℝ) (hx : ¬s.Inside x) :
    1 / 2 < s.theta x :=
  (s.weights x).half_lt_theta_of_one_lt_T (s.outside_one_lt_T x hx)

/-- The pointwise endpoint estimate for the explicit rational rectangle smoother.
Here `kappa = theta - sum_j (pi_(j,+) - pi_(j,-))^2`. -/
theorem endpoint_error (x : Fin p → ℝ) :
    |s.F x - s.indicator x| ≤ 2 * s.kappa x := by
  classical
  by_cases hx : s.Inside x
  · simpa only [F, kappa, indicator, if_pos hx] using
      (s.weights x).error_inside (s.inside_weights_le_one x hx)
  · simpa only [F, kappa, indicator, if_neg hx] using
      (s.weights x).error_outside (s.outside_one_lt_T x hx).le

end FaceSmoother

end RectangleCLT
