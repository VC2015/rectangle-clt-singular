import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-! Numerical cutoff estimates for the sub-exponential argument.  The
parameters `n` and `p` are real casts of positive dimensions.  No probability
bound or Gaussian approximation theorem is assumed in this module. -/

namespace RectangleCLT

noncomputable section

def subexponentialCutoffHeight (n p : ℝ) : ℝ := Real.log (Real.exp 1 * n * p)

def subexponentialCutoff (n p K : ℝ) : ℝ :=
  64 * K * subexponentialCutoffHeight n p

def subexponentialCutoffProbability (n p K : ℝ) : ℝ :=
  2 * n * p * Real.exp (-subexponentialCutoff n p K / (2 * K))

theorem subexponentialCutoffHeight_eq {n p : ℝ} (hn : 0 < n) (hp : 0 < p) :
    subexponentialCutoffHeight n p = 1 + Real.log (n * p) := by
  unfold subexponentialCutoffHeight
  rw [mul_assoc, Real.log_mul (Real.exp_pos 1).ne' (mul_pos hn hp).ne', Real.log_exp]

theorem subexponentialCutoffHeight_ge_dimensionLog {n p : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    Real.log (Real.exp 1 * p) ≤ subexponentialCutoffHeight n p := by
  apply Real.log_le_log (mul_pos (Real.exp_pos _) (by linarith))
  have hmul := mul_le_mul_of_nonneg_right hn (mul_nonneg (Real.exp_pos 1).le (by linarith : 0 ≤ p))
  nlinarith only [hmul]

theorem subexponentialCutoffHeight_bounds {n p : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) :
    1 ≤ subexponentialCutoffHeight n p ∧ subexponentialCutoffHeight n p ≤ n * p := by
  have hn0 : 0 < n := by linarith
  have hp0 : 0 < p := by linarith
  have hx : 1 ≤ n * p := one_le_mul_of_one_le_of_one_le hn hp
  rw [subexponentialCutoffHeight_eq hn0 hp0]
  constructor
  · linarith [Real.log_nonneg hx]
  · linarith [Real.log_le_sub_one_of_pos (mul_pos hn0 hp0)]

theorem subexponentialCutoffProbability_nonneg {n p K : ℝ}
    (hn : 0 ≤ n) (hp : 0 ≤ p) :
    0 ≤ subexponentialCutoffProbability n p K := by
  unfold subexponentialCutoffProbability
  positivity

theorem subexponentialCutoffProbability_eq {n p K : ℝ}
    (hK : 0 < K) :
    subexponentialCutoffProbability n p K =
      2 * (n * p) / (Real.exp (subexponentialCutoffHeight n p)) ^ 32 := by
  have he : -subexponentialCutoff n p K / (2 * K) =
      -(32 * subexponentialCutoffHeight n p) := by
    unfold subexponentialCutoff
    field_simp [hK.ne']
    <;> ring
  unfold subexponentialCutoffProbability
  have hpow : Real.exp (32 * subexponentialCutoffHeight n p) =
      (Real.exp (subexponentialCutoffHeight n p)) ^ 32 := by
    simpa only [Nat.cast_ofNat] using Real.exp_nat_mul (subexponentialCutoffHeight n p) 32
  rw [he, Real.exp_neg, hpow]
  ring

/-- The generous logarithmic cutoff makes its square-root tail smaller
than a fixed reciprocal polynomial in both dimensions. -/
theorem subexponentialCutoffProbability_sqrt_bound {n p K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 0 < K) :
    16 * (n * p) ^ 4 * Real.sqrt (subexponentialCutoffProbability n p K) ≤ 1 := by
  let x := n * p
  let E := Real.exp (subexponentialCutoffHeight n p)
  have hx : 1 ≤ x := one_le_mul_of_one_le_of_one_le hn hp
  have hx0 : 0 < x := by linarith
  have hE : E = Real.exp 1 * x := by
    dsimp [E, subexponentialCutoffHeight, x]
    rw [Real.exp_log (by positivity)]
    ring
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hEx : 2 * x ≤ E := by rw [hE]; nlinarith only [he2, hx0]
  have hE1 : 1 ≤ E := by nlinarith only [hEx, hx]
  have hpow : 512 * x ^ 9 ≤ E ^ 32 := by
    have hx3 : 1 ≤ x ^ 3 := one_le_pow₀ hx
    have hleft : 512 * x ^ 9 ≤ (2 * x) ^ 12 := by
      have hh := mul_le_mul_of_nonneg_left hx3 (by positivity : 0 ≤ 512 * x ^ 9)
      nlinarith only [hh, pow_nonneg hx0.le 12]
    exact hleft.trans ((pow_le_pow_left₀ (by positivity) hEx 12).trans
      (pow_le_pow_right₀ hE1 (by decide : 12 ≤ 32)))
  have hq : subexponentialCutoffProbability n p K ≤ 1 / (256 * x ^ 8) := by
    rw [subexponentialCutoffProbability_eq hK]
    change 2 * x / E ^ 32 ≤ 1 / (256 * x ^ 8)
    apply (div_le_div_iff₀ (by positivity : 0 < E ^ 32) (by positivity : 0 < 256 * x ^ 8)).mpr
    convert hpow using 1 <;> ring
  have hq0 := subexponentialCutoffProbability_nonneg (K := K) (by linarith : 0 ≤ n) (by linarith : 0 ≤ p)
  have hs0 : 0 ≤ Real.sqrt (subexponentialCutoffProbability n p K) := Real.sqrt_nonneg _
  have hs : Real.sqrt (subexponentialCutoffProbability n p K) ≤ 1 / (16 * x ^ 4) := by
    apply (sq_le_sq₀ hs0 (by positivity)).mp
    rw [Real.sq_sqrt hq0]
    convert hq using 1 <;> field_simp <;> ring
  have h := mul_le_mul_of_nonneg_left hs (by positivity : 0 ≤ 16 * x ^ 4)
  convert h using 1 <;> dsimp [x] <;> field_simp <;> ring

theorem subexponentialCutoff_radius_bound {n B u y : ℝ}
    (hn : 1 ≤ n) (hB0 : 0 ≤ B) (hB : B ≤ Real.sqrt n)
    (hu0 : 0 ≤ u) (hu : u ≤ 64 * Real.sqrt n) (hy : 0 ≤ y) :
    Real.sqrt n * y + (4 * B * y) * (2 * n * u / Real.sqrt n) ≤
      513 * n ^ 2 * y := by
  have hn0 : 0 < n := by linarith
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn : Real.sqrt n ≤ n := (Real.sqrt_le_iff).mpr ⟨hn0.le, by nlinarith⟩
  have hn2 : n ≤ n ^ 2 := by nlinarith
  have hBn : B ≤ n := hB.trans hsn
  have hud : u / Real.sqrt n ≤ 64 := (div_le_iff₀ hs).mpr hu
  have hprod := mul_le_mul hBn hud (div_nonneg hu0 hs.le) hn0.le
  have hcoef := mul_le_mul_of_nonneg_left hprod (by positivity : 0 ≤ 8 * n)
  have hcoef' : 8 * B * n * (u / Real.sqrt n) ≤ 512 * n ^ 2 := by
    nlinarith only [hcoef]
  have hsecond := mul_le_mul_of_nonneg_right hcoef' hy
  have hfirst := mul_le_mul_of_nonneg_right (hsn.trans hn2) hy
  have hid : (4 * B * y) * (2 * n * u / Real.sqrt n) =
      (8 * B * n * (u / Real.sqrt n)) * y := by ring
  rw [hid]
  nlinarith only [hfirst, hsecond]

theorem subexponentialCutoff_epsilon_small {n p K B : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 0 < K)
    (hB0 : 0 ≤ B) (hB : B ≤ Real.sqrt n) :
    2 * B * Real.sqrt (subexponentialCutoffProbability n p K) < 1 / 2 := by
  let x := n * p
  let y := Real.sqrt (subexponentialCutoffProbability n p K)
  have hx : 1 ≤ x := one_le_mul_of_one_le_of_one_le hn hp
  have hn0 : 0 < n := by linarith
  have hnX : n ≤ x := by dsimp [x]; nlinarith only [hp, hn0]
  have hsN : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
  have hx4 : x ≤ x ^ 4 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hx (by decide : 1 ≤ 4))
  have hBx : B ≤ x ^ 4 := (hB.trans hsN).trans (hnX.trans hx4)
  have hroot := subexponentialCutoffProbability_sqrt_bound hn hp hK
  change 16 * x ^ 4 * y ≤ 1 at hroot
  have hmult := mul_le_mul_of_nonneg_right hBx (Real.sqrt_nonneg
    (subexponentialCutoffProbability n p K))
  change B * y ≤ x ^ 4 * y at hmult
  change 2 * B * y < 1 / 2
  nlinarith only [hroot, hmult]

/-- All extra costs of the actual coupling and fixed-proxy variance loss
are absorbed by the original envelope term in the nontrivial rate branch.
The large numerical constant is absolute and independent of both scales. -/
theorem subexponentialCutoff_extra_cost_le {n p K B L c : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 1 ≤ K) (hB0 : 0 ≤ B)
    (hB : B ≤ Real.sqrt n)
    (hKH : K * subexponentialCutoffHeight n p ≤ Real.sqrt n)
    (hL : 1 ≤ L) (hLH : L ≤ subexponentialCutoffHeight n p)
    (hc : 0 < c) (hc1 : c ≤ 1) :
    let q := subexponentialCutoffProbability n p K
    let u := subexponentialCutoff n p K
    let r := Real.sqrt n * Real.sqrt q +
      (4 * B * Real.sqrt q) * (2 * n * u / Real.sqrt n)
    (4 * B * Real.sqrt q) * L / c + q + 4 * p * r ≤
      256 * (K * subexponentialCutoffHeight n p * Real.sqrt L) / (c * Real.sqrt n) := by
  let q := subexponentialCutoffProbability n p K
  let y := Real.sqrt q
  let u := subexponentialCutoff n p K
  let r := Real.sqrt n * y + (4 * B * y) * (2 * n * u / Real.sqrt n)
  let x := n * p
  have hn0 : 0 < n := by linarith
  have hp0 : 0 < p := by linarith
  have hK0 : 0 < K := by linarith
  have hH := (subexponentialCutoffHeight_bounds hn hp).1
  have hy : 0 ≤ y := Real.sqrt_nonneg _
  have hq : 0 ≤ q := subexponentialCutoffProbability_nonneg hn0.le hp0.le
  have hs : 0 < Real.sqrt n := Real.sqrt_pos.mpr hn0
  have hsn : Real.sqrt n ≤ n := Real.sqrt_le_iff.mpr ⟨hn0.le, by nlinarith⟩
  have hx : 1 ≤ x := one_le_mul_of_one_le_of_one_le hn hp
  have hnX : n ≤ x := by dsimp [x]; nlinarith only [hp, hn0]
  have hpX : p ≤ x := by dsimp [x]; nlinarith only [hn, hp0]
  have hsX : Real.sqrt n ≤ x := hsn.trans hnX
  have hx4 : 1 ≤ x ^ 4 := one_le_pow₀ hx
  have hx14 : x ≤ x ^ 4 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hx (by decide : 1 ≤ 4))
  have hx24 : x ^ 2 ≤ x ^ 4 := pow_le_pow_right₀ hx (by decide : 2 ≤ 4)
  have hroot := subexponentialCutoffProbability_sqrt_bound hn hp hK0
  change 16 * x ^ 4 * y ≤ 1 at hroot
  have hyle : y ≤ x ^ 4 * y := by nlinarith only [mul_le_mul_of_nonneg_right hx4 hy]
  have hy1 : y ≤ 1 := by nlinarith only [hroot, hyle]
  have hqy : q ≤ y := by
    have hsq : y ^ 2 = q := Real.sq_sqrt hq
    nlinarith only [hsq, hy, hy1]
  have hqs : q * Real.sqrt n ≤ 1 := by
    have h := mul_le_mul hqy (hsX.trans hx14) hs.le hy
    nlinarith only [h, hroot]
  have hHle : subexponentialCutoffHeight n p ≤ Real.sqrt n := by
    have hh := mul_le_mul_of_nonneg_right hK (by linarith : 0 ≤ subexponentialCutoffHeight n p)
    nlinarith only [hh, hKH]
  have hLn : L ≤ Real.sqrt n := hLH.trans hHle
  have hBL : B * L ≤ n := by
    have h := mul_le_mul hB hLn (by linarith : 0 ≤ L) hs.le
    rw [← pow_two, Real.sq_sqrt hn0.le] at h
    exact h
  have hBLs : B * L * Real.sqrt n ≤ x ^ 4 := by
    calc
      _ ≤ n * n := mul_le_mul hBL hsn hs.le hn0.le
      _ = n ^ 2 := (pow_two n).symm
      _ ≤ x ^ 2 := pow_le_pow_left₀ hn0.le hnX 2
      _ ≤ x ^ 4 := hx24
  have hcov : 4 * B * y * L * Real.sqrt n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hBLs hy
    nlinarith only [h, hroot]
  have hu0 : 0 ≤ u := by dsimp [u, subexponentialCutoff]; positivity
  have hu : u ≤ 64 * Real.sqrt n := by
    dsimp [u, subexponentialCutoff]
    nlinarith only [hKH]
  have hr : r ≤ 513 * n ^ 2 * y :=
    subexponentialCutoff_radius_bound hn hB0 hB hu0 hu hy
  have hr0 : 0 ≤ r := by dsimp [r]; positivity
  have hps : p * Real.sqrt n ≤ x * x :=
    mul_le_mul hpX hsX hs.le (by linarith : 0 ≤ x)
  have hcoef : p * n ^ 2 * Real.sqrt n ≤ x ^ 4 := by
    have h := mul_le_mul (pow_le_pow_left₀ hn0.le hnX 2) hps
      (mul_nonneg hp0.le hs.le) (sq_nonneg x)
    nlinarith only [h]
  have hrad : 4 * p * r * Real.sqrt n ≤ 129 := by
    have h := mul_le_mul_of_nonneg_left hr (mul_nonneg hp0.le hs.le)
    have h' := mul_le_mul_of_nonneg_right hcoef hy
    nlinarith only [h, h', hroot]
  have hqcs : c * q * Real.sqrt n ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right hc1 (mul_nonneg hq hs.le)
    nlinarith only [h, hqs]
  have hrcs : 4 * c * p * r * Real.sqrt n ≤ 129 := by
    have h := mul_le_mul_of_nonneg_right hc1
      (by positivity : 0 ≤ 4 * p * r * Real.sqrt n)
    nlinarith only [h, hrad]
  have hKH1 : 1 ≤ K * subexponentialCutoffHeight n p :=
    one_le_mul_of_one_le_of_one_le hK hH
  have hscale : 1 ≤ K * subexponentialCutoffHeight n p * Real.sqrt L :=
    one_le_mul_of_one_le_of_one_le hKH1 (Real.one_le_sqrt.mpr hL)
  change (4 * B * y) * L / c + q + 4 * p * r ≤ _
  apply (le_div_iff₀ (mul_pos hc hs)).mpr
  have hid : ((4 * B * y) * L / c + q + 4 * p * r) * (c * Real.sqrt n) =
      4 * B * y * L * Real.sqrt n + c * q * Real.sqrt n +
        4 * c * p * r * Real.sqrt n := by field_simp [hc.ne']; ring
  rw [hid]
  nlinarith only [hcov, hqcs, hrcs, hscale]

end

end RectangleCLT
