import Mathlib.Probability.Moments.Basic
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Data.Complex.Exponential
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FunProp

/-! Scalar clipping and the exponentially small residual used in the
sub-exponential extension. All bounds refer to the actual residual random
variable, and no tail or concentration assertion is assumed as a premise. -/

open MeasureTheory ProbabilityTheory Real

namespace RectangleCLT.Companion

noncomputable section

def clipAt (T x : ℝ) : ℝ := max (-T) (min T x)

def clipResidual (T x : ℝ) : ℝ := x - clipAt T x

theorem clipAt_continuous (T : ℝ) : Continuous (clipAt T) := by
  unfold clipAt
  fun_prop

theorem clipResidual_continuous (T : ℝ) : Continuous (clipResidual T) := by
  exact continuous_id.sub (clipAt_continuous T)

theorem abs_clipAt_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : |clipAt T x| ≤ T := by
  rw [abs_le]
  exact ⟨le_max_left _ _, max_le (by linarith) (min_le_left _ _)⟩

theorem clipResidual_eq_zero {T x : ℝ} (hx : |x| ≤ T) : clipResidual T x = 0 := by
  rcases abs_le.mp hx with ⟨hl, hu⟩
  simp [clipResidual, clipAt, min_eq_right hu, max_eq_right hl]

theorem abs_clipResidual (T x : ℝ) (hT : 0 ≤ T) :
    |clipResidual T x| = max 0 (|x| - T) := by
  by_cases hx : T ≤ x
  · have hx0 : 0 ≤ x := hT.trans hx
    rw [abs_of_nonneg hx0, max_eq_right (sub_nonneg.mpr hx)]
    simp [clipResidual, clipAt, min_eq_left hx, max_eq_right (by linarith : -T ≤ T),
      abs_of_nonneg (sub_nonneg.mpr hx)]
  · have hxT : x ≤ T := (lt_of_not_ge hx).le
    by_cases hl : x ≤ -T
    · have hx0 : x ≤ 0 := hl.trans (by linarith)
      rw [abs_of_nonpos hx0, max_eq_right (by linarith : 0 ≤ -x - T)]
      simp [clipResidual, clipAt, min_eq_right hxT, max_eq_left hl,
        abs_of_nonpos (by linarith : x - -T ≤ 0)]
    · have hlow : -T ≤ x := (lt_of_not_ge hl).le
      have habs : |x| ≤ T := abs_le.mpr ⟨hlow, hxT⟩
      rw [clipResidual_eq_zero habs, abs_zero, max_eq_left (sub_nonpos.mpr habs)]

theorem abs_clipResidual_le {T : ℝ} (hT : 0 ≤ T) (x : ℝ) :
    |clipResidual T x| ≤ |x| := by
  rw [abs_clipResidual T x hT]
  exact max_le (abs_nonneg _) (by linarith)

theorem abs_clipResidual_eq_sub {T x : ℝ} (hT : 0 ≤ T) (hx : T < |x|) :
    |clipResidual T x| = |x| - T := by
  rw [abs_clipResidual T x hT, max_eq_right (sub_nonneg.mpr hx.le)]

private theorem square_le_two_mul_exp {y : ℝ} (hy : 0 ≤ y) :
    y ^ 2 ≤ 2 * Real.exp y := by
  have h := Real.pow_div_factorial_le_exp hy 2
  norm_num at h
  linarith

/-- A pointwise exponentially small second-moment majorant. -/
theorem clipResidual_sq_le_exp {K u : ℝ} (hK : 0 < K) (hu : 0 ≤ u) (x : ℝ) :
    clipResidual (K * u) x ^ 2 ≤
      2 * K ^ 2 * Real.exp (-u) * Real.exp (|x| / K) := by
  have hT : 0 ≤ K * u := mul_nonneg hK.le hu
  by_cases hx : |x| ≤ K * u
  · rw [clipResidual_eq_zero hx]
    positivity
  · have hx' : K * u < |x| := lt_of_not_ge hx
    let r := |clipResidual (K * u) x|
    have hr : 0 ≤ r := abs_nonneg _
    have hre : r = |x| - K * u := abs_clipResidual_eq_sub hT hx'
    have hsq := square_le_two_mul_exp (div_nonneg hr hK.le)
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg K)
    have hpow : (r / K) ^ 2 * K ^ 2 = r ^ 2 := by field_simp [hK.ne']; ring
    rw [hpow] at hmul
    have he : Real.exp (r / K) = Real.exp (-u) * Real.exp (|x| / K) := by
      rw [hre, sub_div, mul_div_cancel_left₀ u hK.ne', Real.exp_sub,
        Real.exp_neg]
      ring
    rw [he] at hmul
    dsimp only [r] at hmul
    rw [sq_abs] at hmul
    nlinarith

/-- A residual-weighted exponential majorant. The restriction on the
Laplace parameter is the sole source of the linear Bernstein scale. -/
theorem clipResidual_sq_exp_le {K u t : ℝ} (hK : 0 < K) (hu : 0 ≤ u)
    (ht : |t| ≤ 1 / (2 * K)) (x : ℝ) :
    clipResidual (K * u) x ^ 2 * Real.exp (|t * clipResidual (K * u) x|) ≤
      8 * K ^ 2 * Real.exp (-u) * Real.exp (|x| / K) := by
  have hT : 0 ≤ K * u := mul_nonneg hK.le hu
  by_cases hx : |x| ≤ K * u
  · rw [clipResidual_eq_zero hx]
    positivity
  · have hx' : K * u < |x| := lt_of_not_ge hx
    let r := |clipResidual (K * u) x|
    have hr : 0 ≤ r := abs_nonneg _
    have hre : r = |x| - K * u := abs_clipResidual_eq_sub hT hx'
    have hsq := square_le_two_mul_exp (div_nonneg hr (by positivity : 0 ≤ 2 * K))
    have hmul := mul_le_mul_of_nonneg_right hsq (sq_nonneg (2 * K))
    have hpow : (r / (2 * K)) ^ 2 * (2 * K) ^ 2 = r ^ 2 := by field_simp [hK.ne']; ring
    rw [hpow] at hmul
    have hs : r ^ 2 ≤ 8 * K ^ 2 * Real.exp (r / (2 * K)) := by nlinarith
    have ht' : |t * clipResidual (K * u) x| ≤ r / (2 * K) := by
      rw [abs_mul]
      change |t| * r ≤ r / (2 * K)
      nlinarith [mul_le_mul_of_nonneg_right ht hr]
    have he : Real.exp (r / (2 * K)) * Real.exp (r / (2 * K)) =
        Real.exp (-u) * Real.exp (|x| / K) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      rw [hre]
      field_simp [hK.ne']
      ring
    calc
      _ = r ^ 2 * Real.exp (|t * clipResidual (K * u) x|) := by rw [r, sq_abs]
      _ ≤ (8 * K ^ 2 * Real.exp (r / (2 * K))) * Real.exp (r / (2 * K)) :=
        mul_le_mul hs (Real.exp_le_exp.mpr ht') (Real.exp_nonneg _) (by positivity)
      _ = _ := by rw [mul_assoc, he]; ring

/-- Integrability is included explicitly: Bochner integrals are totalized,
so a numerical exponential-moment bound alone would be insufficient. -/
structure ExponentialMomentBound {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) (K : ℝ) : Prop where
  measurable : Measurable X
  scale_pos : 0 < K
  integrable_exp : Integrable (fun ω => Real.exp (|X ω| / K)) μ
  integral_exp_le : (∫ ω, Real.exp (|X ω| / K) ∂μ) ≤ 2

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem ExponentialMomentBound.integrable_residual {X : Ω → ℝ} {K u : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) :
    Integrable (fun ω => clipResidual (K * u) (X ω)) μ := by
  have hm : Measurable (fun ω => clipResidual (K * u) (X ω)) :=
    (clipResidual_continuous _).measurable.comp h.measurable
  refine (h.integrable_exp.const_mul K).mono hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  calc
    |clipResidual (K * u) (X ω)| ≤ |X ω| :=
      abs_clipResidual_le (mul_nonneg h.scale_pos.le hu) _
    _ = K * (|X ω| / K) := by field_simp [h.scale_pos.ne']
    _ ≤ K * Real.exp (|X ω| / K) :=
      mul_le_mul_of_nonneg_left (by linarith [Real.add_one_le_exp (|X ω| / K)]) h.scale_pos.le

theorem ExponentialMomentBound.integrable_residual_sq {X : Ω → ℝ} {K u : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) :
    Integrable (fun ω => clipResidual (K * u) (X ω) ^ 2) μ := by
  have hm : Measurable (fun ω => clipResidual (K * u) (X ω) ^ 2) :=
    ((clipResidual_continuous _).measurable.comp h.measurable).pow_const 2
  refine (h.integrable_exp.const_mul (2 * K ^ 2 * Real.exp (-u))).mono
    hm.aestronglyMeasurable (ae_of_all _ fun ω => ?_)
  simp only [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _),
    abs_of_nonneg (show 0 ≤ 2 * K ^ 2 * Real.exp (-u) * Real.exp (|X ω| / K) by positivity)]
  exact clipResidual_sq_le_exp h.scale_pos hu _

theorem ExponentialMomentBound.integral_residual_sq_le {X : Ω → ℝ} {K u : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) :
    (∫ ω, clipResidual (K * u) (X ω) ^ 2 ∂μ) ≤ 4 * K ^ 2 * Real.exp (-u) := by
  have hi := h.integrable_residual_sq hu
  have hc : 0 ≤ 2 * K ^ 2 * Real.exp (-u) := by positivity
  calc
    _ ≤ ∫ ω, 2 * K ^ 2 * Real.exp (-u) * Real.exp (|X ω| / K) ∂μ :=
      integral_mono hi (h.integrable_exp.const_mul _) (fun ω =>
        clipResidual_sq_le_exp h.scale_pos hu _)
    _ = (2 * K ^ 2 * Real.exp (-u)) * (∫ ω, Real.exp (|X ω| / K) ∂μ) :=
      integral_const_mul _ _
    _ ≤ (2 * K ^ 2 * Real.exp (-u)) * 2 :=
      mul_le_mul_of_nonneg_left h.integral_exp_le hc
    _ = _ := by ring

theorem ExponentialMomentBound.integrable {X : Ω → ℝ} {K : ℝ}
    (h : ExponentialMomentBound μ X K) : Integrable X μ := by
  simpa [clipResidual, clipAt] using h.integrable_residual (u := 0) (by norm_num)

theorem ExponentialMomentBound.integrable_sq {X : Ω → ℝ} {K : ℝ}
    (h : ExponentialMomentBound μ X K) : Integrable (fun ω => X ω ^ 2) μ := by
  simpa [clipResidual, clipAt] using h.integrable_residual_sq (u := 0) (by norm_num)

theorem ExponentialMomentBound.memLp_two {X : Ω → ℝ} {K : ℝ}
    (h : ExponentialMomentBound μ X K) : MemLp X 2 μ :=
  (memLp_two_iff_integrable_sq h.measurable.aestronglyMeasurable).mpr h.integrable_sq

theorem ExponentialMomentBound.residual_memLp_two {X : Ω → ℝ} {K u : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) :
    MemLp (fun ω => clipResidual (K * u) (X ω)) 2 μ :=
  (memLp_two_iff_integrable_sq
    ((clipResidual_continuous _).measurable.comp h.measurable).aestronglyMeasurable).mpr
    (h.integrable_residual_sq hu)

end
end RectangleCLT.Companion
