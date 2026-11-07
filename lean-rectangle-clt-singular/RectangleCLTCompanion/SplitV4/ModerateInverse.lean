import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-! Scalar inverse and cubic-cancellation estimates for moderate tilting.
These are quantitative consequences of actual local Taylor remainders;
the cumulant modules separately discharge those hypotheses. No tail
probability estimate or proposed moderate-deviation conclusion is assumed. -/

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def moderateInverseDisplacementConstant (B : ℝ) : ℝ := 2 + 8 * B
def moderateInverseExpansionConstant (B : ℝ) : ℝ := 3 + 20 * B
def moderateLegendreConstant (B : ℝ) : ℝ :=
  (moderateInverseDisplacementConstant B) ^ 2 +
    2 * moderateInverseDisplacementConstant B + 16 * B
def moderateCancellationConstant (B : ℝ) : ℝ := 12 * B + 4 * (1 + 2 * B) ^ 2

theorem moderate_root_displacement {B δ γ x t : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (_hx : 0 ≤ x) (ht : 0 ≤ t) (htx : t ≤ 2 * x)
    (hsmall : δ * x ≤ 1) (hγ : |γ| ≤ δ)
    (hm : |x - t - γ * t ^ 2 / 2| ≤ B * δ ^ 2 * t ^ 3) :
    |t - x| ≤ moderateInverseDisplacementConstant B * δ * x ^ 2 := by
  have ht2 : t ^ 2 ≤ 4 * x ^ 2 := by
    have hh := pow_le_pow_left₀ ht htx 2
    norm_num [mul_pow] at hh
    exact hh
  have ht3 : t ^ 3 ≤ 8 * x ^ 3 := by
    have hh := pow_le_pow_left₀ ht htx 3
    norm_num [mul_pow] at hh
    exact hh
  have he : |t - x| ≤ |γ| * t ^ 2 / 2 + |x - t - γ * t ^ 2 / 2| := by
    calc
      _ = |-(γ * t ^ 2 / 2) - (x - t - γ * t ^ 2 / 2)| := by congr 1; ring
      _ ≤ |-(γ * t ^ 2 / 2)| + |x - t - γ * t ^ 2 / 2| := abs_sub _ _
      _ = _ := by rw [abs_neg, abs_div, abs_mul, abs_of_nonneg (sq_nonneg t)]; norm_num
  have hg : |γ| * t ^ 2 / 2 ≤ 2 * δ * x ^ 2 := by
    have hh := mul_le_mul hγ ht2 (sq_nonneg t) hδ
    nlinarith
  have hr : B * δ ^ 2 * t ^ 3 ≤ 8 * B * δ * x ^ 2 := by
    calc
      _ ≤ B * δ ^ 2 * (8 * x ^ 3) := mul_le_mul_of_nonneg_left ht3 (by positivity)
      _ = (8 * B * δ * x ^ 2) * (δ * x) := by ring
      _ ≤ (8 * B * δ * x ^ 2) * 1 := mul_le_mul_of_nonneg_left hsmall (by positivity)
      _ = _ := by ring
  unfold moderateInverseDisplacementConstant
  linarith

theorem moderate_inverse_expansion {B δ γ x t : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (ht : 0 ≤ t) (htx : t ≤ 2 * x)
    (hsmall : δ * x ≤ 1) (hγ : |γ| ≤ δ)
    (hm : |x - t - γ * t ^ 2 / 2| ≤ B * δ ^ 2 * t ^ 3) :
    |t - x + γ * x ^ 2 / 2| ≤ moderateInverseExpansionConstant B * δ ^ 2 * x ^ 3 := by
  have hdisp := moderate_root_displacement hB hδ hx ht htx hsmall hγ hm
  have hc : 0 ≤ moderateInverseDisplacementConstant B := by unfold moderateInverseDisplacementConstant; positivity
  have ht3 : t ^ 3 ≤ 8 * x ^ 3 := by
    have hh := pow_le_pow_left₀ ht htx 3
    norm_num [mul_pow] at hh
    exact hh
  have hdiff : |t ^ 2 - x ^ 2| ≤ (moderateInverseDisplacementConstant B * δ * x ^ 2) * (3 * x) := by
    have he : t ^ 2 - x ^ 2 = (t - x) * (t + x) := by ring
    rw [he, abs_mul, abs_of_nonneg (add_nonneg ht hx)]
    exact mul_le_mul hdisp (by linarith : t + x ≤ 3 * x) (add_nonneg ht hx) (by positivity)
  have he : |t - x + γ * x ^ 2 / 2| ≤
      |x - t - γ * t ^ 2 / 2| + |γ| * |t ^ 2 - x ^ 2| / 2 := by
    calc
      _ = |-(x - t - γ * t ^ 2 / 2) - γ * (t ^ 2 - x ^ 2) / 2| := by congr 1; ring
      _ ≤ |-(x - t - γ * t ^ 2 / 2)| + |γ * (t ^ 2 - x ^ 2) / 2| := abs_sub _ _
      _ = _ := by rw [abs_neg, abs_div, abs_mul]; norm_num
  have hr := mul_le_mul_of_nonneg_left ht3 (by positivity : 0 ≤ B * δ ^ 2)
  have hg := mul_le_mul hγ hdiff (abs_nonneg _) hδ
  unfold moderateInverseExpansionConstant moderateInverseDisplacementConstant at *
  nlinarith

theorem moderate_legendre_expansion {B δ γ x t K : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (ht : 0 ≤ t) (htx : t ≤ 2 * x)
    (hsmall : δ * x ≤ 1) (hγ : |γ| ≤ δ)
    (hm : |x - t - γ * t ^ 2 / 2| ≤ B * δ ^ 2 * t ^ 3)
    (hK : |K - t ^ 2 / 2 - γ * t ^ 3 / 6| ≤ B * δ ^ 2 * t ^ 4) :
    |K - t * x + x ^ 2 / 2 - γ * x ^ 3 / 6| ≤ moderateLegendreConstant B * δ ^ 2 * x ^ 4 := by
  have hd := moderate_root_displacement hB hδ hx ht htx hsmall hγ hm
  have hC : 0 ≤ moderateInverseDisplacementConstant B := by unfold moderateInverseDisplacementConstant; positivity
  have ht2 : t ^ 2 ≤ 4 * x ^ 2 := by
    have hh := pow_le_pow_left₀ ht htx 2
    norm_num [mul_pow] at hh
    exact hh
  have ht4 : t ^ 4 ≤ 16 * x ^ 4 := by
    have hh := pow_le_pow_left₀ ht htx 4
    norm_num [mul_pow] at hh
    exact hh
  have htx2 : t * x ≤ 2 * x ^ 2 := by nlinarith
  have hs : (t - x) ^ 2 ≤ (moderateInverseDisplacementConstant B) ^ 2 * δ ^ 2 * x ^ 4 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hd 2
    simpa [sq_abs, mul_pow, ← pow_mul] using hh
  have hdiff : |t ^ 3 - x ^ 3| ≤
      (moderateInverseDisplacementConstant B * δ * x ^ 2) * (7 * x ^ 2) := by
    have he : t ^ 3 - x ^ 3 = (t - x) * (t ^ 2 + t * x + x ^ 2) := by ring
    have hp : 0 ≤ t ^ 2 + t * x + x ^ 2 := by positivity
    rw [he, abs_mul, abs_of_nonneg hp]
    exact mul_le_mul hd (by nlinarith) hp (by positivity)
  have he : |K - t * x + x ^ 2 / 2 - γ * x ^ 3 / 6| ≤
      |K - t ^ 2 / 2 - γ * t ^ 3 / 6| + (t - x) ^ 2 / 2 + |γ| * |t ^ 3 - x ^ 3| / 6 := by
    calc
      _ = |(K - t ^ 2 / 2 - γ * t ^ 3 / 6) + (t - x) ^ 2 / 2 + γ * (t ^ 3 - x ^ 3) / 6| := by congr 1; ring
      _ ≤ |(K - t ^ 2 / 2 - γ * t ^ 3 / 6) + (t - x) ^ 2 / 2| + |γ * (t ^ 3 - x ^ 3) / 6| := abs_add _ _
      _ ≤ (|K - t ^ 2 / 2 - γ * t ^ 3 / 6| + |(t - x) ^ 2 / 2|) + |γ * (t ^ 3 - x ^ 3) / 6| :=
        add_le_add_right (abs_add _ _) _
      _ = _ := by rw [abs_of_nonneg (by positivity : 0 ≤ (t - x) ^ 2 / 2), abs_div, abs_mul]; norm_num
  have hr := mul_le_mul_of_nonneg_left ht4 (by positivity : 0 ≤ B * δ ^ 2)
  have hg := mul_le_mul hγ hdiff (abs_nonneg _) hδ
  have hp : 0 ≤ δ ^ 2 * x ^ 4 := by positivity
  have hpad : 0 ≤ ((moderateInverseDisplacementConstant B) ^ 2 / 2 +
      5 * moderateInverseDisplacementConstant B / 6) * (δ ^ 2 * x ^ 4) := by positivity
  unfold moderateLegendreConstant
  nlinarith

/-- The square root retains its linear term with a quadratic remainder.
This is proved from the exact identity `(sqrt V-1)^2=V-1-2(sqrt V-1)`. -/
theorem moderate_sqrt_variance_expansion {B δ γ t V : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (ht : 0 ≤ t) (hdt : δ * t ≤ 2)
    (hγ : |γ| ≤ δ) (hV : 0 ≤ V)
    (hvar : |V - 1 - γ * t| ≤ B * δ ^ 2 * t ^ 2) :
    |Real.sqrt V - 1 - γ * t / 2| ≤
      ((B + (1 + 2 * B) ^ 2) / 2) * δ ^ 2 * t ^ 2 := by
  have hs : 0 ≤ Real.sqrt V := Real.sqrt_nonneg _
  have hs2 : (Real.sqrt V) ^ 2 = V := Real.sq_sqrt hV
  have hdt0 : 0 ≤ δ * t := mul_nonneg hδ ht
  have hrem : B * δ ^ 2 * t ^ 2 ≤ 2 * B * δ * t := by
    have hh := mul_le_mul_of_nonneg_left hdt (by positivity : 0 ≤ B * δ * t)
    nlinarith
  have hdev : |V - 1| ≤ (1 + 2 * B) * δ * t := by
    have htri : |V - 1| ≤ |V - 1 - γ * t| + |γ| * t := by
      calc
        _ = |(V - 1 - γ * t) + γ * t| := by congr 1; ring
        _ ≤ |V - 1 - γ * t| + |γ * t| := abs_add _ _
        _ = _ := by rw [abs_mul, abs_of_nonneg ht]
    have hg := mul_le_mul_of_nonneg_right hγ ht
    nlinarith
  have hsdev : |Real.sqrt V - 1| ≤ (1 + 2 * B) * δ * t := by
    have he : V - 1 = (Real.sqrt V - 1) * (Real.sqrt V + 1) := by nlinarith
    have hle : |Real.sqrt V - 1| ≤ |V - 1| := by
      rw [he, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt V + 1)]
      nlinarith [abs_nonneg (Real.sqrt V - 1)]
    exact hle.trans hdev
  have hsq : (Real.sqrt V - 1) ^ 2 ≤ (1 + 2 * B) ^ 2 * δ ^ 2 * t ^ 2 := by
    have hh := pow_le_pow_left₀ (abs_nonneg _) hsdev 2
    simpa only [sq_abs, mul_pow] using hh
  have he : |Real.sqrt V - 1 - γ * t / 2| ≤
      |V - 1 - γ * t| / 2 + (Real.sqrt V - 1) ^ 2 / 2 := by
    calc
      _ = |(V - 1 - γ * t) / 2 - (Real.sqrt V - 1) ^ 2 / 2| := by congr 1; nlinarith
      _ ≤ |(V - 1 - γ * t) / 2| + |(Real.sqrt V - 1) ^ 2 / 2| := abs_sub _ _
      _ = _ := by rw [abs_div, abs_of_nonneg (by positivity : 0 ≤ (Real.sqrt V - 1) ^ 2 / 2)]; norm_num
  nlinarith

/-- The linear skew term cancels in the actual tilted Gaussian threshold
`t sqrt V`: the resulting error is quadratic in the observation envelope. -/
theorem moderate_tilted_threshold_cancellation {B δ γ x t V : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (_hx : 0 ≤ x) (ht : 0 ≤ t) (htx : t ≤ 2 * x)
    (hsmall : δ * x ≤ 1) (hγ : |γ| ≤ δ) (hV : 0 ≤ V)
    (hm : |x - t - γ * t ^ 2 / 2| ≤ B * δ ^ 2 * t ^ 3)
    (hvar : |V - 1 - γ * t| ≤ B * δ ^ 2 * t ^ 2) :
    |t * Real.sqrt V - x| ≤ moderateCancellationConstant B * δ ^ 2 * x ^ 3 := by
  have hdt : δ * t ≤ 2 := by nlinarith
  have hs := moderate_sqrt_variance_expansion hB hδ ht hdt hγ hV hvar
  have hst := mul_le_mul_of_nonneg_left hs ht
  have ht3 : t ^ 3 ≤ 8 * x ^ 3 := by
    have hh := pow_le_pow_left₀ ht htx 3
    norm_num [mul_pow] at hh
    exact hh
  have he : |t * Real.sqrt V - x| ≤
      |x - t - γ * t ^ 2 / 2| + t * |Real.sqrt V - 1 - γ * t / 2| := by
    calc
      _ = |-(x - t - γ * t ^ 2 / 2) + t * (Real.sqrt V - 1 - γ * t / 2)| := by congr 1; ring
      _ ≤ |-(x - t - γ * t ^ 2 / 2)| + |t * (Real.sqrt V - 1 - γ * t / 2)| := abs_add _ _
      _ = _ := by rw [abs_neg, abs_mul, abs_of_nonneg ht]
  have hpre : |t * Real.sqrt V - x| ≤
      ((3 * B + (1 + 2 * B) ^ 2) / 2) * δ ^ 2 * t ^ 3 := by nlinarith
  have hp := mul_le_mul_of_nonneg_left ht3
    (by positivity : 0 ≤ ((3 * B + (1 + 2 * B) ^ 2) / 2) * δ ^ 2)
  unfold moderateCancellationConstant
  nlinarith

/-- The actual smallness regime used by the cumulant caller makes the
inverse root close enough for the tilted Gaussian threshold to be
uniformly comparable with the original nonnegative threshold. -/
theorem moderate_tilted_threshold_scale {B δ γ x t V : ℝ}
    (hB : 1 ≤ B) (hδ : 0 ≤ δ) (hx : 0 ≤ x) (ht : 0 ≤ t) (htx : t ≤ 2 * x)
    (hsmall : 100 * B * (δ * x) ≤ 1) (hγ : |γ| ≤ δ)
    (hV : (1 / 2 : ℝ) ≤ V) (hVupper : V ≤ 2)
    (hm : |x - t - γ * t ^ 2 / 2| ≤ B * δ ^ 2 * t ^ 3) :
    x / 2 ≤ t * Real.sqrt V ∧ t * Real.sqrt V ≤ 3 * x := by
  have hd0 : 0 ≤ δ * x := mul_nonneg hδ hx
  have hBd := mul_le_mul_of_nonneg_right hB hd0
  have hweak : δ * x ≤ 1 := by nlinarith
  have hd := moderate_root_displacement (zero_le_one.trans hB) hδ hx ht htx hweak hγ hm
  have hcoef : moderateInverseDisplacementConstant B * (δ * x) ≤ 1 / 4 := by
    unfold moderateInverseDisplacementConstant
    nlinarith
  have hdisp : |t - x| ≤ x / 4 := by
    have hh := mul_le_mul_of_nonneg_right hcoef hx
    nlinarith
  have htlower : 3 * x / 4 ≤ t := by linarith [(abs_le.mp hdisp).1]
  have htupper : t ≤ 5 * x / 4 := by linarith [(abs_le.mp hdisp).2]
  have hV0 : 0 ≤ V := (by norm_num : (0 : ℝ) ≤ 1 / 2).trans hV
  have hslo : (2 / 3 : ℝ) ≤ Real.sqrt V :=
    Real.le_sqrt_of_sq_le (by nlinarith)
  have hshi : Real.sqrt V ≤ (3 / 2 : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith⟩
  constructor
  · have hh := mul_le_mul htlower hslo (by norm_num : (0 : ℝ) ≤ 2 / 3) ht
    nlinarith
  · have hh := mul_le_mul htupper hshi (Real.sqrt_nonneg _) (by positivity : 0 ≤ 5 * x / 4)
    nlinarith

end
end RectangleCLT.Companion.SplitV4
