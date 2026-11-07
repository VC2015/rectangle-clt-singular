import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Analysis.SpecialFunctions.Trigonometric.InverseDeriv

/-!
The three integrable time weights in the proof of Lemma G.1.  Inverse square
roots are expressed using `Real.sqrt`; the values at the two endpoints are
Lean's totalized division values.  Their integrability and the continuous
one-sided primitive limits justify the improper endpoint passages.

These scalar calculus results do not prove the paired Slepian comparison.
-/

open MeasureTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def gaussianTimeWeight (s : ℝ) : ℝ := 1 / Real.sqrt (1 - s)
def pairedTimeWeight (s : ℝ) : ℝ := 1 / Real.sqrt (s * (1 - s))
def fourthTimeWeight (s : ℝ) : ℝ := s / Real.sqrt (1 - s)

/-- Identification with the manuscript's real-power notation, including zero. -/
theorem inv_sqrt_eq_rpow_neg_half {x : ℝ} (hx : 0 ≤ x) :
    1 / Real.sqrt x = x ^ (-(1 / 2 : ℝ)) := by
  rw [Real.rpow_neg hx, ← Real.sqrt_eq_rpow, one_div]

theorem gaussianTimeWeight_eq_rpow {s : ℝ} (hs : s ≤ 1) :
    gaussianTimeWeight s = (1 - s) ^ (-(1 / 2 : ℝ)) := by
  exact inv_sqrt_eq_rpow_neg_half (by linarith)

theorem pairedTimeWeight_eq_rpow {s : ℝ} (hs : s ∈ Icc (0 : ℝ) 1) :
    pairedTimeWeight s = (s * (1 - s)) ^ (-(1 / 2 : ℝ)) := by
  exact inv_sqrt_eq_rpow_neg_half (mul_nonneg hs.1 (by linarith [hs.2]))

theorem fourthTimeWeight_eq_rpow {s : ℝ} (hs : s ≤ 1) :
    fourthTimeWeight s = s * (1 - s) ^ (-(1 / 2 : ℝ)) := by
  rw [← gaussianTimeWeight_eq_rpow hs]
  simp [fourthTimeWeight, gaussianTimeWeight, div_eq_mul_inv]

def gaussianTimePrimitive (s : ℝ) : ℝ := -2 * Real.sqrt (1 - s)
def pairedTimePrimitive (s : ℝ) : ℝ := Real.arcsin (2 * s - 1)
def fourthTimePrimitive (s : ℝ) : ℝ := -(2 / 3 : ℝ) * (s + 2) * Real.sqrt (1 - s)

theorem continuous_gaussianTimePrimitive : Continuous gaussianTimePrimitive := by
  unfold gaussianTimePrimitive
  fun_prop

theorem continuous_pairedTimePrimitive : Continuous pairedTimePrimitive := by
  unfold pairedTimePrimitive
  fun_prop

theorem continuous_fourthTimePrimitive : Continuous fourthTimePrimitive := by
  unfold fourthTimePrimitive
  fun_prop

theorem hasDerivAt_gaussianTimePrimitive {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt gaussianTimePrimitive (gaussianTimeWeight s) s := by
  have hpos : 0 < 1 - s := by linarith [hs.2]
  have hroot : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hd := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).sqrt hpos.ne'
  convert hd.const_mul (-2) using 1 <;>
    dsimp [gaussianTimePrimitive, gaussianTimeWeight]
  field_simp [hroot]

theorem hasDerivAt_pairedTimePrimitive {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt pairedTimePrimitive (pairedTimeWeight s) s := by
  have hleft : 2 * s - 1 ≠ -1 := by linarith [hs.1]
  have hright : 2 * s - 1 ≠ 1 := by linarith [hs.2]
  have hpos : 0 < s * (1 - s) := mul_pos hs.1 (by linarith [hs.2])
  have hroot : Real.sqrt (s * (1 - s)) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hd := (Real.hasDerivAt_arcsin hleft hright).comp s
    (((hasDerivAt_id s).const_mul 2).sub_const 1)
  convert hd using 1 <;> dsimp [pairedTimePrimitive, pairedTimeWeight]
  rw [show 1 - (2 * s - 1) ^ 2 = 4 * (s * (1 - s)) by ring,
    Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num
  field_simp [hroot]

theorem hasDerivAt_fourthTimePrimitive {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) :
    HasDerivAt fourthTimePrimitive (fourthTimeWeight s) s := by
  have hpos : 0 < 1 - s := by linarith [hs.2]
  have hroot : Real.sqrt (1 - s) ≠ 0 := (Real.sqrt_pos.mpr hpos).ne'
  have hd := ((hasDerivAt_id s).add_const 2).const_mul (-(2 / 3 : ℝ))
  have hr := ((hasDerivAt_const s (1 : ℝ)).sub (hasDerivAt_id s)).sqrt hpos.ne'
  convert hd.mul hr using 1 <;> dsimp [fourthTimePrimitive, fourthTimeWeight]
  field_simp [hroot]
  nlinarith [Real.sq_sqrt hpos.le]

theorem intervalIntegrable_gaussianTimeWeight :
    IntervalIntegrable gaussianTimeWeight volume (0 : ℝ) 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    continuous_gaussianTimePrimitive.continuousOn
  · intro s hs
    exact hasDerivAt_gaussianTimePrimitive (by simpa using hs)
  · intro s _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem intervalIntegrable_pairedTimeWeight :
    IntervalIntegrable pairedTimeWeight volume (0 : ℝ) 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    continuous_pairedTimePrimitive.continuousOn
  · intro s hs
    exact hasDerivAt_pairedTimePrimitive (by simpa using hs)
  · intro s _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)

theorem intervalIntegrable_fourthTimeWeight :
    IntervalIntegrable fourthTimeWeight volume (0 : ℝ) 1 := by
  apply intervalIntegral.intervalIntegrable_deriv_of_nonneg
    continuous_fourthTimePrimitive.continuousOn
  · intro s hs
    exact hasDerivAt_fourthTimePrimitive (by simpa using hs)
  · intro s hs
    exact div_nonneg (by simpa using hs.1.le) (Real.sqrt_nonneg _)

/-- Endpoint values of the primitives, available as genuine one-sided limits. -/
theorem gaussianTimePrimitive_endpoint_limits :
    Tendsto gaussianTimePrimitive (𝓝[>] (0 : ℝ)) (𝓝 (-2)) ∧
    Tendsto gaussianTimePrimitive (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  constructor
  · simpa [gaussianTimePrimitive] using
      continuous_gaussianTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Ioi (0 : ℝ)) (x := (0 : ℝ))
  · simpa [gaussianTimePrimitive] using
      continuous_gaussianTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Iio (1 : ℝ)) (x := (1 : ℝ))

theorem pairedTimePrimitive_endpoint_limits :
    Tendsto pairedTimePrimitive (𝓝[>] (0 : ℝ)) (𝓝 (-(Real.pi / 2))) ∧
    Tendsto pairedTimePrimitive (𝓝[<] (1 : ℝ)) (𝓝 (Real.pi / 2)) := by
  constructor
  · simpa [pairedTimePrimitive] using
      continuous_pairedTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Ioi (0 : ℝ)) (x := (0 : ℝ))
  · simpa [pairedTimePrimitive] using
      continuous_pairedTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Iio (1 : ℝ)) (x := (1 : ℝ))

theorem fourthTimePrimitive_endpoint_limits :
    Tendsto fourthTimePrimitive (𝓝[>] (0 : ℝ)) (𝓝 (-(4 / 3 : ℝ))) ∧
    Tendsto fourthTimePrimitive (𝓝[<] (1 : ℝ)) (𝓝 0) := by
  constructor
  · convert
      continuous_fourthTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Ioi (0 : ℝ)) (x := (0 : ℝ)) using 1 <;>
      norm_num [fourthTimePrimitive]
  · simpa [fourthTimePrimitive] using
      continuous_fourthTimePrimitive.continuousAt.continuousWithinAt.tendsto
        (s := Iio (1 : ℝ)) (x := (1 : ℝ))

theorem integral_gaussianTimeWeight :
    (∫ s in (0 : ℝ)..1, gaussianTimeWeight s) = 2 := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1) (fun s hs => hasDerivAt_gaussianTimePrimitive hs)
    intervalIntegrable_gaussianTimeWeight
    gaussianTimePrimitive_endpoint_limits.1 gaussianTimePrimitive_endpoint_limits.2
  norm_num at h ⊢
  exact h

theorem integral_pairedTimeWeight :
    (∫ s in (0 : ℝ)..1, pairedTimeWeight s) = Real.pi := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1) (fun s hs => hasDerivAt_pairedTimePrimitive hs)
    intervalIntegrable_pairedTimeWeight
    pairedTimePrimitive_endpoint_limits.1 pairedTimePrimitive_endpoint_limits.2
  linarith

theorem integral_fourthTimeWeight :
    (∫ s in (0 : ℝ)..1, fourthTimeWeight s) = (4 / 3 : ℝ) := by
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto
    (by norm_num : (0 : ℝ) < 1) (fun s hs => hasDerivAt_fourthTimePrimitive hs)
    intervalIntegrable_fourthTimeWeight
    fourthTimePrimitive_endpoint_limits.1 fourthTimePrimitive_endpoint_limits.2
  norm_num at h ⊢
  exact h

/-- Integrability gives the simultaneous two-endpoint truncation limit.  The
source filter keeps both moving endpoints in the closed unit interval. -/
theorem truncated_time_integral_tendsto {w : ℝ → ℝ}
    (hw : IntervalIntegrable w volume (0 : ℝ) 1) :
    Tendsto (fun ε => ∫ s in ε..(1 - ε), w s)
      (𝓝[Icc (0 : ℝ) 1] (0 : ℝ)) (𝓝 (∫ s in (0 : ℝ)..1, w s)) := by
  have hc : ContinuousOn (fun b => ∫ s in (0 : ℝ)..b, w s) (Icc (0 : ℝ) 1) := by
    simpa using intervalIntegral.continuousOn_primitive_interval' hw
      (by simp : (0 : ℝ) ∈ uIcc (0 : ℝ) 1)
  have hmap : MapsTo (fun ε : ℝ => 1 - ε) (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1) := by
    intro ε hε
    exact ⟨by linarith [hε.2], by linarith [hε.1]⟩
  have hd : ContinuousOn (fun ε => ∫ s in (0 : ℝ)..(1 - ε), w s)
      (Icc (0 : ℝ) 1) :=
    hc.comp (continuous_const.sub continuous_id).continuousOn hmap
  have hlim := ((hd 0 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1)).sub
    (hc 0 (by simp : (0 : ℝ) ∈ Icc (0 : ℝ) 1))).tendsto
  simp only [sub_zero, intervalIntegral.integral_same] at hlim
  apply hlim.congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε' : ε ∈ uIcc (0 : ℝ) 1 := by simpa using hε
  have hε'' : 1 - ε ∈ uIcc (0 : ℝ) 1 := by simpa using hmap hε
  exact intervalIntegral.integral_interval_sub_left
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hε''))
    (hw.mono_set (uIcc_subset_uIcc left_mem_uIcc hε'))

theorem truncated_gaussianTimeWeight_tendsto :
    Tendsto (fun ε => ∫ s in ε..(1 - ε), gaussianTimeWeight s)
      (𝓝[Icc (0 : ℝ) 1] (0 : ℝ)) (𝓝 2) := by
  simpa only [integral_gaussianTimeWeight] using
    truncated_time_integral_tendsto intervalIntegrable_gaussianTimeWeight

theorem truncated_pairedTimeWeight_tendsto :
    Tendsto (fun ε => ∫ s in ε..(1 - ε), pairedTimeWeight s)
      (𝓝[Icc (0 : ℝ) 1] (0 : ℝ)) (𝓝 Real.pi) := by
  simpa only [integral_pairedTimeWeight] using
    truncated_time_integral_tendsto intervalIntegrable_pairedTimeWeight

theorem truncated_fourthTimeWeight_tendsto :
    Tendsto (fun ε => ∫ s in ε..(1 - ε), fourthTimeWeight s)
      (𝓝[Icc (0 : ℝ) 1] (0 : ℝ)) (𝓝 (4 / 3 : ℝ)) := by
  simpa only [integral_fourthTimeWeight] using
    truncated_time_integral_tendsto intervalIntegrable_fourthTimeWeight

end
end RectangleCLT.Companion.SplitV4
