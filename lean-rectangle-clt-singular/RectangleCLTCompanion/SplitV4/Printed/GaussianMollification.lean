import RectangleCLTCompanion.SplitV4.IntrinsicGaussianBoundary
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Printed Gaussian Lemma 1: convolve the actual linear ramp with a
nonnegative smooth probability kernel, then pass to the limit in its
actual derivatives. The earlier interval-majorant proof is retained. -/

open MeasureTheory Set Filter ContinuousLinearMap
open scoped Topology Convolution ContDiff

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The printed linear ramp on `[-s,s]`, with constant extensions. -/
def gaussianLinearRamp (s x : ℝ) : ℝ :=
  (max (-s) (min s x) + s) / (2 * s)

theorem continuous_gaussianLinearRamp (s : ℝ) : Continuous (gaussianLinearRamp s) := by
  unfold gaussianLinearRamp
  fun_prop

theorem gaussianLinearRamp_range {s : ℝ} (hs : 0 < s) (x : ℝ) :
    0 ≤ gaussianLinearRamp s x ∧ gaussianLinearRamp s x ≤ 1 := by
  have hl : -s ≤ max (-s) (min s x) := le_max_left _ _
  have hr : max (-s) (min s x) ≤ s := max_le (by linarith) (min_le_left _ _)
  constructor
  · exact div_nonneg (by linarith) (by positivity)
  · exact (div_le_one (by positivity : 0 < 2 * s)).mpr (by linarith)

theorem gaussianLinearRamp_monotone {s : ℝ} (hs : 0 < s) :
    Monotone (gaussianLinearRamp s) := by
  intro x y hxy
  apply div_le_div_of_nonneg_right _ (by positivity : 0 ≤ 2 * s)
  exact add_le_add_right (max_le_max_left _ (min_le_min_left _ hxy)) _

theorem gaussianLinearRamp_abs_sub_le {s : ℝ} (hs : 0 < s) (x y : ℝ) :
    |gaussianLinearRamp s x - gaussianLinearRamp s y| ≤ (1 / (2 * s)) * |x - y| := by
  have hh := (((LipschitzWith.id.const_min s).const_max (-s)).dist_le_mul x y)
  simp only [NNReal.coe_one, one_mul, Real.dist_eq] at hh
  unfold gaussianLinearRamp
  rw [← sub_div, add_sub_add_right_eq_sub, abs_div, abs_of_pos (by positivity : 0 < 2 * s)]
  simpa only [one_div, div_eq_mul_inv, mul_comm, id_eq, one_mul] using
    div_le_div_of_nonneg_right hh (by positivity : 0 ≤ 2 * s)

theorem gaussianLinearRamp_eq_linear {s x : ℝ} (hs : 0 < s) (hx : x ∈ Icc (-s) s) :
    gaussianLinearRamp s x = (x + s) / (2 * s) := by
  simp only [gaussianLinearRamp, min_eq_right hx.2, max_eq_right hx.1]

theorem gaussianLinearRamp_eq_zero {s x : ℝ} (hs : 0 < s) (hx : x ≤ -s) :
    gaussianLinearRamp s x = 0 := by
  have hmin : min s x ≤ -s := (min_le_right _ _).trans hx
  simp only [gaussianLinearRamp, max_eq_left hmin, neg_add_cancel, zero_div]

theorem gaussianLinearRamp_eq_one {s x : ℝ} (hs : 0 < s) (hx : s ≤ x) :
    gaussianLinearRamp s x = 1 := by
  simp only [gaussianLinearRamp, min_eq_left hx, max_eq_right (by linarith : -s ≤ s)]
  field_simp
  ring

/-- The actual smooth mollification used in the printed proof. -/
def gaussianMollifiedRamp (s : ℝ) (φ : ContDiffBump (0 : ℝ)) : ℝ → ℝ :=
  φ.normed volume ⋆[lsmul ℝ ℝ, volume] gaussianLinearRamp s

private theorem gaussianMollifiedRamp_integrable (s : ℝ) (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    Integrable (fun y => φ.normed volume y * gaussianLinearRamp s (x - y)) volume := by
  exact φ.hasCompactSupport_normed.convolutionExists_left_of_continuous_right (lsmul ℝ ℝ)
    φ.integrable_normed.locallyIntegrable (continuous_gaussianLinearRamp s) x

/-- The kernel is genuinely smooth; the mollified ramp is genuinely C∞. -/
theorem contDiff_gaussianMollifiedRamp (s : ℝ) (φ : ContDiffBump (0 : ℝ)) :
    ContDiff ℝ ∞ (gaussianMollifiedRamp s φ) :=
  φ.hasCompactSupport_normed.contDiff_convolution_left (lsmul ℝ ℝ) φ.contDiff_normed
    (continuous_gaussianLinearRamp s).locallyIntegrable

theorem gaussianMollifiedRamp_range {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    0 ≤ gaussianMollifiedRamp s φ x ∧ gaussianMollifiedRamp s φ x ≤ 1 := by
  constructor
  · exact integral_nonneg (fun y => mul_nonneg (φ.nonneg_normed _) (gaussianLinearRamp_range hs _).1)
  · calc
      _ ≤ ∫ y, φ.normed volume y ∂volume :=
        integral_mono (gaussianMollifiedRamp_integrable s φ x) φ.integrable_normed
          (fun y => mul_le_of_le_one_right (φ.nonneg_normed _) (gaussianLinearRamp_range hs _).2)
      _ = 1 := φ.integral_normed

theorem gaussianMollifiedRamp_monotone {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) : Monotone (gaussianMollifiedRamp s φ) := by
  intro x y hxy
  exact integral_mono (gaussianMollifiedRamp_integrable s φ x) (gaussianMollifiedRamp_integrable s φ y)
    (fun z => mul_le_mul_of_nonneg_left (gaussianLinearRamp_monotone hs (sub_le_sub_right hxy z))
      (φ.nonneg_normed _))

theorem gaussianMollifiedRamp_abs_sub_le {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) (x y : ℝ) :
    |gaussianMollifiedRamp s φ x - gaussianMollifiedRamp s φ y| ≤
      (1 / (2 * s)) * |x - y| := by
  have hix := gaussianMollifiedRamp_integrable s φ x
  have hiy := gaussianMollifiedRamp_integrable s φ y
  have he : gaussianMollifiedRamp s φ x - gaussianMollifiedRamp s φ y =
      ∫ z, φ.normed volume z * (gaussianLinearRamp s (x - z) - gaussianLinearRamp s (y - z)) := by
    unfold gaussianMollifiedRamp
    simp only [convolution_def, lsmul_apply, smul_eq_mul]
    rw [← integral_sub hix hiy]
    apply integral_congr_ae
    exact ae_of_all _ (fun z => by ring)
  rw [he]
  have hh := norm_integral_le_of_norm_le
    (f := fun z => φ.normed volume z * (gaussianLinearRamp s (x - z) - gaussianLinearRamp s (y - z)))
    (φ.integrable_normed.mul_const ((1 / (2 * s)) * |x - y|))
    (ae_of_all _ (fun z => by
      rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (φ.nonneg_normed _)]
      rw [Real.norm_eq_abs]
      apply mul_le_mul_of_nonneg_left _ (φ.nonneg_normed _)
      simpa only [sub_sub_sub_cancel_right] using gaussianLinearRamp_abs_sub_le hs (x - z) (y - z)))
  rw [integral_mul_const, φ.integral_normed, one_mul] at hh
  exact hh

/-- The printed derivative bounds follow from monotonicity and the exact
linear-ramp Lipschitz constant. -/
theorem gaussianMollifiedRamp_deriv_bounds {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) (x : ℝ) :
    0 ≤ deriv (gaussianMollifiedRamp s φ) x ∧
      deriv (gaussianMollifiedRamp s φ) x ≤ 1 / (2 * s) := by
  constructor
  · have hd := ((contDiff_gaussianMollifiedRamp s φ).differentiable (by simp)).differentiableAt (x := x) |>.hasDerivAt
    apply ge_of_tendsto hd.tendsto_slope_zero_right
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htpos : 0 < t := ht
    simp only [smul_eq_mul]
    exact mul_nonneg (inv_nonneg.mpr ht.le)
      (sub_nonneg.mpr (gaussianMollifiedRamp_monotone hs φ (by linarith [htpos])))
  · have hh := norm_deriv_le_of_lip' (f := gaussianMollifiedRamp s φ) (x₀ := x) (by positivity : 0 ≤ 1 / (2 * s))
      (Eventually.of_forall (fun y => by
        simpa only [Real.norm_eq_abs] using gaussianMollifiedRamp_abs_sub_le hs φ y x))
    exact (le_abs_self _).trans hh

private theorem bump_first_moment_integrable (φ : ContDiffBump (0 : ℝ)) :
    Integrable (fun y => φ.normed volume y * y) volume :=
  (φ.continuous_normed.mul continuous_id).integrable_of_hasCompactSupport
    (φ.hasCompactSupport_normed.mul_right)

/-- The normalized bump is symmetric, so its actual first moment is zero. -/
theorem bump_first_moment_zero (φ : ContDiffBump (0 : ℝ)) :
    (∫ y, φ.normed volume y * y) = 0 := by
  have hh := integral_neg_eq_self (fun y => φ.normed volume y * y) volume
  have he : (fun y => φ.normed volume (-y) * (-y)) =
      (fun y => -(φ.normed volume y * y)) := by
    funext y
    rw [φ.normed_neg, mul_neg]
  rw [he, integral_neg] at hh
  linarith

private theorem bump_support_abs_lt (φ : ContDiffBump (0 : ℝ)) (y : ℝ)
    (hy : φ.normed volume y ≠ 0) : |y| < φ.rOut := by
  have hh : y ∈ Function.support (φ.normed volume) := hy
  rw [φ.support_normed_eq] at hh
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hh

/-- In the central affine region a symmetric mollification equals the
printed ramp exactly. -/
theorem gaussianMollifiedRamp_eq_linear {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : |x| + φ.rOut ≤ s) :
    gaussianMollifiedRamp s φ x = (x + s) / (2 * s) := by
  have hmoment := bump_first_moment_integrable φ
  have hsplit : Integrable (fun y => φ.normed volume y * ((x + s) / (2 * s)) -
      (φ.normed volume y * y) / (2 * s)) volume :=
    (φ.integrable_normed.mul_const _).sub (hmoment.div_const _)
  change (∫ y, φ.normed volume y * gaussianLinearRamp s (x - y)) = _
  calc
    _ = ∫ y, φ.normed volume y * ((x + s) / (2 * s)) -
        (φ.normed volume y * y) / (2 * s) := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        by_cases hy : φ.normed volume y = 0
        · simp only [hy, zero_mul, zero_div, sub_zero]
        · have habs := bump_support_abs_lt φ y hy
          have hxy : x - y ∈ Icc (-s) s := by
            constructor <;> linarith [le_abs_self x, neg_abs_le x, le_abs_self y, neg_abs_le y]
          rw [gaussianLinearRamp_eq_linear hs hxy]
          ring)
    _ = _ := by
      rw [integral_sub (φ.integrable_normed.mul_const _) (hmoment.div_const _),
        integral_mul_const, integral_div, φ.integral_normed, bump_first_moment_zero,
        zero_div, sub_zero, one_mul]

/-- On the left constant region the mollified ramp is zero. -/
theorem gaussianMollifiedRamp_eq_zero {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : x + φ.rOut ≤ -s) :
    gaussianMollifiedRamp s φ x = 0 := by
  change (∫ y, φ.normed volume y * gaussianLinearRamp s (x - y)) = 0
  apply integral_eq_zero_of_ae
  exact ae_of_all _ (fun y => by
    dsimp only [Pi.zero_apply]
    by_cases hy : φ.normed volume y = 0
    · simp [hy]
    · have habs := bump_support_abs_lt φ y hy
      rw [gaussianLinearRamp_eq_zero hs (by linarith [neg_abs_le y]), mul_zero])

/-- On the right constant region the mollified ramp is one. -/
theorem gaussianMollifiedRamp_eq_one {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : s ≤ x - φ.rOut) :
    gaussianMollifiedRamp s φ x = 1 := by
  change (∫ y, φ.normed volume y * gaussianLinearRamp s (x - y)) = 1
  calc
    _ = ∫ y, φ.normed volume y := by
      apply integral_congr_ae
      exact ae_of_all _ (fun y => by
        dsimp only
        by_cases hy : φ.normed volume y = 0
        · simp [hy]
        · have habs := bump_support_abs_lt φ y hy
          rw [gaussianLinearRamp_eq_one hs (by linarith [le_abs_self y]), mul_one])
    _ = 1 := φ.integral_normed

/-- If the kernel stays inside the affine region around `x`, the actual
mollified derivative is exactly the reciprocal width. -/
theorem gaussianMollifiedRamp_deriv_eq_center {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : |x| + φ.rOut < s) :
    deriv (gaussianMollifiedRamp s φ) x = 1 / (2 * s) := by
  have he : gaussianMollifiedRamp s φ =ᶠ[𝓝 x] (fun z => (z + s) / (2 * s)) := by
    have hn := ((continuous_abs.add continuous_const).tendsto x) (gt_mem_nhds hx)
    filter_upwards [hn] with z hz
    exact gaussianMollifiedRamp_eq_linear hs φ hz.le
  have hd := (((hasDerivAt_id x).add_const s).div_const (2 * s)).congr_of_eventuallyEq he
  exact hd.deriv

/-- If the kernel stays in the left constant region around `x`, the actual
mollified derivative vanishes. -/
theorem gaussianMollifiedRamp_deriv_eq_left {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : x + φ.rOut < -s) :
    deriv (gaussianMollifiedRamp s φ) x = 0 := by
  have he : gaussianMollifiedRamp s φ =ᶠ[𝓝 x] (fun _ => (0 : ℝ)) := by
    have hn := ((continuous_id.add continuous_const).tendsto x) (gt_mem_nhds hx)
    filter_upwards [hn] with z hz
    exact gaussianMollifiedRamp_eq_zero hs φ hz.le
  exact ((hasDerivAt_const x (0 : ℝ)).congr_of_eventuallyEq he).deriv

/-- If the kernel stays in the right constant region around `x`, the actual
mollified derivative vanishes. -/
theorem gaussianMollifiedRamp_deriv_eq_right {s : ℝ} (hs : 0 < s)
    (φ : ContDiffBump (0 : ℝ)) {x : ℝ} (hx : s < x - φ.rOut) :
    deriv (gaussianMollifiedRamp s φ) x = 0 := by
  have he : gaussianMollifiedRamp s φ =ᶠ[𝓝 x] (fun _ => (1 : ℝ)) := by
    have hn := ((continuous_id.sub continuous_const).tendsto x) (lt_mem_nhds hx)
    filter_upwards [hn] with z hz
    exact gaussianMollifiedRamp_eq_one hs φ hz.le
  exact ((hasDerivAt_const x (1 : ℝ)).congr_of_eventuallyEq he).deriv

/-- The actual derivative of a shrinking smooth-kernel mollification
converges to the reciprocal-width interval indicator away from endpoints. -/
theorem gaussianMollifiedRamp_deriv_tendsto {ι : Type*} {l : Filter ι}
    {s : ℝ} (hs : 0 < s) (φ : ι → ContDiffBump (0 : ℝ))
    (hφ : Tendsto (fun i => (φ i).rOut) l (𝓝 0))
    {x : ℝ} (hleft : x ≠ -s) (hright : x ≠ s) :
    Tendsto (fun i => deriv (gaussianMollifiedRamp s (φ i)) x) l
      (𝓝 ((Ioo (-s) s).indicator (fun _ => 1 / (2 * s)) x)) := by
  by_cases hx : x ∈ Ioo (-s) s
  · have habs : |x| < s := abs_lt.mpr ⟨by linarith [hx.1], hx.2⟩
    have hsmall := hφ.eventually_lt_const (by linarith : 0 < s - |x|)
    apply tendsto_const_nhds.congr'
    filter_upwards [hsmall] with i hi
    rw [Set.indicator_of_mem hx]
    exact (gaussianMollifiedRamp_deriv_eq_center hs (φ i) (by linarith)).symm
  · rw [Set.indicator_of_not_mem hx]
    by_cases hxl : x < -s
    · have hsmall := hφ.eventually_lt_const (by linarith : 0 < -s - x)
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with i hi
      exact (gaussianMollifiedRamp_deriv_eq_left hs (φ i) (by linarith)).symm
    · have hxr : s < x := by
        have hlow : -s < x := lt_of_le_of_ne (le_of_not_gt hxl) (Ne.symm hleft)
        have hge : s ≤ x := le_of_not_gt (fun hh => hx ⟨hlow, hh⟩)
        exact lt_of_le_of_ne hge (Ne.symm hright)
      have hsmall := hφ.eventually_lt_const (by linarith : 0 < x - s)
      apply tendsto_const_nhds.congr'
      filter_upwards [hsmall] with i hi
      exact (gaussianMollifiedRamp_deriv_eq_right hs (φ i) (by linarith)).symm

/-- A concrete sequence of nonnegative smooth probability kernels with
support contained in `[-1/(n+1),1/(n+1)]`. -/
def gaussianShrinkingBump (n : ℕ) : ContDiffBump (0 : ℝ) where
  rIn := (1 / ((n : ℝ) + 1)) / 2
  rOut := 1 / ((n : ℝ) + 1)
  rIn_pos := by positivity
  rIn_lt_rOut := by
    have hh : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith

theorem gaussianShrinkingBump_radius_tendsto :
    Tendsto (fun n => (gaussianShrinkingBump n).rOut) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

/-- The complete printed Gaussian route: first the already checked
smooth-maximum Stein limit, then actual smooth-kernel convolution of the
linear ramp, then derivative dominated convergence using atom-free levels.
This proof does not invoke the older final boundary estimate. -/
theorem intrinsicGaussianBoundary_printed_mollification {m r : ℕ} [NeZero m]
    (w : Fin m → Vector r) (a : Fin m → ℝ)
    (hw : ∀ α, vectorNormSq (w α) = 1) {s : ℝ} (hs : 0 < s) :
    (standardGaussian r).real {x | -s ≤ gaussianAffineMaximum w a x ∧
      gaussianAffineMaximum w a x ≤ s} ≤
      (2 * s) * ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
  let F := gaussianAffineMaximum w a
  let S := {x | -s ≤ F x ∧ F x ≤ s}
  let H := fun n : ℕ => fun x => deriv (gaussianMollifiedRamp s (gaussianShrinkingBump n)) (F x)
  have hF : Measurable F := (continuous_gaussianAffineMaximum w a).measurable
  have hS : MeasurableSet S := by
    exact measurableSet_Icc.preimage hF
  have hnz : ∀ α, w α ≠ 0 := by
    intro α hz
    have hh := hw α
    rw [hz] at hh
    norm_num [vectorNormSq] at hh
  have hleft : ∀ᵐ x ∂standardGaussian r, F x ≠ -s := by
    simpa only [ae_iff, not_not] using gaussianAffineMaximum_level_zero w a hnz (-s)
  have hright : ∀ᵐ x ∂standardGaussian r, F x ≠ s := by
    simpa only [ae_iff, not_not] using gaussianAffineMaximum_level_zero w a hnz s
  have hlim : ∀ᵐ x ∂standardGaussian r, Tendsto (fun n => H n x) atTop
      (𝓝 (S.indicator (fun _ => 1 / (2 * s)) x)) := by
    filter_upwards [hleft, hright] with x hxl hxr
    have hh := gaussianMollifiedRamp_deriv_tendsto hs gaussianShrinkingBump
      gaussianShrinkingBump_radius_tendsto hxl hxr
    have he : (Ioo (-s) s).indicator (fun _ => 1 / (2 * s)) (F x) =
        S.indicator (fun _ => 1 / (2 * s)) x := by
      by_cases hx : F x ∈ Ioo (-s) s
      · have hxS : x ∈ S := ⟨hx.1.le, hx.2.le⟩
        simp only [Set.indicator_of_mem hx, Set.indicator_of_mem hxS]
      · have hxS : x ∉ S := by
          intro hxs
          exact hx ⟨lt_of_le_of_ne hxs.1 (Ne.symm hxl), lt_of_le_of_ne hxs.2 hxr⟩
        simp only [Set.indicator_of_not_mem hx, Set.indicator_of_not_mem hxS]
    simpa only [he] using hh
  have hDCT := tendsto_integral_filter_of_dominated_convergence
    (μ := standardGaussian r) (F := H) (f := S.indicator (fun _ => 1 / (2 * s)))
    (fun _ => 1 / (2 * s))
    (Eventually.of_forall (fun n =>
      (((contDiff_gaussianMollifiedRamp s (gaussianShrinkingBump n)).continuous_deriv (by simp)).measurable.comp hF).aestronglyMeasurable))
    (Eventually.of_forall (fun n => ae_of_all _ (fun x => by
      have hb := gaussianMollifiedRamp_deriv_bounds hs (gaussianShrinkingBump n) (F x)
      simpa only [H, Real.norm_eq_abs, abs_of_nonneg hb.1] using hb.2)))
    (integrable_const _) hlim
  have htest (n : ℕ) : (∫ x, H n x ∂standardGaussian r) ≤
      ∫ x, positiveGaussianFaceMaximum w x ∂standardGaussian r := by
    apply gaussianAffineMaximum_test_bound w a hw
      (gaussianMollifiedRamp s (gaussianShrinkingBump n))
      (deriv (gaussianMollifiedRamp s (gaussianShrinkingBump n)))
      (fun x => ((contDiff_gaussianMollifiedRamp s (gaussianShrinkingBump n)).differentiable (by simp)).differentiableAt.hasDerivAt)
      ((contDiff_gaussianMollifiedRamp s (gaussianShrinkingBump n)).continuous_deriv (by simp))
      (gaussianMollifiedRamp_range hs (gaussianShrinkingBump n)) (1 / (2 * s))
    intro x
    have hb := gaussianMollifiedRamp_deriv_bounds hs (gaussianShrinkingBump n) x
    rw [abs_of_nonneg hb.1]
    exact hb.2
  have hh := le_of_tendsto hDCT (Eventually.of_forall htest)
  rw [integral_indicator_const _ hS, smul_eq_mul] at hh
  have hpos : 0 < 2 * s := by positivity
  have hmul := mul_le_mul_of_nonneg_right hh hpos.le
  rw [mul_assoc, one_div, inv_mul_cancel₀ hpos.ne', mul_one] at hmul
  simpa only [S, F, mul_comm] using hmul

end
end RectangleCLT.Companion.SplitV4.Printed
