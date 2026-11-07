import RectangleCLTCompanion.SplitV4.GaussianThresholdIdentity
import RectangleCLTCompanion.SplitV4.GaussianThresholdAPI

/-! The actual common-threshold derivative of the hard Gaussian radial
trace, obtained from continuous genuine coordinate derivatives. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem hasDerivAt_gaussianThresholdTrace_coordinate {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (l : Fin m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdTrace u (Function.update b l t))
      (-(gaussianThresholdFirst u (Function.update b l c) l) -
        ∑ j, (Function.update b l c) j * gaussianThresholdMixed u (Function.update b l c) j l) c := by
  cases r with
  | zero => have hh := hu l; norm_num [vectorNormSq] at hh
  | succ n =>
    simpa only [Function.update_idem, Function.update_self] using
      hasDerivAt_gaussianThresholdTrace_update u (Function.update b l c) l hu hi

theorem continuous_gaussianThresholdTrace_partial {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (l : Fin m) :
    Continuous (fun b : Vector m => -(gaussianThresholdFirst u b l) -
      ∑ j, b j * gaussianThresholdMixed u b j l) :=
  (continuous_gaussianThresholdFirst_of_unit_independent u l (hu l) hi).neg.sub
    (continuous_finset_sum _ (fun j _ => (continuous_apply j).mul
      (continuous_gaussianThresholdMixed_of_unit_independent u j l (hu j) hi)))

theorem hasFDerivAt_gaussianThresholdTrace {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (b : Vector m) :
    HasFDerivAt (gaussianThresholdTrace u)
      (∑ l, (-(gaussianThresholdFirst u b l) - ∑ j, b j * gaussianThresholdMixed u b j l) •
        (ContinuousLinearMap.proj l : Vector m →L[ℝ] ℝ)) b :=
  hasFDerivAt_of_continuous_coordinate_derivatives (gaussianThresholdTrace u)
    (fun b l => -(gaussianThresholdFirst u b l) - ∑ j, b j * gaussianThresholdMixed u b j l)
    (fun b l c => hasDerivAt_gaussianThresholdTrace_coordinate u b l hu hi c)
    (continuous_gaussianThresholdTrace_partial u hu hi) b

theorem continuous_gaussianThresholdTrace {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) : Continuous (gaussianThresholdTrace u) :=
  continuous_iff_continuousAt.mpr (fun b => (hasFDerivAt_gaussianThresholdTrace u hu hi b).continuousAt)

theorem gaussianThresholdDerivative_eq_sum_partials {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdDerivative u b =
      ∑ l, (-(gaussianThresholdFirst u b l) - ∑ j, b j * gaussianThresholdMixed u b j l) := by
  unfold gaussianThresholdDerivative
  exact Finset.sum_congr rfl (fun l _ => by
    simpa only [Function.update_eq_self] using
      (hasDerivAt_gaussianThresholdTrace_coordinate u b l hu hi (b l)).deriv)

theorem continuous_gaussianThresholdDerivative {m r : ℕ}
    (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) : Continuous (gaussianThresholdDerivative u) := by
  have he : gaussianThresholdDerivative u = fun b =>
      ∑ l, (-(gaussianThresholdFirst u b l) - ∑ j, b j * gaussianThresholdMixed u b j l) :=
    funext (fun b => gaussianThresholdDerivative_eq_sum_partials u b hu hi)
  rw [he]
  exact continuous_finset_sum _ (fun l _ => continuous_gaussianThresholdTrace_partial u hu hi l)

/-- The derivative in the simultaneous threshold direction is the actual
sum of coordinate derivatives used in the paper's B.5 identity. -/
theorem hasDerivAt_gaussianThresholdTrace_commonShift {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussianThresholdTrace u (fun j => b j + s))
      (gaussianThresholdDerivative u (fun j => b j + t)) t := by
  have hb : HasDerivAt (fun s : ℝ => fun j => b j + s) (fun _ => (1 : ℝ)) t := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa only [zero_add] using (hasDerivAt_const t (b j)).add (hasDerivAt_id t)
  have hh := (hasFDerivAt_gaussianThresholdTrace u hu hi (fun j => b j + t)).comp_hasDerivAt t hb
  convert hh using 1
  rw [gaussianThresholdDerivative_eq_sum_partials u _ hu hi]
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, mul_one]

/-- Exact fundamental theorem of calculus along a common threshold shift.
The integrand is the true derivative, not a quantitative bound premise. -/
theorem gaussianThresholdTrace_commonShift_sub_eq_integral {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hu : ∀ j, vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (a c : ℝ) :
    gaussianThresholdTrace u (fun j => b j + c) - gaussianThresholdTrace u (fun j => b j + a) =
      ∫ t in a..c, gaussianThresholdDerivative u (fun j => b j + t) := by
  have hc : Continuous (fun t : ℝ => gaussianThresholdDerivative u (fun j => b j + t)) :=
    (continuous_gaussianThresholdDerivative u hu hi).comp (by fun_prop)
  exact (intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_gaussianThresholdTrace_commonShift u b hu hi t) (hc.intervalIntegrable a c)).symm

/-- A dimension-dependent bound used only to justify signed Gaussian
Fubini and base integration. It is never the quantitative boundary estimate.
-/
theorem abs_gaussianThresholdTrace_le_twice_dimension {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) : |gaussianThresholdTrace u b| ≤ 2 * r := by
  have hi := (SignedSurface.standardGaussian_integrable_vectorNormSq r).add
    (integrable_const (r : ℝ))
  have hp (g : Vector r) : ‖({g | ∀ j, faceDot (u j) g ≤ b j}).indicator
      (fun g => vectorNormSq g - (r : ℝ)) g‖ ≤ vectorNormSq g + r := by
    by_cases hg : ∀ j, faceDot (u j) g ≤ b j
    · rw [Set.indicator_of_mem (show g ∈ {g | ∀ j, faceDot (u j) g ≤ b j} from hg), Real.norm_eq_abs]
      exact (abs_sub _ _).trans_eq (by
        rw [abs_of_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)), abs_of_nonneg (Nat.cast_nonneg r)])
    · rw [Set.indicator_of_not_mem (show g ∉ {g | ∀ j, faceDot (u j) g ≤ b j} from hg), norm_zero]
      exact add_nonneg (Finset.sum_nonneg (fun j _ => sq_nonneg _)) (Nat.cast_nonneg r)
  have hh := norm_integral_le_of_norm_le (f := fun g =>
    ({g | ∀ j, faceDot (u j) g ≤ b j}).indicator (fun g => vectorNormSq g - (r : ℝ)) g) hi (ae_of_all _ hp)
  change ‖∫ g, ({g | ∀ j, faceDot (u j) g ≤ b j}).indicator
      (fun g => vectorNormSq g - (r : ℝ)) g ∂standardGaussian r‖ ≤
    ∫ g, vectorNormSq g + (r : ℝ) ∂standardGaussian r at hh
  rw [integral_add (SignedSurface.standardGaussian_integrable_vectorNormSq r) (integrable_const _),
    SignedSurface.standardGaussian_integral_vectorNormSq] at hh
  simpa only [gaussianThresholdTrace, Real.norm_eq_abs, integral_const, measureReal_univ_eq_one,
    one_smul, two_mul] using hh

theorem integrable_gaussianThresholdTrace_parameter
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (u : Fin m → Vector r) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (b : Ω → Vector m) (hb : Measurable b) :
    Integrable (fun ω => gaussianThresholdTrace u (b ω)) μ :=
  (integrable_const ((2 : ℝ) * r)).mono'
    (((continuous_gaussianThresholdTrace u hu hi).measurable.comp hb).aestronglyMeasurable)
    (ae_of_all _ (fun ω => by
      simpa only [Real.norm_eq_abs] using abs_gaussianThresholdTrace_le_twice_dimension u (b ω)))

end

end RectangleCLT.Companion.SplitV4
