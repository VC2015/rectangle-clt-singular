import RectangleCLTCompanion.SplitV4.Printed.MatrixNonnegativeContraction
import RectangleCLTCompanion.SplitV4.GenericC4Taylor
import Mathlib.Probability.Variance

/-! The actual C2 potential/Hessian chain in the covariance-contraction
remark, frozen lines 2871--2882. The external Brascamp--Lieb *linear*
special case is proved below by the checked Prekopa route. That proof is
an explicit alternative proof of the cited external input, not a proof
of the general Brascamp--Lieb function variance inequality. The printed
potential calculation and linear application are checked; no independent
Brascamp--Lieb proof of the external input is claimed. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem hasDerivAt_C2_diagonal_segment {r k : ℕ} {F : Vector r → ℝ}
    (hF : ContDiff ℝ 2 F) (hk : k < 2) (x a : Vector r) (t : ℝ) :
    HasDerivAt (fun s => canonicalDiagonal F k (x+s • a) a)
      (canonicalDiagonal F (k+1) (x+t • a) a) t := by
  have hd := ((hF.differentiable_iteratedFDeriv (m := k) (by exact_mod_cast hk)) (x+t • a)).hasFDerivAt
  have he := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin k => Vector r) ℝ (fun _ => a)).hasFDerivAt.comp _ hd
  have hl : HasDerivAt (fun s : ℝ => x+s • a) a t := by simpa using ((hasDerivAt_id t).smul_const a).const_add x
  have hh := he.comp_hasDerivAt t hl
  have hc : Fin.cons a (fun _ : Fin k => a) = (fun _ : Fin (k+1) => a) := by funext i; exact Fin.cases rfl (fun _ => rfl) i
  simpa only [canonicalDiagonal, ContinuousLinearMap.comp_apply, ContinuousMultilinearMap.apply_apply,
    iteratedFDeriv_succ_apply_left, hc] using hh

theorem concaveOn_of_C2_diagonal_nonpos {r : ℕ} {F : Vector r → ℝ}
    (hF : ContDiff ℝ 2 F) (hess : ∀ x a, canonicalDiagonal F 2 x a ≤ 0) :
    ConcaveOn ℝ univ F := by
  have hline (x a : Vector r) : ConcaveOn ℝ univ (fun t : ℝ => F (x+t • a)) := by
    apply concaveOn_of_hasDerivWithinAt2_nonpos convex_univ
      ((hF.continuous.comp (by fun_prop : Continuous (fun t : ℝ => x+t • a))).continuousOn)
      (f' := fun t => canonicalDiagonal F 1 (x+t • a) a)
      (f'' := fun t => canonicalDiagonal F 2 (x+t • a) a)
    · intro t _
      simpa only [canonicalDiagonal,iteratedFDeriv_zero_apply] using
        (hasDerivAt_C2_diagonal_segment hF (k := 0) (by decide) x a t).hasDerivWithinAt
    · intro t _
      exact (hasDerivAt_C2_diagonal_segment hF (k := 1) (by decide) x a t).hasDerivWithinAt
    · intro t _
      exact hess _ _
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := (hline x (y-x)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  have hpoint : x+b • (y-x) = a • x+b • y := by
    ext j
    simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
    rw [show a = 1 - b by linarith]
    ring
  simp only [smul_eq_mul,mul_zero,mul_one,add_zero,zero_add,zero_smul,one_smul,add_sub_cancel] at hh
  rw [hpoint] at hh
  exact hh

theorem C2_diagonal_nonpos_of_concaveOn {r : ℕ} {F : Vector r → ℝ}
    (hF : ContDiff ℝ 2 F) (hc : ConcaveOn ℝ univ F) (x a : Vector r) :
    canonicalDiagonal F 2 x a ≤ 0 := by
  let f : ℝ → ℝ := fun t => F (x+t • a)
  have hline : ConcaveOn ℝ univ f := by
    refine ⟨convex_univ, ?_⟩
    intro s _ t _ c d hc0 hd0 hcd
    have hh := hc.2 (mem_univ (x+s • a)) (mem_univ (x+t • a)) hc0 hd0 hcd
    have he : x+(c*s+d*t) • a = c • (x+s • a)+d • (x+t • a) := by
      ext j
      simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
      rw [show c = 1 - d by linarith]
      ring
    simpa only [f,smul_eq_mul,he] using hh
  have hfirst (t : ℝ) : HasDerivAt f (canonicalDiagonal F 1 (x+t • a) a) t := by
    simpa only [f,canonicalDiagonal,iteratedFDeriv_zero_apply] using
      hasDerivAt_C2_diagonal_segment hF (k := 0) (by decide) x a t
  have heq : deriv f = fun t => canonicalDiagonal F 1 (x+t • a) a := funext (fun t => (hfirst t).deriv)
  have hanti : Antitone (deriv f) := fun s t hst => hline.antitoneOn_deriv
    (fun t _ => (hfirst t).differentiableAt) (mem_univ s) (mem_univ t) hst
  have hd : HasDerivAt (deriv f) (canonicalDiagonal F 2 x a) 0 := by
    rw [heq]
    simpa only [zero_smul,add_zero] using hasDerivAt_C2_diagonal_segment hF (k := 1) (by decide) x a 0
  apply le_of_tendsto hd.tendsto_slope_zero_right
  filter_upwards [self_mem_nhdsWithin] with t ht
  simp only [zero_add, smul_eq_mul]
  exact mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.mpr ht.le)
    (sub_nonpos.mpr (hanti ht.le))

def gaussianWeightPotential {r : ℕ} (w : Vector r → ℝ) (x : Vector r) : ℝ :=
  vectorNormSq x/2-Real.log (w x)

theorem contDiff_half_vectorNormSq {r : ℕ} :
    ContDiff ℝ 2 (fun x : Vector r => vectorNormSq x/2) := by
  apply ContDiff.div_const
  unfold vectorNormSq
  apply ContDiff.sum
  intro i _
  exact (contDiff_apply ℝ ℝ i).pow 2

theorem half_vectorNormSq_hessian {r : ℕ} (x a : Vector r) :
    canonicalDiagonal (fun x : Vector r => vectorNormSq x/2) 2 x a = vectorNormSq a := by
  let Q : Vector r → ℝ := fun x => vectorNormSq x/2
  have hd (t : ℝ) : HasDerivAt (fun s : ℝ => Q (x+s • a))
      (faceDot x a+t*vectorNormSq a) t := by
    have hh := (HasDerivAt.sum (u := Finset.univ) (fun j _ =>
      (((hasDerivAt_const t (x j)).add ((hasDerivAt_id t).mul_const (a j))).pow 2))).div_const 2
    convert hh using 1
    simp only [faceDot, vectorNormSq, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
      Nat.cast_ofNat, Nat.reduceSub, pow_one, zero_add, one_mul, id_eq,
      Finset.sum_add_distrib, Finset.mul_sum, Finset.sum_div, Finset.sum_mul]
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have he (t : ℝ) : canonicalDiagonal Q 1 (x+t • a) a = faceDot x a+t*vectorNormSq a := by
    exact (hasDerivAt_C2_diagonal_segment contDiff_half_vectorNormSq (k := 0) (by decide) x a t).unique (hd t)
  have heq : (fun t : ℝ => canonicalDiagonal Q 1 (x+t • a) a) = fun t => faceDot x a+t*vectorNormSq a := funext he
  have h2 := hasDerivAt_C2_diagonal_segment contDiff_half_vectorNormSq (k := 1) (by decide) x a 0
  rw [heq] at h2
  simpa only [zero_smul,add_zero, Nat.reduceAdd, one_mul] using h2.unique (((hasDerivAt_id (0 : ℝ)).mul_const (vectorNormSq a)).const_add (faceDot x a))

theorem gaussianWeightPotential_hessian {r : ℕ} (w : Vector r → ℝ)
    (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x) (x a : Vector r) :
    canonicalDiagonal (gaussianWeightPotential w) 2 x a =
      vectorNormSq a-canonicalDiagonal (fun x => Real.log (w x)) 2 x a := by
  have hlog := hw.log (fun x => (hwpos x).ne')
  change (iteratedFDeriv ℝ 2
    (fun y => vectorNormSq y / 2 + -Real.log (w y)) x (fun _ => a)) = _
  rw [iteratedFDeriv_add_apply' (contDiff_half_vectorNormSq.contDiffAt) hlog.neg.contDiffAt,
    ContinuousMultilinearMap.add_apply]
  change canonicalDiagonal (fun y : Vector r => vectorNormSq y / 2) 2 x a +
      (iteratedFDeriv ℝ 2 (-(fun y => Real.log (w y))) x (fun _ => a)) = _
  rw [iteratedFDeriv_neg_apply, ContinuousMultilinearMap.neg_apply, half_vectorNormSq_hessian]
  rfl

theorem nonnegativeLogConcave_of_concave_log {r : ℕ} (w : Vector r → ℝ)
    (hwpos : ∀ x, 0 < w x) (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) :
    NonnegativeLogConcave w := by
  intro x y t ht ht1
  have hh := hc.2 (mem_univ x) (mem_univ y) (by linarith : 0 ≤ 1-t) ht.le (by ring)
  rw [Real.rpow_def_of_pos (hwpos x),Real.rpow_def_of_pos (hwpos y),← Real.exp_add]
  apply (Real.exp_le_exp.mpr _).trans_eq (Real.exp_log (hwpos _))
  simpa only [smul_eq_mul,mul_comm] using hh

/-- The Hessian-dominance input is geometric, not a desired variance
estimate. This is exactly the linear specialization cited in the remark;
its external input is proved by an explicitly alternative Prekopa proof. -/
theorem linear_variance_le_of_potential_hessian {r : ℕ}
    (w : Vector r → ℝ) (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x)
    (hw1 : ∀ x, w x ≤ 1)
    (hess : ∀ x a, vectorNormSq a ≤ canonicalDiagonal (gaussianWeightPotential w) 2 x a)
    (a : Vector r) :
    (∫ g, w g*(faceDot a g)^2 ∂standardGaussian r)/weightMass (standardGaussian r) w-
      ((∫ g, w g*faceDot a g ∂standardGaussian r)/weightMass (standardGaussian r) w)^2 ≤ vectorNormSq a := by
  have hlog := hw.log (fun x => (hwpos x).ne')
  have hc := concaveOn_of_C2_diagonal_nonpos hlog (fun x a => by
    have hh := hess x a
    rw [gaussianWeightPotential_hessian w hw hwpos] at hh
    linarith)
  have hp : 0 < ∫ g, w g ∂standardGaussian r := by
    simpa only [add_zero] using gaussian_integral_shift_pos w hw.continuous.measurable hwpos hw1 0
  exact gaussianTilt_directional_variance_le_nonnegative w hw.continuous.measurable
    (fun x => (hwpos x).le) hw1 hp (nonnegativeLogConcave_of_concave_log w hwpos hc) a

/-- The actual potential Hessian calculation printed in the remark:
log-concavity of the smooth positive weight makes the Gaussian tilt
potential at least as curved as the identity in every direction. -/
theorem gaussianWeightPotential_hessian_ge_identity {r : ℕ}
    (w : Vector r → ℝ) (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) (x a : Vector r) :
    vectorNormSq a ≤ canonicalDiagonal (gaussianWeightPotential w) 2 x a := by
  have hlog := hw.log (fun x => (hwpos x).ne')
  have hh := C2_diagonal_nonpos_of_concaveOn hlog hc x a
  rw [gaussianWeightPotential_hessian w hw hwpos]
  linarith

/-- The printed potential-to-linear-variance application chain. The
external linear specialization is implemented by the explicit Prékopa
proof above; the printed potential/Hessian step is used, not bypassed. -/
theorem linear_variance_le_via_printed_potential {r : ℕ}
    (w : Vector r → ℝ) (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x)
    (hw1 : ∀ x, w x ≤ 1)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) (a : Vector r) :
    (∫ g, w g * (faceDot a g) ^ 2 ∂standardGaussian r) / weightMass (standardGaussian r) w -
      ((∫ g, w g * faceDot a g ∂standardGaussian r) / weightMass (standardGaussian r) w) ^ 2 ≤
        vectorNormSq a :=
  linear_variance_le_of_potential_hessian w hw hwpos hw1
    (gaussianWeightPotential_hessian_ge_identity w hw hwpos hc) a

/-- The actual normalized Gaussian weighted probability law from the
remark. Positivity and total mass one are established below. -/
def gaussianWeightProbabilityLaw {r : ℕ} (w : Vector r → ℝ) : Measure (Vector r) :=
  (ENNReal.ofReal (weightMass (standardGaussian r) w))⁻¹ • gaussianTilt w

private theorem positive_weightMass {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hwpos : ∀ x, 0 < w x) (hw1 : ∀ x, w x ≤ 1) :
    0 < weightMass (standardGaussian r) w := by
  simpa only [add_zero, weightMass] using gaussian_integral_shift_pos w hw hwpos hw1 0

/-- The displayed normalized density defines a genuine probability law,
not a formal quotient of possibly zero or infinite measures. -/
theorem gaussianWeightProbabilityLaw_isProbability {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hwpos : ∀ x, 0 < w x) (hw1 : ∀ x, w x ≤ 1) :
    IsProbabilityMeasure (gaussianWeightProbabilityLaw w) := by
  letI := gaussianTilt_finite w hw (fun x => (hwpos x).le) hw1
  have hp := positive_weightMass w hw hwpos hw1
  have hreal := gaussianTilt_real_univ w hw (fun x => (hwpos x).le)
  have hmass : (gaussianTilt w) univ = ENNReal.ofReal (weightMass (standardGaussian r) w) := by
    calc
      _ = ENNReal.ofReal ((gaussianTilt w).real univ) :=
        (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
      _ = _ := congrArg ENNReal.ofReal hreal
  constructor
  rw [gaussianWeightProbabilityLaw, Measure.smul_apply, smul_eq_mul, hmass]
  exact ENNReal.inv_mul_cancel (ENNReal.ofReal_ne_zero_iff.mpr hp) ENNReal.ofReal_ne_top

/-- Every actual expectation under the normalized law is its weighted
Gaussian expectation divided by the proved positive mass. -/
theorem gaussianWeightProbabilityLaw_integral {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x)
    (hp : 0 < weightMass (standardGaussian r) w) (f : Vector r → ℝ) :
    (∫ g, f g ∂gaussianWeightProbabilityLaw w) =
      (∫ g, w g * f g ∂standardGaussian r) / weightMass (standardGaussian r) w := by
  rw [gaussianWeightProbabilityLaw, integral_smul_measure, ENNReal.toReal_inv,
    ENNReal.toReal_ofReal hp.le, smul_eq_mul, gaussianTilt_integral w hw hw₀]
  ring

/-- The actual law has precisely the normalized Gaussian density printed
in the remark, expressed by its integral against an arbitrary real test. -/
theorem gaussianWeightProbabilityLaw_integral_density {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw₀ : ∀ x, 0 ≤ w x)
    (hp : 0 < weightMass (standardGaussian r) w) (f : Vector r → ℝ) :
    (∫ g, f g ∂gaussianWeightProbabilityLaw w) =
      ∫ g, (w g / weightMass (standardGaussian r) w) * f g ∂standardGaussian r := by
  rw [gaussianWeightProbabilityLaw_integral w hw hw₀ hp, ← integral_div]
  exact integral_congr_ae (ae_of_all _ (fun g => by ring))

/-- The external Brascamp--Lieb linear specialization needed by the paper,
for the actual probability law and actual variance. The theorem is proved
from its geometric Hessian hypothesis through the explicit Prékopa proof
above, not assumed as an analytic estimate or as an axiom. -/
theorem gaussianWeightProbabilityLaw_variance_le_of_potential_hessian {r : ℕ}
    (w : Vector r → ℝ) (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x)
    (hw1 : ∀ x, w x ≤ 1)
    (hess : ∀ x a, vectorNormSq a ≤ canonicalDiagonal (gaussianWeightPotential w) 2 x a)
    (a : Vector r) :
    variance (fun g => faceDot a g) (gaussianWeightProbabilityLaw w) ≤ vectorNormSq a := by
  letI := gaussianWeightProbabilityLaw_isProbability w hw.continuous.measurable hwpos hw1
  have hp := positive_weightMass w hw.continuous.measurable hwpos hw1
  have hb (g : Vector r) : |w g| ≤ 1 := by rw [abs_of_pos (hwpos g)]; exact hw1 g
  have hi : Integrable (fun g => faceDot a g ^ 2) (gaussianTilt w) :=
    (gaussianTilt_integrable_iff w hw.continuous.measurable (fun x => (hwpos x).le) _).mpr
      (gaussian_integrable_weighted_linear_sq w hw.continuous.measurable hb a)
  have hiQ : Integrable (fun g => faceDot a g ^ 2) (gaussianWeightProbabilityLaw w) :=
    hi.smul_measure (ENNReal.inv_ne_top.mpr (ENNReal.ofReal_ne_zero_iff.mpr hp))
  have ha : Measurable (fun g : Vector r => faceDot a g) := by unfold faceDot; fun_prop
  have hLp : MemLp (fun g => faceDot a g) 2 (gaussianWeightProbabilityLaw w) :=
    (memLp_two_iff_integrable_sq ha.aestronglyMeasurable).mpr hiQ
  rw [variance_def' hLp]
  simp only [Pi.pow_apply]
  rw [gaussianWeightProbabilityLaw_integral w hw.continuous.measurable (fun x => (hwpos x).le) hp,
    gaussianWeightProbabilityLaw_integral w hw.continuous.measurable (fun x => (hwpos x).le) hp]
  exact linear_variance_le_of_potential_hessian w hw hwpos hw1 hess a

/-- The exact smooth-positive-weight argument printed in the remark:
compute the actual potential, prove its Hessian lower bound, then apply
the checked linear-variance specialization to the actual tilted law. -/
theorem gaussianWeightProbabilityLaw_variance_le_via_printed_potential {r : ℕ}
    (w : Vector r → ℝ) (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x)
    (hw1 : ∀ x, w x ≤ 1)
    (hc : ConcaveOn ℝ univ (fun x => Real.log (w x))) (a : Vector r) :
    variance (fun g => faceDot a g) (gaussianWeightProbabilityLaw w) ≤ vectorNormSq a :=
  gaussianWeightProbabilityLaw_variance_le_of_potential_hessian w hw hwpos hw1
    (gaussianWeightPotential_hessian_ge_identity w hw hwpos hc) a

/-- The actual logarithmic potential has the regularity required by its
Hessian, under the paper's smooth-positive-weight assumption. -/
theorem contDiff_gaussianWeightPotential {r : ℕ} (w : Vector r → ℝ)
    (hw : ContDiff ℝ 2 w) (hwpos : ∀ x, 0 < w x) :
    ContDiff ℝ 2 (gaussianWeightPotential w) :=
  contDiff_half_vectorNormSq.sub (hw.log (fun x => (hwpos x).ne'))

/-- The printed potential is the actual negative logarithmic Gaussian
weighted density, up to the fixed Gaussian normalizing constant. -/
theorem exp_neg_gaussianWeightPotential {r : ℕ} (w : Vector r → ℝ)
    (hwpos : ∀ x, 0 < w x) (x : Vector r) :
    Real.exp (-gaussianWeightPotential w x) = Real.exp (-vectorNormSq x / 2) * w x := by
  have he : -gaussianWeightPotential w x = -vectorNormSq x / 2 + Real.log (w x) := by
    unfold gaussianWeightPotential
    ring
  rw [he, Real.exp_add, Real.exp_log (hwpos x)]

theorem gaussian_weighted_density_eq_potential {r : ℕ} (w : Vector r → ℝ)
    (hwpos : ∀ x, 0 < w x) (x : Vector r) :
    standardGaussianDensity r x * w x =
      ((Real.sqrt (2 * Real.pi))⁻¹) ^ r * Real.exp (-gaussianWeightPotential w x) := by
  rw [exp_neg_gaussianWeightPotential w hwpos, standardGaussianDensity_eq_kernel]
  unfold gaussianKernel
  ring

/-- Arbitrary test integrals under the actual tilted law have Lebesgue
density proportional to `exp(-V)`, for the exact printed potential `V`. -/
theorem gaussianWeightProbabilityLaw_integral_potential_density {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hwpos : ∀ x, 0 < w x)
    (hp : 0 < weightMass (standardGaussian r) w) (f : Vector r → ℝ) :
    (∫ g, f g ∂gaussianWeightProbabilityLaw w) =
      ∫ g, (((Real.sqrt (2 * Real.pi))⁻¹) ^ r / weightMass (standardGaussian r) w) *
        Real.exp (-gaussianWeightPotential w g) * f g := by
  rw [gaussianWeightProbabilityLaw_integral_density w hw (fun x => (hwpos x).le) hp,
    standardGaussian_integral_density_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun g => by
    have hh := congrArg (fun z => z * f g / weightMass (standardGaussian r) w)
      (gaussian_weighted_density_eq_potential w hwpos g)
    convert hh using 1 <;> ring)

end
end RectangleCLT.Companion.SplitV4.Printed
