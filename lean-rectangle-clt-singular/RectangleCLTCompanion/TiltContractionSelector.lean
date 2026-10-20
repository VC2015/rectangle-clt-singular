import RectangleCLT.GaussianNormalMap
import RectangleCLTCompanion.MatrixReduction
import Mathlib.Analysis.Convex.Deriv

/-!
# Log-concavity of the concrete selector weights

These are pointwise and moment foundations for Gaussian covariance
contraction. They do not assume or assert preservation of log-concavity under
marginalization (Prékopa's theorem).
-/

open MeasureTheory Set
open scoped BigOperators Topology

namespace RectangleCLT.Companion

noncomputable section

variable {p k : ℕ} (s : FaceSmoother p)

/-- The actual selector, with repeated face indices allowed. -/
def selectorWeight (faces : Fin k → Face p) (x : Vector p) : ℝ :=
  s.F x * ∏ i, s.pi x (faces i)

theorem selectorWeight_nonneg (faces : Fin k → Face p) (x : Vector p) :
    0 ≤ selectorWeight s faces x :=
  mul_nonneg (s.F_pos x).le
    (Finset.prod_nonneg (fun i _ => (s.weights x).pi_nonneg (faces i)))

theorem selectorWeight_pos (faces : Fin k → Face p)
    (hactive : ∀ i, faces i ∈ s.faces) (x : Vector p) :
    0 < selectorWeight s faces x := by
  apply mul_pos (s.F_pos x)
  apply Finset.prod_pos
  intro i _
  change 0 < (s.weights x).weight (faces i) / (1 + (s.weights x).T)
  apply div_pos _ (s.weights x).denominator_pos
  simp only [FaceSmoother.weights, hactive, ↓reduceIte]
  exact Real.exp_pos _

theorem selectorWeight_le_one (faces : Fin k → Face p) (x : Vector p) :
    selectorWeight s faces x ≤ 1 := by
  have hp : (∏ i, s.pi x (faces i)) ≤ 1 := by
    apply Finset.prod_le_one
    · intro i _
      exact (s.weights x).pi_nonneg (faces i)
    · intro i _
      exact ((s.weights x).pi_le_theta (faces i)).trans (s.weights x).theta_lt_one.le
  calc
    _ ≤ s.F x * 1 := mul_le_mul_of_nonneg_left hp (s.F_pos x).le
    _ ≤ 1 := by simpa only [mul_one] using s.F_le_one x

theorem continuous_selectorWeight (faces : Fin k → Face p) :
    Continuous (selectorWeight s faces) :=
  s.continuous_F.mul (continuous_finset_prod _ (fun i _ => s.continuous_pi (faces i)))

/-- The logarithm has a linear numerator and a convex log-sum-exp denominator. -/
theorem log_selectorWeight_eq (faces : Fin k → Face p)
    (hactive : ∀ i, faces i ∈ s.faces) (x : Vector p) :
    Real.log (selectorWeight s faces x) =
      (∑ i, s.faceScore (faces i) x) / s.bandwidth -
        ((k : ℝ) + 1) * (s.potential x / s.bandwidth) := by
  have hpi (i : Fin k) : s.pi x (faces i) ≠ 0 := by
    change (s.weights x).weight (faces i) / (1 + (s.weights x).T) ≠ 0
    apply div_ne_zero _ (s.weights x).denominator_pos.ne'
    simp only [FaceSmoother.weights, hactive, ↓reduceIte]
    exact (Real.exp_pos _).ne'
  have hlog (i : Fin k) : Real.log (s.pi x (faces i)) =
      s.faceScore (faces i) x / s.bandwidth - Real.log (1 + (s.weights x).T) := by
    change Real.log ((s.weights x).weight (faces i) / (1 + (s.weights x).T)) = _
    have hw : (s.weights x).weight (faces i) =
        Real.exp (s.faceScore (faces i) x / s.bandwidth) := by
      simp only [FaceSmoother.weights, hactive, ↓reduceIte]
    rw [Real.log_div (by rw [hw]; exact (Real.exp_pos _).ne')
      (s.weights x).denominator_pos.ne', hw, Real.log_exp]
  unfold selectorWeight
  rw [Real.log_mul (s.F_pos x).ne' (Finset.prod_ne_zero_iff.mpr (fun i _ => hpi i)),
    Real.log_prod Finset.univ _ (fun i _ => hpi i)]
  simp_rw [hlog]
  simp only [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  change Real.log (1 / (1 + (s.weights x).T)) + _ = _
  rw [one_div, Real.log_inv]
  unfold FaceSmoother.potential
  field_simp [s.bandwidth_pos.ne']
  ring

/-- Actual nonnegative second derivatives on every line give convexity of
the rational smoother's logarithmic potential in the whole coordinate space. -/
theorem convexOn_smootherPotential : ConvexOn ℝ univ s.potential := by
  have hline (x y : Vector p) : ConvexOn ℝ univ
      (fun t : ℝ => s.potential (FaceSmoother.line x y t)) := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (f' := fun t =>
      (s.weights (FaceSmoother.line x y t)).directionalMean y)
      (f'' := fun t => (s.weights (FaceSmoother.line x y t)).directionalCovariance y /
        s.bandwidth) convex_univ
    · intro t _
      exact (s.hasDerivAt_potential_line x y t).continuousAt.continuousWithinAt
    · intro t _
      exact (s.hasDerivAt_potential_line x y t).hasDerivWithinAt
    · intro t _
      exact (s.hasDerivAt_directionalMean_line x y t).hasDerivWithinAt
    · intro t _
      exact div_nonneg ((s.weights _).directionalCovariance_nonneg y) s.bandwidth_pos.le
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hh := (hline x (y - x)).2 (mem_univ (0 : ℝ)) (mem_univ (1 : ℝ)) ha hb hab
  have h1 : FaceSmoother.line x (y - x) 1 = y := by
    ext j
    simp only [FaceSmoother.line, one_mul, Pi.sub_apply]
    ring
  have hmix : FaceSmoother.line x (y - x) b = a • x + b • y := by
    ext j
    simp only [FaceSmoother.line, Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show a = 1 - b by linarith]
    ring
  simpa only [smul_eq_mul, mul_zero, mul_one, zero_add, FaceSmoother.line_zero,
    h1, hmix] using hh

/-- The selector's logarithm is genuinely concave, including repeated
indices. All selected faces are active, so the logarithm is taken of a
strictly positive function. -/
theorem concaveOn_log_selectorWeight (faces : Fin k → Face p)
    (hactive : ∀ i, faces i ∈ s.faces) :
    ConcaveOn ℝ univ (fun x => Real.log (selectorWeight s faces x)) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hp := (convexOn_smootherPotential s).2 (mem_univ x) (mem_univ y) ha hb hab
  have hlinear (f : Face p) : s.faceScore f (a • x + b • y) =
      a * s.faceScore f x + b * s.faceScore f y := by
    unfold FaceSmoother.faceScore FaceSmoother.normalDot
    cases hf : f.2 <;> simp only [hf, Bool.false_eq_true, ↓reduceIte,
      Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    all_goals rw [show a = 1 - b by linarith]; ring
  have hsum : (∑ i, s.faceScore (faces i) (a • x + b • y)) =
      a * (∑ i, s.faceScore (faces i) x) + b * (∑ i, s.faceScore (faces i) y) := by
    simp_rw [hlinear, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hc : 0 ≤ (k : ℝ) + 1 := by positivity
  have hscaled := mul_le_mul_of_nonneg_left
    (div_le_div_of_nonneg_right hp s.bandwidth_pos.le) hc
  simp only [smul_eq_mul] at hscaled ⊢
  rw [log_selectorWeight_eq s faces hactive, log_selectorWeight_eq s faces hactive,
    log_selectorWeight_eq s faces hactive, hsum]
  simp only [add_div, mul_div_assoc] at hscaled ⊢
  nlinarith

/-- Pullback through an arbitrary affine Gaussian factor preserves the
proved pointwise log-concavity. The factor may be rectangular or singular. -/
theorem concaveOn_log_selectorWeight_affine {r : ℕ}
    (faces : Fin k → Face p) (hactive : ∀ i, faces i ∈ s.faces)
    (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    ConcaveOn ℝ univ
      (fun g : Vector r => Real.log (selectorWeight s faces (B.mulVec g + v))) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have h := (concaveOn_log_selectorWeight s faces hactive).2
    (mem_univ (B.mulVec x + v)) (mem_univ (B.mulVec y + v)) ha hb hab
  have heq : B.mulVec (a • x + b • y) + v =
      a • (B.mulVec x + v) + b • (B.mulVec y + v) := by
    rw [Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul]
    ext j
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    rw [show a = 1 - b by linarith]
    ring
  simpa only [heq] using h

theorem continuous_selectorWeight_affine {r : ℕ}
    (faces : Fin k → Face p) (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    Continuous (fun g : Vector r => selectorWeight s faces (B.mulVec g + v)) := by
  have hB : Continuous (fun g : Vector r => B.mulVec g) := by
    apply continuous_pi
    intro j
    change Continuous (fun g : Vector r => ∑ i : Fin r, B j i * g i)
    exact continuous_finset_sum _ (fun i _ => continuous_const.mul (continuous_apply i))
  exact (continuous_selectorWeight s faces).comp (hB.add continuous_const)

/-- Every polynomial moment used by the actual covariance is integrable. -/
theorem selectorWeight_affine_moments {r : ℕ}
    (faces : Fin k → Face p) (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    Integrable (fun g : Vector r => selectorWeight s faces (B.mulVec g + v))
        (standardGaussian r) ∧
      (∀ j, Integrable (fun g : Vector r => g j *
        selectorWeight s faces (B.mulVec g + v)) (standardGaussian r)) ∧
      (∀ j l, Integrable (fun g : Vector r => g j * g l *
        selectorWeight s faces (B.mulVec g + v)) (standardGaussian r)) := by
  have hm := (continuous_selectorWeight_affine s faces B v).measurable
  have hb (g : Vector r) : |selectorWeight s faces (B.mulVec g + v)| ≤ 1 := by
    rw [abs_of_nonneg (selectorWeight_nonneg s faces _)]
    exact selectorWeight_le_one s faces _
  exact ⟨standardGaussian_integrable_bounded_weight _ hm hb,
    standardGaussian_integrable_weighted_coordinate _ hm hb,
    standardGaussian_integrable_weighted_product _ hm hb⟩

/-- Active selector weights have strictly positive actual Gaussian mass,
even for singular or zero affine factors. -/
theorem selectorWeight_affine_mass_pos {r : ℕ}
    (faces : Fin k → Face p) (hactive : ∀ i, faces i ∈ s.faces)
    (B : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) :
    0 < weightMass (standardGaussian r)
      (fun g => selectorWeight s faces (B.mulVec g + v)) := by
  unfold weightMass
  rw [integral_pos_iff_support_of_nonneg
    (fun g => selectorWeight_nonneg s faces _) (selectorWeight_affine_moments s faces B v).1]
  have hs : Function.support (fun g : Vector r => selectorWeight s faces (B.mulVec g + v)) =
      univ := by
    ext g
    simp only [Function.mem_support, ne_eq, (selectorWeight_pos s faces hactive _).ne',
      not_false_eq_true, mem_univ]
  rw [hs]
  simp

end

end RectangleCLT.Companion
