import RectangleCLTCompanion.GaussianEntropy
import RectangleCLTCompanion.SplitV4.Printed.GaussianOrthogonalIndependence

/-!
# Appendix B.3: Gaussian mean relative to one face

Frozen main source: lines 4959–4975 (statement), 4978–5046 (proof).
The statement environment is byte-identical to the archived release.
The proof assembles Jensen, the actual orthogonal-coordinate independence
factorization, the tangent mean decomposition, and weighted Cauchy–Schwarz. The
archive's `vectorNormSq` is the sum of coordinate squares, so it is the
Euclidean squared norm used in the manuscript, rather than the supremum norm
of its plain function-space vector representation.
-/

namespace RectangleCLTArxivV1

set_option autoImplicit false

open MeasureTheory RectangleCLT RectangleCLT.Companion

/-- The exact Gaussian mean estimate of B.3 for actual bounded measurable
weights. Positivity of the reference mass is explicit as in the paper; the
archive also derives it from domination and positivity of the tilted mass. -/
theorem gaussian_mean_relative_to_single_face {r : ℕ}
    (u : Vector r) (hu : vectorNormSq u = 1)
    (β : ℝ → ℝ) (hβ : Measurable β) (hβb : ∀ a, 0 ≤ β a ∧ β a ≤ 1)
    (w : Vector r → ℝ) (hw : Measurable w)
    (hwb : ∀ z, 0 ≤ w z ∧ w z ≤ β (faceDot u z))
    (_hpb : 0 < ∫ z, β (faceDot u z) ∂standardGaussian r)
    (hpw : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w * vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
        2 * weightMass (standardGaussian r) w *
          Real.log ((∫ z, β (faceDot u z) ∂standardGaussian r) /
            weightMass (standardGaussian r) w) :=
by
  let μ := weightMean (standardGaussian r) id w
  let t := tangentMean u μ
  let p := weightMass (standardGaussian r) w
  let b : Vector r → ℝ := fun z => β (faceDot u z)
  let pb := ∫ z, b z ∂standardGaussian r
  have hw0 : ∀ z, 0 ≤ w z := fun z => (hwb z).1
  have hbound : ∀ z, |w z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hw0 z)]
    exact (hwb z).2.trans (hβb _).2
  have hb : Measurable b := hβ.comp (Finset.measurable_sum _
    (fun j _ => measurable_const.mul (measurable_pi_apply j)))
  have hbb : ∀ z, |b z| ≤ 1 := fun z => by
    rw [abs_of_nonneg (hβb _).1]
    exact (hβb _).2
  have hwi := standardGaussian_integrable_bounded_weight w hw hbound
  have hbi := standardGaussian_integrable_bounded_weight b hb hbb
  have hppb : p ≤ pb := integral_mono hwi hbi fun z => (hwb z).2
  have hpb : 0 < pb := hpw.trans_le hppb
  have hexp : Integrable (fun z => Real.exp (faceDot t z)) (standardGaussian r) := by
    simpa only [one_mul, faceDot] using integrable_exp_linearProjection t 1
  have hwexp := hexp.bdd_mul hw.aestronglyMeasurable ⟨1, fun z => by
    simpa only [Real.norm_eq_abs] using hbound z⟩
  have hbexp := hexp.bdd_mul hb.aestronglyMeasurable ⟨1, fun z => by
    simpa only [Real.norm_eq_abs] using hbb z⟩
  have hJ := weighted_exp_mean_le (standardGaussian r) w (faceDot t) hw0 hwi
    (gaussian_integrable_weighted_linear w hw hbound t) hwexp hpw
  rw [weighted_linear_integral_eq_mean w hw hbound hpw.ne'] at hJ
  change p * Real.exp ((p * faceDot t μ) / p) ≤ _ at hJ
  rw [mul_div_cancel_left₀ _ hpw.ne'] at hJ
  have horth : faceDot u t = 0 := tangentMean_orthogonal u μ hu
  have hnormal : faceDot t μ = vectorNormSq t := by
    rw [tangentMean_dot_mean u μ, tangentMean_normSq u μ hu]
  have hI : p * Real.exp (vectorNormSq t) ≤ pb * Real.exp (vectorNormSq t / 2) := by
    calc
      _ = p * Real.exp (faceDot t μ) := by rw [hnormal]
      _ ≤ ∫ z, w z * Real.exp (faceDot t z) ∂standardGaussian r := hJ
      _ ≤ ∫ z, b z * Real.exp (faceDot t z) ∂standardGaussian r :=
        integral_mono hwexp hbexp fun z =>
          mul_le_mul_of_nonneg_right (hwb z).2 (Real.exp_nonneg _)
      _ = _ := by
        simpa only [b,pb] using
          RectangleCLT.Companion.SplitV4.Printed.gaussian_one_face_exponential_via_independence
            β hβ (fun x => (hβb x).1) (fun x => (hβb x).2) u t hu
            (by simpa only [faceDot, mul_comm] using horth)
  have hexpHalf : Real.exp (vectorNormSq t / 2) ≤ pb / p := by
    apply (le_div_iff₀ hpw).mpr
    apply (mul_le_mul_right (Real.exp_pos (vectorNormSq t / 2))).mp
    have heq : Real.exp (vectorNormSq t) =
        Real.exp (vectorNormSq t / 2) * Real.exp (vectorNormSq t / 2) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [heq] at hI
    convert hI using 1
    ring
  have hlog : vectorNormSq t ≤ 2 * Real.log (pb / p) := by
    have hh := (Real.le_log_iff_exp_le (div_pos hpb hpw)).mpr hexpHalf
    linarith
  have hsecond := weighted_mean_sq_le_second (standardGaussian r) w (faceDot u)
    hw0 hwi (gaussian_integrable_weighted_linear w hw hbound u)
    (gaussian_integrable_weighted_linear_sq w hw hbound u) hpw
  rw [weighted_linear_integral_eq_mean w hw hbound hpw.ne'] at hsecond
  change p * ((p * faceDot u μ) / p) ^ 2 ≤ _ at hsecond
  rw [mul_div_cancel_left₀ _ hpw.ne'] at hsecond
  have hscale := mul_le_mul_of_nonneg_left hlog hpw.le
  change p * vectorNormSq t ≤ p * (2 * Real.log (pb / p)) at hscale
  change p * vectorNormSq μ ≤ (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
    2 * p * Real.log (pb / p)
  change p * (faceDot u μ) ^ 2 ≤ _ at hsecond
  calc
    _ = p * (faceDot u μ) ^ 2 + p * vectorNormSq t := by
      dsimp only [t]
      rw [tangentMean_normSq u μ hu]
      ring
    _ ≤ (∫ z, w z * (faceDot u z) ^ 2 ∂standardGaussian r) +
        p * (2 * Real.log (pb / p)) := add_le_add hsecond hscale
    _ = _ := by ring

end RectangleCLTArxivV1
