import RectangleCLTCompanion.SplitV4.GaussianThresholdTubes
import RectangleCLTCompanion.GaussianEntropy
import Mathlib.Probability.Independence.Integrable

/-! Printed B.3: orthogonal Gaussian coordinates really are independent.
This supplies the printed probability-factorization route in addition to
the earlier Cameron–Martin proof of the same integral identity. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- A unit linear projection of the actual product standard Gaussian has
exactly the one-dimensional standard Gaussian law. -/
theorem standardGaussian_map_unit_faceDot {r : ℕ} (u : Vector r)
    (hu : vectorNormSq u = 1) :
    (standardGaussian r).map (fun g => faceDot u g) = gaussianReal 0 1 := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n =>
    have hT := gaussianNormalSectionMap_measurePreserving u hu
    have hd : Measurable (fun g => faceDot u g) := measurable_thresholdDot u
    rw [← hT.map_eq, Measure.map_map hd hT.measurable]
    have he : (fun g => faceDot u g) ∘ gaussianNormalSectionMap u = Prod.fst := by
      funext z
      exact SignedSurface.gaussianSectionPoint_on_hyperplane u z.1 hu z.2
    rw [he, Measure.map_fst_prod]
    simp

/-- The joint law of a unit normal coordinate and an orthogonal linear
coordinate is the product of their actual laws. -/
theorem standardGaussian_map_orthogonal_pair {r : ℕ} (u t : Vector r)
    (hu : vectorNormSq u = 1) (hortho : faceDot t u = 0) :
    (standardGaussian r).map (fun g => (faceDot u g, faceDot t g)) =
      (gaussianReal 0 1).prod ((standardGaussian r).map (fun g => faceDot t g)) := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n =>
    have hT := gaussianNormalSectionMap_measurePreserving u hu
    have hj : Measurable (fun g => (faceDot u g, faceDot t g)) :=
      (measurable_thresholdDot u).prodMk (measurable_thresholdDot t)
    conv_lhs => rw [← hT.map_eq, Measure.map_map hj hT.measurable]
    have he : (fun g => (faceDot u g, faceDot t g)) ∘ gaussianNormalSectionMap u =
        Prod.map id (fun g => faceDot t g) := by
      funext z
      apply Prod.ext
      · exact SignedSurface.gaussianSectionPoint_on_hyperplane u z.1 hu z.2
      · change faceDot t (SignedSurface.gaussianSectionPoint u z.1 z.2) = faceDot t z.2
        simp only [gaussianSectionPoint_faceDot, hortho, mul_zero, zero_add,
          gaussianNormalProjection, zero_smul, sub_zero]
    rw [he]
    simpa only [Measure.map_id] using
      (Measure.map_prod_map (gaussianReal 0 1) (standardGaussian (n + 1))
        measurable_id (measurable_thresholdDot t)).symm

/-- Independence of the two orthogonal Gaussian linear forms used in
printed B.3, including the degenerate case `t=0`. -/
theorem standardGaussian_orthogonal_faceDots_independent {r : ℕ} (u t : Vector r)
    (hu : vectorNormSq u = 1) (hortho : faceDot t u = 0) :
    IndepFun (fun g => faceDot u g) (fun g => faceDot t g) (standardGaussian r) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map
    (measurable_thresholdDot u).aemeasurable (measurable_thresholdDot t).aemeasurable,
    standardGaussian_map_unit_faceDot u hu]
  exact standardGaussian_map_orthogonal_pair u t hu hortho

/-- The exact exponential factorization in printed B.3, now obtained by
independence and the Gaussian MGF rather than Cameron–Martin translation. -/
theorem gaussian_one_face_exponential_via_independence {r : ℕ}
    (β : ℝ → ℝ) (hβ : Measurable β) (hβ₀ : ∀ x, 0 ≤ β x) (hβ₁ : ∀ x, β x ≤ 1)
    (u t : Vector r) (hu : vectorNormSq u = 1) (hortho : faceDot t u = 0) :
    (∫ g, β (faceDot u g) * Real.exp (faceDot t g) ∂standardGaussian r) =
      (∫ g, β (faceDot u g) ∂standardGaussian r) * Real.exp (vectorNormSq t / 2) := by
  have hb : Integrable (fun g => β (faceDot u g)) (standardGaussian r) :=
    standardGaussian_integrable_bounded_weight _ (hβ.comp (measurable_thresholdDot u))
      (fun g => by rw [abs_of_nonneg (hβ₀ _)]; exact hβ₁ _)
  have he : Integrable (fun g => Real.exp (faceDot t g)) (standardGaussian r) := by
    simpa only [one_mul] using integrable_exp_linearProjection t 1
  have hi := (standardGaussian_orthogonal_faceDots_independent u t hu hortho).comp
    hβ Real.measurable_exp
  have hf := hi.integral_mul_of_integrable hb he
  have hmgf : (∫ g, Real.exp (faceDot t g) ∂standardGaussian r) =
      Real.exp (vectorNormSq t / 2) := by
    simpa only [mgf, one_pow, one_mul, faceDot, vectorNormSq] using
      standardGaussian_mgf_linearProjection t 1
  change (∫ g, β (faceDot u g) * Real.exp (faceDot t g) ∂standardGaussian r) =
    (∫ g, β (faceDot u g) ∂standardGaussian r) *
      (∫ g, Real.exp (faceDot t g) ∂standardGaussian r) at hf
  rw [hmgf] at hf
  exact hf

end
end RectangleCLT.Companion.SplitV4.Printed
