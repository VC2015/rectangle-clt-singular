import RectangleCLTCompanion.RestorationScore
import RectangleCLT.TranslationTaylor

/-! Two genuine integrations by parts against the finite standard Gaussian.
The first results are generic derivative witnesses; actual smoother
specializations below discharge their regularity and moment hypotheses. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {r : ℕ}

/-- Twice the already proved first Gaussian Stein identity.  In particular,
the quadratic score correction is exactly one on a repeated coordinate. -/
theorem standardGaussian_second_coordinate_stein
    (f : Vector r → ℝ) (d : Fin r → Vector r → ℝ)
    (dd : Fin r → Fin r → Vector r → ℝ)
    (hf : ∀ j g, HasDerivAt (fun t => f (Function.update g j t)) (d j g) (g j))
    (hd : ∀ j k g, HasDerivAt (fun t => d j (Function.update g k t)) (dd j k g) (g k))
    (hfi : Integrable f (standardGaussian r))
    (hdi : ∀ j, Integrable (d j) (standardGaussian r))
    (hddi : ∀ j k, Integrable (dd j k) (standardGaussian r))
    (hgf : ∀ j, Integrable (fun g => g j * f g) (standardGaussian r))
    (hggf : ∀ j k, Integrable (fun g => g j * g k * f g) (standardGaussian r))
    (hgd : ∀ j k, Integrable (fun g => g k * d j g) (standardGaussian r))
    (j k : Fin r) :
    (∫ g, (g j * g k - if j = k then 1 else 0) * f g ∂standardGaussian r) =
      ∫ g, dd j k g ∂standardGaussian r := by
  classical
  have hdiff (g : Vector r) : HasDerivAt
      (fun t => (Function.update g j t) k * f (Function.update g j t))
      ((if j = k then 1 else 0) * f g + g k * d j g) (g j) := by
    by_cases h : j = k
    · subst k
      simpa only [Function.update_self, Function.update_eq_self, ↓reduceIte] using
        (hasDerivAt_id (g j)).mul (hf j g)
    · simpa only [Function.update_of_ne (Ne.symm h), Function.update_eq_self,
        h, ↓reduceIte] using (hasDerivAt_const (g j) (g k)).mul (hf j g)
  have hsum := (hfi.const_mul (if j = k then 1 else 0)).add (hgd j k)
  have hleft : Integrable (fun g => g j * (g k * f g)) (standardGaussian r) := by
    simpa only [mul_assoc] using hggf j k
  have hs := standardGaussian_coordinate_stein_of_integrable j hdiff
    (hgf k) hsum hleft
  have ht := standardGaussian_coordinate_stein_of_integrable k (hd j k)
    (hdi j) (hddi j k) (hgd j k)
  have heq (g : Vector r) :
      (g j * g k - if j = k then 1 else 0) * f g =
        g j * (g k * f g) - (if j = k then 1 else 0) * f g := by ring
  simp_rw [heq]
  dsimp only [Pi.add_apply] at hs
  rw [integral_add (hfi.const_mul _) (hgd j k)] at hs
  rw [integral_sub hleft (hfi.const_mul _), hs, ht]
  ring

/-- Directional second Stein identity, retaining the actual repeated-pair
score needed for the dimension-free coefficient trace reduction. -/
theorem standardGaussian_second_directional_stein
    (f : Vector r → ℝ) (d : Fin r → Vector r → ℝ)
    (dd : Fin r → Fin r → Vector r → ℝ)
    (hf : ∀ j g, HasDerivAt (fun t => f (Function.update g j t)) (d j g) (g j))
    (hd : ∀ j k g, HasDerivAt (fun t => d j (Function.update g k t)) (dd j k g) (g k))
    (hfi : Integrable f (standardGaussian r))
    (hdi : ∀ j, Integrable (d j) (standardGaussian r))
    (hddi : ∀ j k, Integrable (dd j k) (standardGaussian r))
    (hgf : ∀ j, Integrable (fun g => g j * f g) (standardGaussian r))
    (hggf : ∀ j k, Integrable (fun g => g j * g k * f g) (standardGaussian r))
    (hgd : ∀ j k, Integrable (fun g => g k * d j g) (standardGaussian r))
    (z : Vector r) :
    (∫ g, repeatedDirectionScore g z * f g ∂standardGaussian r) =
      ∫ g, matrixQuadratic (fun j k => dd j k g) z ∂standardGaussian r := by
  have hscore := integral_repeatedDirectionScore_eq_quadratic
    (standardGaussian r) id f hfi hggf z
  have hs : weightedScore (standardGaussian r) id f =
      fun j k => ∫ g, dd j k g ∂standardGaussian r := by
    ext j k
    exact standardGaussian_second_coordinate_stein f d dd hf hd hfi hdi hddi
      hgf hggf hgd j k
  calc
    _ = matrixQuadratic (weightedScore (standardGaussian r) id f) z := hscore
    _ = _ := by rw [hs, matrixQuadratic_integral (standardGaussian r) _ hddi]

private theorem integrable_gaussian_bounded
    (f : Vector r → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ g, |f g| ≤ C) :
    Integrable f (standardGaussian r) := by
  obtain ⟨C, hC⟩ := hb
  exact (integrable_const C).mono' hf.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun g => hC g))

private theorem integrable_gaussian_coordinate_mul_bounded
    (f : Vector r → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ g, |f g| ≤ C) (j : Fin r) :
    Integrable (fun g => g j * f g) (standardGaussian r) := by
  obtain ⟨C, hC⟩ := hb
  simpa only [mul_comm] using
    (standardGaussian_integrable_coordinate r j).bdd_mul hf.aestronglyMeasurable
      ⟨C, fun g => hC g⟩

private theorem integrable_gaussian_product_mul_bounded
    (f : Vector r → ℝ) (hf : Measurable f)
    (hb : ∃ C : ℝ, ∀ g, |f g| ≤ C) (j k : Fin r) :
    Integrable (fun g => g j * g k * f g) (standardGaussian r) := by
  obtain ⟨C, hC⟩ := hb
  simpa only [mul_comm] using
    (standardGaussian_integrable_coordinate_product r j k).bdd_mul hf.aestronglyMeasurable
      ⟨C, fun g => hC g⟩

/-- Bounded measurable Gaussian derivative jets automatically satisfy every
integrability premise of the twice integrated formula. -/
theorem standardGaussian_second_directional_stein_bounded
    (f : Vector r → ℝ) (d : Fin r → Vector r → ℝ)
    (dd : Fin r → Fin r → Vector r → ℝ)
    (hf : ∀ j g, HasDerivAt (fun t => f (Function.update g j t)) (d j g) (g j))
    (hd : ∀ j k g, HasDerivAt (fun t => d j (Function.update g k t)) (dd j k g) (g k))
    (hfm : Measurable f) (hdm : ∀ j, Measurable (d j))
    (hddm : ∀ j k, Measurable (dd j k))
    (hfb : ∃ C : ℝ, ∀ g, |f g| ≤ C)
    (hdb : ∀ j, ∃ C : ℝ, ∀ g, |d j g| ≤ C)
    (hddb : ∀ j k, ∃ C : ℝ, ∀ g, |dd j k g| ≤ C) (z : Vector r) :
    (∫ g, repeatedDirectionScore g z * f g ∂standardGaussian r) =
      ∫ g, matrixQuadratic (fun j k => dd j k g) z ∂standardGaussian r :=
  standardGaussian_second_directional_stein f d dd hf hd
    (integrable_gaussian_bounded f hfm hfb)
    (fun j => integrable_gaussian_bounded (d j) (hdm j) (hdb j))
    (fun j k => integrable_gaussian_bounded (dd j k) (hddm j k) (hddb j k))
    (integrable_gaussian_coordinate_mul_bounded f hfm hfb)
    (integrable_gaussian_product_mul_bounded f hfm hfb)
    (fun j k => integrable_gaussian_coordinate_mul_bounded (d j) (hdm j) (hdb j) k) z

end
end RectangleCLT.Companion
