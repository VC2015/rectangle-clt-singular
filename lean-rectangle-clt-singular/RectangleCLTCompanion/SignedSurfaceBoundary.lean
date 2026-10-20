import RectangleCLTCompanion.SignedSurfaceGaussianSection
import RectangleCLT.SmootherConvolution

/-! Actual Gaussian tangent integration by parts for bounded smooth tests.
These identities retain the signed ridge cancellation before any absolute
value is taken. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {r : ℕ}

theorem integrable_gaussian_bounded_mul {g P : Vector r → ℝ}
    (hg : Continuous g) (hgb : ∃ M, ∀ x, ‖g x‖ ≤ M)
    (hP : Integrable P (standardGaussian r)) :
    Integrable (fun x => P x * g x) (standardGaussian r) := by
  simpa only [mul_comm] using hP.bdd_mul hg.aestronglyMeasurable hgb

theorem standardGaussian_integrable_affine (c : ℝ) (v : Vector r) :
    Integrable (fun x => c + faceDot v x) (standardGaussian r) :=
  (integrable_const c).add (standardGaussian_integrable_faceDot v)

theorem standardGaussian_integrable_coordinate_affine (j : Fin r) (c : ℝ) (v : Vector r) :
    Integrable (fun x : Vector r => x j * (c + faceDot v x)) (standardGaussian r) := by
  have hi : Integrable (fun x : Vector r => ∑ k, v k * (x j * x k))
      (standardGaussian r) :=
    integrable_finset_sum Finset.univ (fun k _ =>
      (standardGaussian_integrable_coordinate_product r j k).const_mul (v k))
  convert ((standardGaussian_integrable_coordinate r j).mul_const c).add hi using 1
  funext x
  simp only [Pi.add_apply]
  change x j * (c + faceDot v x) = x j * c + ∑ k, v k * (x j * x k)
  rw [mul_add]
  congr 1
  simp only [faceDot, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- A linear polynomial test times a bounded `C¹` function. Gaussian first
and second moments discharge all integrability hypotheses. -/
theorem gaussian_affine_weight_directional_stein
    {g : Vector r → ℝ} {D : Fin r → Vector r → ℝ}
    (hg : Continuous g) (hD : ∀ j, Continuous (D j))
    (hderiv : ∀ j x, HasDerivAt (fun t => g (Function.update x j t)) (D j x) (x j))
    (hgb : ∃ M, ∀ x, ‖g x‖ ≤ M) (hDb : ∀ j, ∃ M, ∀ x, ‖D j x‖ ≤ M)
    (c : ℝ) (v u : Vector r) :
    (∫ x, faceDot u x * (c + faceDot v x) * g x ∂standardGaussian r) =
      faceDot u v * (∫ x, g x ∂standardGaussian r) +
        ∑ j, u j * (∫ x, (c + faceDot v x) * D j x ∂standardGaussian r) := by
  have hgi := integrable_gaussian_bounded_mul hg hgb (standardGaussian_integrable_affine c v)
  have hg0 : Integrable g (standardGaussian r) := by
    simpa only [one_mul] using integrable_gaussian_bounded_mul hg hgb
      (integrable_const (1 : ℝ))
  have hDi (j : Fin r) : Integrable (fun x => (c + faceDot v x) * D j x)
      (standardGaussian r) :=
    integrable_gaussian_bounded_mul (hD j) (hDb j) (standardGaussian_integrable_affine c v)
  have hdi (j : Fin r) : Integrable
      (fun x => v j * g x + (c + faceDot v x) * D j x) (standardGaussian r) :=
    (hg0.const_mul _).add (hDi j)
  have hxgi (j : Fin r) : Integrable (fun x => x j * ((c + faceDot v x) * g x))
      (standardGaussian r) := by
    simpa only [mul_assoc] using integrable_gaussian_bounded_mul hg hgb
      (standardGaussian_integrable_coordinate_affine j c v)
  have hd (j : Fin r) (x : Vector r) : HasDerivAt
      (fun t => (c + faceDot v (Function.update x j t)) * g (Function.update x j t))
      (v j * g x + (c + faceDot v x) * D j x) (x j) := by
    simpa only [Function.update_eq_self] using
      ((hasDerivAt_faceDot_update v x j).const_add c).mul (hderiv j x)
  have hh := standardGaussian_directional_stein_of_integrable u hd hgi hdi hxgi
  calc
    _ = ∫ x, faceDot u x * ((c + faceDot v x) * g x) ∂standardGaussian r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = _ := hh
    _ = ∑ j, u j * (v j * (∫ x, g x ∂standardGaussian r) +
        (∫ x, (c + faceDot v x) * D j x ∂standardGaussian r)) := by
      rw [integral_finset_sum Finset.univ (fun j _ => (hdi j).const_mul (u j))]
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul, integral_add (hg0.const_mul _) (hDi j), integral_const_mul]
    _ = _ := by
      simp only [faceDot, mul_add, Finset.sum_add_distrib, Finset.sum_mul]
      congr 1
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem faceDot_single_left (j : Fin r) (x : Vector r) :
    faceDot (Pi.single j 1) x = x j := by
  simp [faceDot, Pi.single_apply, ite_mul]

/-- The radial Gaussian score is the actual integral of the radial
coordinate derivative. -/
theorem gaussian_radial_score_stein
    {g : Vector r → ℝ} {D : Fin r → Vector r → ℝ}
    (hg : Continuous g) (hD : ∀ j, Continuous (D j))
    (hderiv : ∀ j x, HasDerivAt (fun t => g (Function.update x j t)) (D j x) (x j))
    (hgb : ∃ M, ∀ x, ‖g x‖ ≤ M) (hDb : ∀ j, ∃ M, ∀ x, ‖D j x‖ ≤ M) :
    (∫ x, (vectorNormSq x - (r : ℝ)) * g x ∂standardGaussian r) =
      ∑ j, (∫ x, x j * D j x ∂standardGaussian r) := by
  classical
  have hgi : Integrable g (standardGaussian r) := by
    simpa only [one_mul] using integrable_gaussian_bounded_mul hg hgb
      (integrable_const (1 : ℝ))
  have hsq (j : Fin r) : Integrable (fun x => x j ^ 2 * g x) (standardGaussian r) :=
    integrable_gaussian_bounded_mul hg hgb (standardGaussian_integrable_coordinate_pow r j 2)
  have heach (j : Fin r) :
      (∫ x, x j ^ 2 * g x ∂standardGaussian r) =
        (∫ x, g x ∂standardGaussian r) + (∫ x, x j * D j x ∂standardGaussian r) := by
    have hh := gaussian_affine_weight_directional_stein hg hD hderiv hgb hDb 0
      (Pi.single j 1) (Pi.single j 1)
    simpa [faceDot_single_left, Pi.single_apply, ite_mul, sq] using hh
  calc
    _ = ∫ x, vectorNormSq x * g x - (r : ℝ) * g x ∂standardGaussian r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun x => by ring)
    _ = (∫ x, (vectorNormSq x * g x) ∂standardGaussian r) -
        (r : ℝ) * (∫ x, g x ∂standardGaussian r) := by
      rw [integral_sub
        (integrable_gaussian_bounded_mul hg hgb (standardGaussian_integrable_vectorNormSq r))
        (hgi.const_mul (r : ℝ)), integral_const_mul]
    _ = (∑ j, ∫ x, x j ^ 2 * g x ∂standardGaussian r) -
        (r : ℝ) * (∫ x, g x ∂standardGaussian r) := by
      congr 1
      simp_rw [vectorNormSq, Finset.sum_mul]
      exact integral_finset_sum Finset.univ (fun j _ => hsq j)
    _ = _ := by
      simp_rw [heach]
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul]
      ring

/-- Decomposition into the score in one unit normal direction and the
actual tangent derivative. This is an equality for the concrete product
Gaussian, including arbitrary ambient dimension. -/
theorem gaussian_tangent_score_stein
    {g : Vector r → ℝ} {D : Fin r → Vector r → ℝ}
    (hg : Continuous g) (hD : ∀ j, Continuous (D j))
    (hderiv : ∀ j x, HasDerivAt (fun t => g (Function.update x j t)) (D j x) (x j))
    (hgb : ∃ M, ∀ x, ‖g x‖ ≤ M) (hDb : ∀ j, ∃ M, ∀ x, ‖D j x‖ ≤ M)
    (u : Vector r) (hu : vectorNormSq u = 1) :
    (∫ x, (vectorNormSq x - (r : ℝ)) * g x ∂standardGaussian r) =
      (∫ x, (faceDot u x ^ 2 - 1) * g x ∂standardGaussian r) +
        (∫ x, ∑ j, (x j - faceDot u x * u j) * D j x ∂standardGaussian r) := by
  have hgi : Integrable g (standardGaussian r) := by
    simpa only [one_mul] using integrable_gaussian_bounded_mul hg hgb
      (integrable_const (1 : ℝ))
  have hDxi (j : Fin r) : Integrable (fun x => x j * D j x) (standardGaussian r) :=
    integrable_gaussian_bounded_mul (hD j) (hDb j) (standardGaussian_integrable_coordinate r j)
  have hDui (j : Fin r) : Integrable (fun x => faceDot u x * D j x) (standardGaussian r) :=
    integrable_gaussian_bounded_mul (hD j) (hDb j) (standardGaussian_integrable_faceDot u)
  have hrank := gaussian_affine_weight_directional_stein hg hD hderiv hgb hDb 0 u u
  have huu : faceDot u u = 1 := by simpa only [faceDot, vectorNormSq, sq] using hu
  simp only [zero_add, huu, one_mul] at hrank
  have hnormal : (∫ x, (faceDot u x ^ 2 - 1) * g x ∂standardGaussian r) =
      ∑ j, u j * (∫ x, faceDot u x * D j x ∂standardGaussian r) := by
    calc
      _ = (∫ x, faceDot u x * faceDot u x * g x ∂standardGaussian r) -
          (∫ x, g x ∂standardGaussian r) := by
        rw [← integral_sub (integrable_gaussian_bounded_mul hg hgb
          (standardGaussian_integrable_faceDot_product u u)) hgi]
        apply integral_congr_ae
        exact ae_of_all _ (fun x => by ring)
      _ = _ := by rw [hrank]; ring
  have htan : (∫ x, ∑ j, (x j - faceDot u x * u j) * D j x ∂standardGaussian r) =
      (∑ j, ∫ x, x j * D j x ∂standardGaussian r) -
        ∑ j, u j * (∫ x, faceDot u x * D j x ∂standardGaussian r) := by
    calc
      _ = ∫ x, ∑ j, (x j * D j x - u j * (faceDot u x * D j x))
          ∂standardGaussian r := by
        apply integral_congr_ae
        exact ae_of_all _ (fun x => Finset.sum_congr rfl (fun j _ => by ring))
      _ = ∑ j, ∫ x, (x j * D j x - u j * (faceDot u x * D j x))
          ∂standardGaussian r :=
        integral_finset_sum Finset.univ (fun j _ => (hDxi j).sub ((hDui j).const_mul (u j)))
      _ = _ := by
        simp_rw [integral_sub (hDxi _) ((hDui _).const_mul _), integral_const_mul]
        rw [Finset.sum_sub_distrib]
  rw [gaussian_radial_score_stein hg hD hderiv hgb hDb, hnormal, htan]
  ring

end
end RectangleCLT.Companion.SignedSurface
