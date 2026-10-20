import RectangleCLT.InterpolationLaw
import RectangleCLT.ThinningMoments

/-! The covariance of the concrete independent-product interpolation law.
The identity permits distinct original and Gaussian covariances, and does
not require either covariance to be invertible. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u v

namespace RectangleCLT

theorem covariance_map {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (hW : Measurable W) :
    covariance (μ.map W) id = covariance μ W := by
  ext j k
  unfold covariance
  simp only [id_eq]
  rw [integral_map hW.aemeasurable
    ((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable,
    integral_map hW.aemeasurable (measurable_pi_apply j).aestronglyMeasurable,
    integral_map hW.aemeasurable (measurable_pi_apply k).aestronglyMeasurable]

/-- Covariances of centered vectors on independent product spaces add. -/
theorem covariance_prod_add_of_centered
    {Ω : Type u} [MeasurableSpace Ω] {Ω' : Type v} [MeasurableSpace Ω'] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ω') [IsProbabilityMeasure ν]
    (W : Ω → Vector p) (Z : Ω' → Vector p)
    (hW : ∀ j, Integrable (fun ω => W ω j) μ)
    (hZ : ∀ j, Integrable (fun ω => Z ω j) ν)
    (hWW : ∀ j k, Integrable (fun ω => W ω j * W ω k) μ)
    (hZZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) ν)
    (hW₀ : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hZ₀ : ∀ j, (∫ ω, Z ω j ∂ν) = 0) :
    covariance (μ.prod ν) (fun ω => W ω.1 + Z ω.2) =
      covariance μ W + covariance ν Z := by
  have hfst (j : Fin p) : Integrable (fun ω : Ω × Ω' => W ω.1 j) (μ.prod ν) := by
    simpa only [mul_one] using (hW j).mul_prod (integrable_const (1 : ℝ))
  have hsnd (j : Fin p) : Integrable (fun ω : Ω × Ω' => Z ω.2 j) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (hZ j)
  have hfstprod (j k : Fin p) :
      Integrable (fun ω : Ω × Ω' => W ω.1 j * W ω.1 k) (μ.prod ν) := by
    simpa only [mul_one] using (hWW j k).mul_prod (integrable_const (1 : ℝ))
  have hsndprod (j k : Fin p) :
      Integrable (fun ω : Ω × Ω' => Z ω.2 j * Z ω.2 k) (μ.prod ν) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (hZZ j k)
  have hcross (j k : Fin p) :
      Integrable (fun ω : Ω × Ω' => W ω.1 j * Z ω.2 k) (μ.prod ν) :=
    (hW j).mul_prod (hZ k)
  have hmean (j : Fin p) : (∫ ω : Ω × Ω', W ω.1 j + Z ω.2 j ∂μ.prod ν) = 0 := by
    rw [integral_add (hfst j) (hsnd j),
      integral_fun_fst (μ := μ) (ν := ν) (fun ω => W ω j),
      integral_fun_snd (μ := μ) (ν := ν) (fun ω => Z ω j), hW₀, hZ₀]
    simp
  ext j k
  simp only [covariance, Pi.add_apply, Matrix.add_apply, hmean, hW₀, hZ₀,
    zero_mul, sub_zero]
  have hpoint (ω : Ω × Ω') :
      (W ω.1 j + Z ω.2 j) * (W ω.1 k + Z ω.2 k) =
        ((W ω.1 j * W ω.1 k + W ω.1 j * Z ω.2 k) +
          W ω.1 k * Z ω.2 j) + Z ω.2 j * Z ω.2 k := by ring
  simp_rw [hpoint]
  rw [integral_add (f := fun ω : Ω × Ω' =>
      (W ω.1 j * W ω.1 k + W ω.1 j * Z ω.2 k) + W ω.1 k * Z ω.2 j)
      (((hfstprod j k).add (hcross j k)).add (hcross k j)) (hsndprod j k),
    integral_add (f := fun ω : Ω × Ω' => W ω.1 j * W ω.1 k + W ω.1 j * Z ω.2 k)
      ((hfstprod j k).add (hcross j k)) (hcross k j),
    integral_add (hfstprod j k) (hcross j k),
    integral_fun_fst (μ := μ) (ν := ν) (fun ω => W ω j * W ω k),
    integral_fun_snd (μ := μ) (ν := ν) (fun ω => Z ω j * Z ω k),
    integral_prod_mul (fun ω => W ω j) (fun ω => Z ω k),
    integral_prod_mul (fun ω => W ω k) (fun ω => Z ω j), hW₀, hW₀, hZ₀, hZ₀]
  simp

/-- The actual full path covariance, not just its formal scalar coefficient. -/
theorem interpolationLaw_covariance
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hLp : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    covariance (interpolationLaw μ ξ A t) id =
      (1 - t) • covariance μ (sumVector ξ) + t • (A * A.transpose) := by
  let ν := bernoulliArrayLaw μ ξ t
  let B := interpolatedGaussianFactor A t
  letI : IsProbabilityMeasure ν := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  have hInt (i : Fin n) (j : Fin p) : Integrable (fun ω => ξ i ω j) μ :=
    (hLp i j).integrable (by norm_num)
  have hnewInt (i : Fin n) (j : Fin p) :
      Integrable (fun a : Fin n → Vector p => a i j) ν := by
    have hh := integrable_bernoulliArrayLaw_coordinateProduct μ ξ hξ t i
      (fun _ : Fin 1 => j) (by decide) (by simpa using hInt i j)
    have heq : arrayCoordinateProduct i (fun _ : Fin 1 => j) =
        (fun a : Fin n → Vector p => a i j) := by
      funext a
      simp [arrayCoordinateProduct]
    rwa [heq] at hh
  have hnewProd (i l : Fin n) (j k : Fin p) :
      Integrable (fun a : Fin n → Vector p => a i j * a l k) ν :=
    integrable_bernoulliArrayLaw_cross μ ξ hξ t i l j k
      ((hLp i j).integrable_mul (hLp l k))
  have hsumInt (j : Fin p) : Integrable (fun a : Fin n → Vector p => arraySum a j) ν := by
    simpa [arraySum] using integrable_finset_sum Finset.univ (fun i _ => hnewInt i j)
  have hsumProd (j k : Fin p) :
      Integrable (fun a : Fin n → Vector p => arraySum a j * arraySum a k) ν := by
    have hh := integrable_finset_sum Finset.univ (fun i _ =>
      integrable_finset_sum Finset.univ (fun l _ => hnewProd i l j k))
    have heq : (fun a : Fin n → Vector p => arraySum a j * arraySum a k) =
        (fun a => ∑ i, ∑ l, a i j * a l k) := by
      funext a
      simp only [arraySum, Finset.sum_apply]
      rw [Finset.sum_mul]
      simp_rw [Finset.mul_sum]
    rw [heq]
    exact hh
  have hsumMean (j : Fin p) : (∫ a : Fin n → Vector p, arraySum a j ∂ν) = 0 := by
    have hnewMean := bernoulliArrayLaw_centered μ ξ hξ t ht ht1 hInt hcenter
    simp only [arraySum, Finset.sum_apply]
    rw [integral_finset_sum Finset.univ (fun i _ => hnewInt i j)]
    change (∑ i, ∫ a, a i j ∂bernoulliArrayLaw μ ξ t) = 0
    simp only [hnewMean, Finset.sum_const_zero]
  unfold interpolationLaw
  rw [covariance_map _ _ (measurable_interpolationSum p n)]
  change covariance (ν.prod (gaussianLaw B)) (fun ω => arraySum ω.1 + id ω.2) = _
  rw [covariance_prod_add_of_centered ν (gaussianLaw B) arraySum id
    hsumInt (gaussianLaw_integrable_coordinate B) hsumProd
    (gaussianLaw_integrable_coordinate_product B) hsumMean (gaussianLaw_integral_coordinate B)]
  change covariance (bernoulliArrayLaw μ ξ t) (fun a => ∑ i, a i) +
    covariance (gaussianLaw (interpolatedGaussianFactor A t)) id = _
  rw [bernoulliArrayLaw_sum_covariance μ ξ hξ hind hLp hcenter t ht ht1,
    interpolatedGaussian_covariance A ht]

/-- With matched covariance the concrete interpolation keeps the original
covariance at every point, including both endpoints. -/
theorem interpolationLaw_covariance_matched
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hLp : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (sumVector ξ))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    covariance (interpolationLaw μ ξ A t) id = covariance μ (sumVector ξ) := by
  rw [interpolationLaw_covariance μ ξ hξ hind hLp hcenter A t ht ht1, hfactor]
  ext j k
  simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

end RectangleCLT
