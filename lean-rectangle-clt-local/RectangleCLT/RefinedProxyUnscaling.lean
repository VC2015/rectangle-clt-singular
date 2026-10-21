import RectangleCLT.RefinedProxyNoiseStability
import RectangleCLT.CoordinateRescaling
import RectangleCLT.GaussianComparisonLaw

/-! Exact positive rescaling and two actual noise-stability estimates
transfer a regularized matched-covariance approximation to the original
bounded observation sum. -/

open MeasureTheory
namespace RectangleCLT
noncomputable section

private theorem gaussianLaw_one (p : ℕ) :
    gaussianLaw (1 : Matrix (Fin p) (Fin p) ℝ) = standardGaussian p := by
  unfold gaussianLaw
  have heq : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec = id := by
    funext z
    simp
  rw [heq, Measure.map_id]

theorem gaussian_normalized_noisy_law {p : ℕ}
    (A D : Matrix (Fin p) (Fin p) ℝ) (a ε : ℝ)
    (hcov : D*D.transpose = a⁻¹^2 • (A*A.transpose) +
      (a⁻¹*Real.sqrt ε)^2 • (1 : Matrix (Fin p) (Fin p) ℝ)) :
    ((standardGaussian p).prod (standardGaussian p)).map
      (fun z => a⁻¹ • (A.mulVec z.1 + Real.sqrt ε • z.2)) = gaussianLaw D := by
  have hh := gaussianLaw_scaled_sum A (1 : Matrix (Fin p) (Fin p) ℝ) D
    a⁻¹ (a⁻¹*Real.sqrt ε) (by simpa using hcov)
  have hprod : (gaussianLaw A).prod (standardGaussian p) =
      ((standardGaussian p).prod (standardGaussian p)).map
        (Prod.map A.mulVec id) := by
    simpa only [gaussianLaw, Measure.map_id] using
      (Measure.map_prod_map (standardGaussian p) (standardGaussian p)
        (measurable_mulVec A) measurable_id)
  rw [gaussianLaw_one, hprod, Measure.map_map
    (measurable_gaussianScaledSum _ _)
    ((measurable_mulVec A).prodMap measurable_id)] at hh
  convert hh using 2
  funext z
  simp only [Function.comp_apply, Prod.map_apply, id_eq, gaussianScaledSum,
    smul_add, smul_smul]
  rfl

theorem regularized_rectangleError_identity
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p : ℕ}
    (W : Ω → Vector p) (A D : Matrix (Fin p) (Fin p) ℝ)
    {a ε : ℝ} (ha : 0 < a)
    (hcov : D*D.transpose = a⁻¹^2 • (A*A.transpose) +
      (a⁻¹*Real.sqrt ε)^2 • (1 : Matrix (Fin p) (Fin p) ℝ)) (R : Rect p) :
    rectangleError (μ.prod (standardGaussian p))
      (fun z => a⁻¹ • (W z.1 + Real.sqrt ε • z.2)) D
      (R.preimageCoordinateScale (fun _ => a) (fun _ => ha)) =
    |(μ.prod (standardGaussian p)).real
      {z | W z.1 + Real.sqrt ε • z.2 ∈ R.carrier} -
     ((standardGaussian p).prod (standardGaussian p)).real
      {z | A.mulVec z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| := by
  have hmem (x : Vector p) :
      a⁻¹ • x ∈ (R.preimageCoordinateScale (fun _ => a) (fun _ => ha)).carrier ↔
        x ∈ R.carrier := by
    change scaleCoordinates (fun _ => a) (a⁻¹ • x) ∈ R.carrier ↔ x ∈ R.carrier
    have heq : scaleCoordinates (fun _ => a) (a⁻¹ • x) = x := by
      ext j
      simp [scaleCoordinates, smul_eq_mul, ← mul_assoc, ha.ne']
    rw [heq]
  unfold rectangleError
  rw [← gaussian_normalized_noisy_law A D a ε hcov]
  have hmeas : Measurable (fun z : Vector p × Vector p =>
      a⁻¹ • (A.mulVec z.1 + Real.sqrt ε • z.2)) := by fun_prop
  rw [map_measureReal_apply hmeas
    (R.preimageCoordinateScale (fun _ => a) (fun _ => ha)).measurableSet_carrier]
  congr 2 <;> congr 1 <;> ext z <;> exact hmem _

/-- The regularized approximation cost plus two actual perturbation costs.
The observation and Gaussian covariance may be singular. -/
theorem bounded_regularized_error_transfer
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ ε a : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A D : Matrix (Fin p) (Fin p) ℝ) (hA : ∀ j, (A*A.transpose) j j = 1)
    (ha : 0 < a) (hε : 0 ≤ ε)
    (hcov : D*D.transpose = a⁻¹^2 • (A*A.transpose) +
      (a⁻¹*Real.sqrt ε)^2 • (1 : Matrix (Fin p) (Fin p) ℝ)) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R ≤
      rectangleError (μ.prod (standardGaussian p))
        (fun z => a⁻¹ • (sumVector ξ z.1 + Real.sqrt ε • z.2)) D
        (R.preimageCoordinateScale (fun _ => a) (fun _ => ha)) +
      (4*1073741824)*(2*Real.sqrt ε*dimensionLog p+δ*Real.sqrt (dimensionLog p)) := by
  have hW := bounded_gaussian_noise_stability μ ξ h hp hdiag hε R
  have hG := gaussian_gaussian_noise_stability hp A hA hε R
  rw [regularized_rectangleError_identity μ (sumVector ξ) A D ha hcov R]
  unfold rectangleError
  have hlaw : (gaussianLaw A).real R.carrier =
      (standardGaussian p).real {z | A.mulVec z ∈ R.carrier} := by
    exact map_measureReal_apply (measurable_mulVec A) R.measurableSet_carrier
  rw [hlaw]
  change |μ.real {ω | sumVector ξ ω ∈ R.carrier} -
      (standardGaussian p).real {z | A.mulVec z ∈ R.carrier}| ≤ _
  have ht := abs_sub_le (μ.real {ω | sumVector ξ ω ∈ R.carrier})
    ((μ.prod (standardGaussian p)).real
      {z | sumVector ξ z.1 + Real.sqrt ε • z.2 ∈ R.carrier})
    ((standardGaussian p).real {z | A.mulVec z ∈ R.carrier})
  have hu := abs_sub_le ((μ.prod (standardGaussian p)).real
      {z | sumVector ξ z.1 + Real.sqrt ε • z.2 ∈ R.carrier})
    (((standardGaussian p).prod (standardGaussian p)).real
      {z | A.mulVec z.1 + Real.sqrt ε • z.2 ∈ R.carrier})
    ((standardGaussian p).real {z | A.mulVec z ∈ R.carrier})
  rw [abs_sub_comm] at hG
  linarith

end
end RectangleCLT
