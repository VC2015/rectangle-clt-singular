import RectangleCLTArxivV1.SignedCoordinates
import RectangleCLTArxivV1.BernsteinMixedTail
import RectangleCLT.GaussianMaximum
import RectangleCLT.GaussianComparisonLaw
import RectangleCLTCompanion.FactorExistence
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.LinearAlgebra.Matrix.ToLin
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators NNReal ENNReal
namespace RectangleCLTArxivV1

/-- Every admissible covariance admits an actual Gaussian factor, with no
lower spectral bound and no nonsingularity assumption. -/
theorem gaussian_factor_exists {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → RectangleCLT.Vector p} {δ : ℝ}
    (h : RectangleCLT.BoundedIndependentHypotheses μ ξ δ) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = RectangleCLT.covariance μ (RectangleCLT.sumVector ξ) :=
  RectangleCLT.Companion.gaussian_factor_exists_of_boundedIndependent h

/-- The concrete Gaussian law is carried by the factor range. Zero
eigenvalues reduce this support without changing the representation. -/
theorem gaussianLaw_ae_mem_factor_range {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    ∀ᵐ x ∂RectangleCLT.gaussianLaw A, x ∈ Set.range A.mulVec := by
  apply ae_map_mem_range
  change MeasurableSet ((LinearMap.range (Matrix.mulVecLin A)) : Set (Fin p → ℝ))
  exact (LinearMap.range (Matrix.mulVecLin A)).closed_of_finiteDimensional.measurableSet

lemma integral_x_exp_half :
    (∫ x : ℝ in Ioi 0, x * Real.exp (-(1/2:ℝ) * x ^ 2)) = 1 := by
  have hb : (0:ℝ) < (1/2:ℂ).re := by norm_num
  have h := congrArg Complex.re (integral_mul_cexp_neg_mul_sq hb)
  rw [← RCLike.re_eq_complex_re, ← integral_re (integrable_mul_cexp_neg_mul_sq hb).integrableOn] at h
  convert h using 1 <;> norm_num
  apply setIntegral_congr_fun measurableSet_Ioi
  intro x _
  norm_cast
  dsimp only
  rw [show -(1 / 2 * (↑(x ^ 2) : ℂ)) = ((-( (1 / 2 : ℝ) * x ^ 2) : ℝ) : ℂ) by push_cast; ring, Complex.exp_ofReal_re]

lemma standardNormal_integral_abs :
    (∫ x : ℝ, |x| ∂gaussianReal 0 1) = Real.sqrt (2 / Real.pi) := by
  rw [integral_gaussianReal_eq_integral_smul (by norm_num : (1:ℝ≥0) ≠ 0)]
  simp only [gaussianPDFReal, NNReal.coe_one, mul_one, sub_zero, smul_eq_mul]
  have heq : (fun x : ℝ => (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-x ^ 2 / 2) * |x|) =
      (fun x => (Real.sqrt (2 * Real.pi))⁻¹ * (|x| * Real.exp (-(1/2:ℝ) * |x| ^ 2))) := by
    funext x
    rw [sq_abs]
    rw [show -x ^ 2 / 2 = -(1 / 2 : ℝ) * x ^ 2 by ring]
    ring
  rw [heq, integral_const_mul, integral_comp_abs (f := fun x : ℝ => x * Real.exp (-(1/2:ℝ) * x ^ 2)), integral_x_exp_half]
  have hp : 0 < Real.pi := Real.pi_pos
  have hs : 0 < Real.sqrt (2 * Real.pi) := by positivity
  have hs2 : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi := Real.sq_sqrt (by positivity)
  apply (sq_eq_sq₀ (by positivity) (Real.sqrt_nonneg _)).mp
  rw [Real.sq_sqrt (by positivity)]
  rw [mul_pow, inv_pow, hs2]
  field_simp
  ring

/-- Euclidean coefficient rows of a covariance factor. The factor may have
arbitrary rank; no inverse or nonzero eigenvalue is used. -/
noncomputable def factorRows {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) (j : Fin p) :
    EuclideanSpace ℝ (Fin r) := (WithLp.equiv 2 (Fin r → ℝ)).symm (A j)

theorem gaussianLinear_factorRows {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (j : Fin p) (g : Fin r → ℝ) :
    GenericChaining.gaussianLinear (factorRows A j) g = A.mulVec g j := by
  unfold GenericChaining.gaussianLinear Matrix.mulVec dotProduct
  apply Finset.sum_congr rfl
  intro k _
  exact mul_comm _ _

theorem factorRows_norm_sq {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ) (j : Fin p) :
    ‖factorRows A j‖ ^ 2 = (A * A.transpose) j j := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp [factorRows, Matrix.mul_apply, Matrix.transpose_apply, Real.norm_eq_abs, sq_abs, pow_two]

theorem signed_factorRows_apply {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (t : SignedIndex p) (k : Fin r) :
    signedVectors (factorRows A) t k = signedVectors (fun j => A j) t k := by
  cases t with
  | none => rfl
  | some v => rcases v with ⟨b, j⟩; cases b <;> rfl

/-- The signed canonical norm is exactly the quadratic form of the factor
covariance, including all zero and perfectly correlated contrasts. -/
theorem signed_factorRows_norm_sq {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (s t : SignedIndex p) :
    ‖signedVectors (factorRows A) t - signedVectors (factorRows A) s‖ ^ 2 =
      RectangleCLT.matrixQuadratic (A * A.transpose) (signedDirection t - signedDirection s) := by
  rw [RectangleCLT.Companion.matrixQuadratic_gram, PiLp.norm_sq_eq_of_L2,
    transpose_mulVec_signedContrast]
  simp only [Real.norm_eq_abs, sq_abs, PiLp.sub_apply, Pi.sub_apply, signed_factorRows_apply]

/-- The variance metric of the actual bounded sum is the canonical Gaussian
metric of any factor of its covariance. This is the exact bridge between the
Bernstein input and the majorizing-measure input. -/
theorem signedVarianceMetric_eq_canonicalDist {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    {ξ : Fin n → Ω → RectangleCLT.Vector p} {δ : ℝ}
    (h : RectangleCLT.BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = RectangleCLT.covariance μ (RectangleCLT.sumVector ξ)) :
    signedVarianceMetric μ ξ = GenericChaining.canonicalDist (signedVectors (factorRows A)) := by
  funext s t
  apply Subtype.ext
  change (signedVarianceMetric μ ξ s t : ℝ) =
    ‖signedVectors (factorRows A) s - signedVectors (factorRows A) t‖
  apply (sq_eq_sq₀ (NNReal.coe_nonneg _) (norm_nonneg _)).mp
  rw [signedVarianceMetric_sq_covariance h, ← hfactor]
  exact (signed_factorRows_norm_sq A t s).symm

/-- The paper's Gaussian maximum, defined using the actual Gaussian
pushforward law rather than an assumed width parameter. -/
noncomputable def gaussianMaximumMean {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : ℝ :=
  ∫ x : Fin p → ℝ, ‖x‖ ∂RectangleCLT.gaussianLaw A

theorem gaussianMaximumMean_nonneg {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ gaussianMaximumMean A := integral_nonneg (fun _ => norm_nonneg _)

/-- The parameter is determined by the covariance, even when its factors
have nontrivial kernels. Thus it is legitimately the paper's `g_Σ`. -/
theorem gaussianMaximumMean_eq_of_covariance {p : ℕ} {A B : Matrix (Fin p) (Fin p) ℝ}
    (hcov : A * A.transpose = B * B.transpose) : gaussianMaximumMean A = gaussianMaximumMean B := by
  unfold gaussianMaximumMean
  rw [RectangleCLT.gaussianLaw_eq_of_factor_covariance hcov]

/-- The library's one-sided maximum of the signed Euclidean process is
exactly the infinity-norm Gaussian maximum printed as `g_Σ`. -/
theorem gaussianWidth_signedFactorRows {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gaussianWidth (signedVectors (factorRows A)) = gaussianMaximumMean A := by
  unfold GenericChaining.gaussianWidth GenericChaining.gaussianMaximum gaussianMaximumMean
    RectangleCLT.gaussianLaw
  rw [integral_map (RectangleCLT.measurable_mulVec A).aemeasurable measurable_norm.aestronglyMeasurable]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro g
  simp only [signedGaussianLinear, gaussianLinear_factorRows, signedMaximum_eq_norm]

/-- Square integrability of every signed contrast under the actual Gaussian law. -/
theorem gaussianLaw_integrable_signedContrast_sq {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (s t : SignedIndex p) :
    Integrable (fun x => (signedCoordinate t x - signedCoordinate s x) ^ 2)
      (RectangleCLT.gaussianLaw A) := by
  have hi := GenericChaining.gaussianLinear_integrable_contrast_sq
    (signedVectors (factorRows A) t) (signedVectors (factorRows A) s)
  have hi' : Integrable
      (fun g => (signedCoordinate t (A.mulVec g) - signedCoordinate s (A.mulVec g)) ^ 2)
      (RectangleCLT.standardGaussian p) := by
    simpa only [signedGaussianLinear, gaussianLinear_factorRows] using hi
  exact (integrable_map_measure
    (((signedCoordinate_measurable t).sub (signedCoordinate_measurable s)).pow_const 2).aestronglyMeasurable
    (RectangleCLT.measurable_mulVec A).aemeasurable).mpr hi'

/-- The actual Gaussian signed process has exactly the Euclidean canonical metric. -/
theorem gaussianLaw_integral_signedContrast_sq {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (s t : SignedIndex p) :
    (∫ x, (signedCoordinate t x - signedCoordinate s x) ^ 2 ∂RectangleCLT.gaussianLaw A) =
      ‖signedVectors (factorRows A) t - signedVectors (factorRows A) s‖ ^ 2 := by
  unfold RectangleCLT.gaussianLaw
  rw [integral_map (RectangleCLT.measurable_mulVec A).aemeasurable
    (((signedCoordinate_measurable t).sub (signedCoordinate_measurable s)).pow_const 2).aestronglyMeasurable]
  simpa only [signedGaussianLinear, gaussianLinear_factorRows] using
    GenericChaining.gaussianLinear_canonical_increment
      (signedVectors (factorRows A) t) (signedVectors (factorRows A) s)

/-- Zero canonical distance identifies Gaussian coordinates almost surely.
This reduction applies also to perfect positive and negative correlations. -/
theorem gaussianLaw_signedCoordinate_ae_eq_of_zero_dist {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (s t : SignedIndex p)
    (hzero : GenericChaining.canonicalDist (signedVectors (factorRows A)) t s = 0) :
    signedCoordinate t =ᵐ[RectangleCLT.gaussianLaw A] signedCoordinate s := by
  apply GenericChaining.ae_eq_of_zero_contrast
    (gaussianLaw_integrable_signedContrast_sq A s t)
  rw [gaussianLaw_integral_signedContrast_sq]
  have hn := congrArg (fun z : ℝ≥0 => (z : ℝ)) hzero
  change ‖signedVectors (factorRows A) t - signedVectors (factorRows A) s‖ = 0 at hn
  rw [hn, zero_pow (by decide)]

/-- Finiteness is justified before taking the real value of the chaining functional. -/
theorem gamma2_signedFactorRows_ne_top {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gamma2 (fun s t =>
      (GenericChaining.canonicalDist (signedVectors (factorRows A)) s t : ℝ≥0∞)) ≠ ⊤ :=
  GenericChaining.gamma2_canonicalDist_ne_top _

/-- C2.6: the majorizing-measure theorem applies without a covariance rank
assumption and without identifying any indices for the discrete metric. -/
theorem gamma2_signedFactorRows_le {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    (GenericChaining.gamma2 (fun s t =>
      (GenericChaining.canonicalDist (signedVectors (factorRows A)) s t : ℝ≥0∞))).toReal ≤
      GenericChaining.gaussianMajorizingConstant * gaussianMaximumMean A := by
  simpa only [gaussianWidth_signedFactorRows] using
    GenericChaining.gamma2_le_gaussianWidth (signedVectors (factorRows A))

/-- C2.7: any unit-variance marginal gives the exact dimension-free lower
bound used to absorb the additive constant, including dimension one. -/
theorem sqrt_two_div_pi_le_gaussianMaximumMean {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1) :
    Real.sqrt (2 / Real.pi) ≤ gaussianMaximumMean A := by
  let j : Fin p := ⟨0, by omega⟩
  have hm := integral_map (μ := RectangleCLT.gaussianLaw A)
    (measurable_pi_apply j).aemeasurable (f := fun x : ℝ => |x|)
    measurable_id.abs.aestronglyMeasurable
  rw [RectangleCLT.gaussianLaw_map_eval_eq_standard A j (hdiag j), standardNormal_integral_abs] at hm
  rw [hm]
  exact integral_mono (RectangleCLT.gaussianLaw_integrable_coordinate A j).abs
    (RectangleCLT.gaussianLaw_integrable_norm A)
    (fun x => by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j)

/-- Identifying repeated signed coefficient vectors preserves the canonical
chaining functional. This quotient concerns only the Gaussian metric: the
discrete metric continues to use the original `SignedIndex p` type. -/
theorem gamma2_signedFactorRows_eq_range {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gamma2 (fun s t =>
      (GenericChaining.canonicalDist (signedVectors (factorRows A)) s t : ℝ≥0∞)) =
    GenericChaining.gamma2 (fun s t : Set.range (signedVectors (factorRows A)) =>
      (GenericChaining.canonicalDist
        (fun v : Set.range (signedVectors (factorRows A)) => v.val) s t : ℝ≥0∞)) :=
  GenericChaining.gamma2_canonicalDist_range (signedVectors (factorRows A))

/-- The finite image of the signed vectors has the same Gaussian maximum
almost surely. The checked zero-contrast quotient theorem supplies this
identification, including perfect positive and negative correlations. -/
theorem gaussianMaximum_signedFactorRows_ae_eq_range {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gaussianMaximum (signedVectors (factorRows A))
      =ᵐ[GenericChaining.standardGaussian p]
    GenericChaining.gaussianMaximum
      (fun v : Set.range (signedVectors (factorRows A)) => v.val) := by
  classical
  let q := Set.rangeFactorization (signedVectors (factorRows A))
  have hq : Function.Surjective q := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  exact GenericChaining.gaussianMaximum_ae_eq_of_vector_quotient q hq
    (signedVectors (factorRows A)) (fun v => v.val) (fun _ => rfl)

/-- Removing duplicate Gaussian indices preserves the actual one-sided width. -/
theorem gaussianWidth_signedFactorRows_eq_range {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gaussianWidth (signedVectors (factorRows A)) =
    GenericChaining.gaussianWidth
      (fun v : Set.range (signedVectors (factorRows A)) => v.val) := by
  classical
  let q := Set.rangeFactorization (signedVectors (factorRows A))
  have hq : Function.Surjective q := by
    rintro ⟨x, t, rfl⟩
    exact ⟨t, rfl⟩
  exact GenericChaining.gaussianWidth_of_vector_quotient q hq
    (signedVectors (factorRows A)) (fun v => v.val) (fun _ => rfl)

/-- The quotient width is still precisely the paper's `g_Σ`, rather than
a new parameter attached to a reduced coordinate model. -/
theorem gaussianWidth_signedFactorRows_range {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) :
    GenericChaining.gaussianWidth
      (fun v : Set.range (signedVectors (factorRows A)) => v.val) = gaussianMaximumMean A :=
  (gaussianWidth_signedFactorRows_eq_range A).symm.trans (gaussianWidth_signedFactorRows A)

end RectangleCLTArxivV1
