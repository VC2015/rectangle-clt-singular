import RectangleCLT.GaussianHeat
import RectangleCLT.GaussianDualBounds

/-!
# Full-covariance Gaussian score identities

This is an analytic foundation for the full-eigenvalue derivative branch:
the inverse-covariance Stein identity is proved for the actual Gaussian
law, and full coordinate dual directions have squared norm at most `ν⁻¹`.
These facts alone do not bound the sum of the separate fourth-derivative
local suprema, and no such cap or global CLT is asserted here.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

/-- The inverse covariance score, with the sign convention for the Stein
identity `E[score_j g] = E[∂_j g]`. -/
def fullGaussianScore {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (j : Fin p) : ℝ :=
  ((A * A.transpose)⁻¹).mulVec x j

theorem factor_covariance_det_isUnit_of_full_lower {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) :
    IsUnit (A * A.transpose).det := by
  have hQ : (A * A.transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose A
  have hpos : (A * A.transpose).PosDef := by
    refine ⟨hQ.isHermitian, ?_⟩
    intro v hv
    have hh := (mul_pos hν (vectorNormSq_pos hv)).trans_le (hlower v)
    simpa only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum,
      mul_assoc, star_trivial] using hh
  exact hpos.det_pos.ne'.isUnit

/-- A genuine inverse-covariance Gaussian integration-by-parts identity.
The hypotheses concern differentiability, measurability, and ordinary
boundedness of a test function; no Gaussian derivative estimate is assumed. -/
theorem gaussianLaw_inverse_stein {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (j : Fin p) {g : Vector p → ℝ} {dg : Vector p → Vector p}
    (hgderiv : ∀ x r, HasDerivAt
      (fun t : ℝ => g (x + t • (fun k => A k r)))
      (∑ k, A k r * dg x k) 0)
    (hgmeas : Measurable g) (hdgmeas : ∀ k, Measurable (fun x => dg x k))
    (hgbounded : ∃ C : ℝ, ∀ x, |g x| ≤ C)
    (hdgbounded : ∃ D : ℝ, ∀ x k, |dg x k| ≤ D) :
    (∫ x, fullGaussianScore A x j * g x ∂gaussianLaw A) =
      ∫ x, dg x j ∂gaussianLaw A := by
  classical
  obtain ⟨C, hC⟩ := hgbounded
  have hi (r : Fin p) : Integrable (fun x : Vector p => x r * g x) (gaussianLaw A) := by
    simpa only [mul_comm] using (gaussianLaw_integrable_coordinate A r).bdd_mul
      hgmeas.aestronglyMeasurable
      ⟨C, fun x => by simpa only [Real.norm_eq_abs] using hC x⟩
  have hstein : (fun r => ∫ x : Vector p, x r * g x ∂gaussianLaw A) =
      (A * A.transpose).mulVec (fun k => ∫ x, dg x k ∂gaussianLaw A) := by
    funext r
    exact gaussianLaw_stein A r hgderiv hgmeas hdgmeas ⟨C, hC⟩ hdgbounded
  calc
    (∫ x, fullGaussianScore A x j * g x ∂gaussianLaw A) =
        ((A * A.transpose)⁻¹).mulVec
          (fun r => ∫ x : Vector p, x r * g x ∂gaussianLaw A) j := by
      unfold fullGaussianScore Matrix.mulVec dotProduct
      simp only [Finset.sum_mul, mul_assoc]
      rw [integral_finset_sum Finset.univ (fun r _ =>
        (hi r).const_mul ((A * A.transpose)⁻¹ j r))]
      simp only [integral_const_mul]
    _ = ((A * A.transpose)⁻¹).mulVec
        ((A * A.transpose).mulVec (fun k => ∫ x, dg x k ∂gaussianLaw A)) j := by
      rw [hstein]
    _ = _ := by
      rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hd, Matrix.one_mulVec]

/-- The full dual direction corresponding to a coordinate. -/
def fullGaussianDual {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) : Vector p :=
  A.transpose.mulVec (((A * A.transpose)⁻¹).mulVec (FaceSmoother.coordinateDirection j))

theorem fullGaussianDual_right_inverse {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det) (j : Fin p) :
    A.mulVec (fullGaussianDual A j) = FaceSmoother.coordinateDirection j := by
  unfold fullGaussianDual
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hd,
    Matrix.one_mulVec]

theorem fullGaussianDual_normSq_eq {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det) (j : Fin p) :
    vectorNormSq (fullGaussianDual A j) =
      faceDot (FaceSmoother.coordinateDirection j)
        (((A * A.transpose)⁻¹).mulVec (FaceSmoother.coordinateDirection j)) := by
  let v := ((A * A.transpose)⁻¹).mulVec (FaceSmoother.coordinateDirection j)
  have hAv : A.mulVec (A.transpose.mulVec v) = FaceSmoother.coordinateDirection j :=
    fullGaussianDual_right_inverse A hd j
  change (∑ k, (A.transpose.mulVec v k) ^ 2) = faceDot (FaceSmoother.coordinateDirection j) v
  calc
    _ = dotProduct (A.transpose.mulVec v) (A.transpose.mulVec v) := by
      simp only [dotProduct, pow_two]
    _ = dotProduct v (A.mulVec (A.transpose.mulVec v)) := by
      rw [Matrix.dotProduct_mulVec v A (A.transpose.mulVec v), ← Matrix.mulVec_transpose]
    _ = dotProduct v (FaceSmoother.coordinateDirection j) := by rw [hAv]
    _ = _ := by rw [dotProduct_comm]; rfl

/-- The exact inverse-eigenvalue score variance bound. Here `ν` is an
eigenvalue, not its square root. -/
theorem fullGaussianDual_normSq_le_inv {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (j : Fin p) : vectorNormSq (fullGaussianDual A j) ≤ 1 / ν := by
  rw [fullGaussianDual_normSq_eq A hd j]
  apply inverse_quadratic_le_inv _ hd hν hlower
  simp [vectorNormSq, FaceSmoother.coordinateDirection]

/-- Normalized full coordinate duals are genuine Gaussian projection rows
of variance at most one, ready for the existing maximum-moment estimates. -/
theorem normalized_fullGaussianDual_normSq_le_one {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (j : Fin p) :
    (∑ k, (Real.sqrt ν * fullGaussianDual A j k) ^ 2) ≤ 1 := by
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  have hh := fullGaussianDual_normSq_le_inv A hd hν hlower j
  have hscaled := mul_le_mul_of_nonneg_left hh hν.le
  calc
    _ = ν * vectorNormSq (fullGaussianDual A j) := by
      simp only [mul_pow, Real.sq_sqrt hν.le, vectorNormSq, Finset.mul_sum]
    _ ≤ ν * (1 / ν) := hscaled
    _ = 1 := by field_simp [hν.ne']

def normalizedFullGaussianScoreFamily {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (z : Vector p) : Vector p :=
  linearProjectionFamily (fun j k => Real.sqrt ν * fullGaussianDual A j k) z

/-- A threshold-independent maximum of all full coordinate score directions
has the usual Gaussian maximum exponential bound. The directions may be
dependent; only their proved variance bounds are used. -/
theorem integral_exp_normalizedFullGaussianScoreFamily_le {p : ℕ}
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (t : ℝ) :
    (∫ z, Real.exp (t * ‖normalizedFullGaussianScoreFamily A ν z‖)
      ∂standardGaussian p) ≤ (2 * (p : ℝ)) * Real.exp (t ^ 2 / 2) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  simpa only [normalizedFullGaussianScoreFamily, Fintype.card_fin] using
    integral_exp_projectionMaximum_le (fun j k => Real.sqrt ν * fullGaussianDual A j k)
      (normalized_fullGaussianDual_normSq_le_one A hν hlower) t

/-- Scaling the full-score maximum by `sqrt(log(e*p))` gives a bound whose
constant is independent of the dimension and the full eigenvalue. -/
theorem integral_exp_scaled_normalizedFullGaussianScoreFamily_le {p : ℕ}
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (t : ℝ) :
    (∫ z, Real.exp ((t / Real.sqrt (dimensionLog p)) *
      ‖normalizedFullGaussianScoreFamily A ν z‖) ∂standardGaussian p) ≤
        Real.exp (2 + t ^ 2 / 2) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hL := log_exp_mul_nat_ge_one hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from hp)
  have hcard : 2 * (p : ℝ) ≤ Real.exp (2 * dimensionLog p) := by
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
    calc
      2 * (p : ℝ) ≤ Real.exp 1 * (p : ℝ) := mul_le_mul_of_nonneg_right he hp₀.le
      _ = Real.exp (dimensionLog p) := by
        rw [dimensionLog, Real.exp_log (mul_pos (Real.exp_pos 1) hp₀)]
      _ ≤ Real.exp (2 * dimensionLog p) := Real.exp_le_exp.mpr (by linarith)
  simpa only [normalizedFullGaussianScoreFamily, Fintype.card_fin] using
    integral_exp_projectionMaximum_scaled_le
      (fun j k => Real.sqrt ν * fullGaussianDual A j k)
      (normalized_fullGaussianDual_normSq_le_one A hν hlower) hL hcard t

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- The actual first derivative of the Gaussian convolution has the inverse
covariance score representation. All test-function assumptions are proved
for the concrete rational smoother. -/
theorem gaussian_convolutionFirstDerivative_score
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (r : Vector p) (j : Fin p) :
    s.convolutionFirstDerivative (gaussianLaw A) r j =
      ∫ z, fullGaussianScore A z j * s.F (r + z) ∂gaussianLaw A := by
  rw [s.convolutionFirstDerivative_eq_integral]
  symm
  apply gaussianLaw_inverse_stein A hd j
  · intro z a
    simpa only [line, zero_smul, add_zero, add_assoc] using
      s.hasDerivAt_F_line_sum (r + z) (fun k => A k a) 0
  · exact (s.continuous_F.comp (continuous_const.add continuous_id)).measurable
  · intro k
    exact ((s.continuous_firstDerivative k).comp
      (continuous_const.add continuous_id)).measurable
  · exact ⟨1, fun z => by simpa only [Real.norm_eq_abs] using s.norm_F_le_one (r + z)⟩
  · exact ⟨1 / s.bandwidth, fun z k => by
      simpa only [Real.norm_eq_abs] using s.norm_firstDerivative_le (r + z) k⟩

/-- One actual Gaussian second derivative is an inverse score times the
corresponding actual first derivative. This is the first integration-by-parts
step needed by a full-eigenvalue higher-derivative proof. -/
theorem gaussian_convolutionSecondDerivative_score
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (A * A.transpose).det)
    (r : Vector p) (j k : Fin p) :
    s.convolutionSecondDerivative (gaussianLaw A) r j k =
      ∫ z, fullGaussianScore A z k * s.coordinateDerivativeF (r + z) j
        ∂gaussianLaw A := by
  rw [s.convolutionSecondDerivative_eq_integral]
  symm
  apply gaussianLaw_inverse_stein A hd k
  · intro z a
    simpa only [line, zero_smul, add_zero, add_assoc] using
      s.hasDerivAt_firstDerivative_line_sum (r + z) (fun l => A l a) j 0
  · exact ((s.continuous_firstDerivative j).comp
      (continuous_const.add continuous_id)).measurable
  · intro l
    exact ((s.continuous_secondDerivative j l).comp
      (continuous_const.add continuous_id)).measurable
  · exact ⟨1 / s.bandwidth, fun z => by
      simpa only [Real.norm_eq_abs] using s.norm_firstDerivative_le (r + z) j⟩
  · exact ⟨3 / s.bandwidth ^ 2, fun z l => by
      simpa only [Real.norm_eq_abs] using s.norm_secondDerivative_le (r + z) j l⟩

end FaceSmoother

end

end RectangleCLT
