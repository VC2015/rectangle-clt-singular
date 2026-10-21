import RectangleCLT.GlobalDerivativeTubeFaceBounds
import RectangleCLT.GlobalDerivativeBounds

/-! Concrete full-score face moments obtained from the actual dual tubes.
The probability input is a boundary bound for an independent base vector;
the applications supply it from bounded or Gaussian concentration. -/

open MeasureTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

def dualFaceMoment {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (r : Vector p) (k : ℕ) : ℝ :=
  s.fullDualGaussianSoftFaceMoment A ν r (activeFaces S) k / s.bandwidth ^ q

theorem dualFaceMoment_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℝ) (r : Vector p) (k : ℕ) : 0 ≤ dualFaceMoment S s A ν r k :=
  div_nonneg (s.fullDualGaussianSoftFaceMoment_nonneg A ν r _ k)
    (pow_nonneg s.bandwidth_pos.le q)

def commonFullScoreTubeWeight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν M : ℝ) (k : ℕ) (ze : CommonSamples p) : ℝ :=
  fullScoreTubeWeight A ν M k ze.1

theorem commonFullScoreTubeWeight_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν M : ℝ) (k : ℕ) (ze : CommonSamples p) :
    0 ≤ commonFullScoreTubeWeight A ν M k ze :=
  mul_nonneg (Real.exp_nonneg _) (fullScorePolynomial_nonneg A ν k ze.1)

theorem commonFullScoreTubeWeight_integrable {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν M : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (commonFullScoreTubeWeight A ν M k)
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
  simpa only [mul_one] using
    (fullScoreTubeWeight_weighted_moment_le hp A hν hlower hM k).1.mul_prod
      (integrable_const (1 : ℝ) (μ := exponentialRectangleLaw p))

theorem commonFullScoreTubeWeight_integral_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ν M : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    (∫ ze, commonFullScoreTubeWeight A ν M k ze
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) ≤
      (Real.sqrt (dimensionLog p)) ^ k * Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) := by
  have heq : (∫ ze, commonFullScoreTubeWeight A ν M k ze
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫ z, fullScoreTubeWeight A ν M k z ∂standardGaussian p := by
    simpa only [measureReal_univ_eq_one, one_smul, commonFullScoreTubeWeight] using
      (integral_fun_fst (μ := standardGaussian p) (ν := exponentialRectangleLaw p)
        (fullScoreTubeWeight A ν M k))
  rw [heq]
  exact (fullScoreTubeWeight_weighted_moment_le hp A hν hlower hM k).2

theorem dualImageRatioWeight_integral_eq_dualFaceMoment {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (hp : 1 ≤ p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ ze, dualImageRatioWeight S s A r width (fullScorePolynomial A ν k) ze
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      width ^ q * (q.factorial : ℝ) * dualFaceMoment S s A ν r k := by
  rw [integral_dualImageRatioWeight_eq_softFaceWeight S s A r hp hν hw hlower hM
    hwidth hactive hgram k]
  unfold dualFaceMoment FaceSmoother.fullDualGaussianSoftFaceMoment fullScorePolynomial
  simp_rw [mul_comm (s.softFaceWeight _ _) _]
  ring

end

end RectangleCLT.GaussianTube
