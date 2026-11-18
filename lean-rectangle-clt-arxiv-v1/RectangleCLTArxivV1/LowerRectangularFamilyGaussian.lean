import RectangleCLTArxivV1.LowerRectangularFamilyGeometry
import RectangleCLTArxivV1.LowerWidthCalibration

/-! The Gaussian counterpart of the actual two-count observations. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem lowerFamilyCovariance_eq_gaussianGram (P : SymmetricFamilyParameters) (r m : ℕ) :
    lowerFamilyCovariance r m P.variance =
      lowerGridGaussianFactor r m P.scale (Real.sqrt P.variance)*
        (lowerGridGaussianFactor r m P.scale (Real.sqrt P.variance)).transpose := by
  rw [lowerGridGaussianFactor_gram,P.scale_sq,Real.sq_sqrt P.variance_pos.le]
  rfl

theorem lowerFamilyCovariance_factor_exists (P : SymmetricFamilyParameters) (r m : ℕ) :
    ∃ A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ,
      A*A.transpose = lowerFamilyCovariance r m P.variance := by
  rw [lowerFamilyCovariance_eq_gaussianGram P r m]
  exact lowerGridGaussianFactor_exists r m P.scale (Real.sqrt P.variance)

def lowerFamilyGaussianFactor (P : SymmetricFamilyParameters) (r m : ℕ) :
    Matrix (Fin (r*m)) (Fin (r*m)) ℝ :=
  Classical.choose (lowerFamilyCovariance_factor_exists P r m)

theorem lowerFamilyGaussianFactor_gram (P : SymmetricFamilyParameters) (r m : ℕ) :
    lowerFamilyGaussianFactor P r m*(lowerFamilyGaussianFactor P r m).transpose =
      lowerFamilyCovariance r m P.variance :=
  Classical.choose_spec (lowerFamilyCovariance_factor_exists P r m)

theorem lowerFamilyGaussianFactor_matches_covariance (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1≤n) :
    lowerFamilyGaussianFactor P r m*(lowerFamilyGaussianFactor P r m).transpose =
      covariance (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P)) := by
  rw [lowerFamilyNormalizedObservations_covariance P hn,lowerFamilyGaussianFactor_gram]

theorem lowerFamilyGaussianLaw_eq (P : SymmetricFamilyParameters) {r m : ℕ}
    (A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ)
    (hA : A*A.transpose = lowerFamilyCovariance r m P.variance) :
    lowerGridGaussianLaw r m P.scale (Real.sqrt P.variance) = gaussianLaw A := by
  apply lowerGridGaussianLaw_eq_gaussianLaw
  exact hA.trans (lowerFamilyCovariance_eq_gaussianGram P r m)

theorem lowerFamilyGaussianMaximumMean_eq (P : SymmetricFamilyParameters) {r m : ℕ}
    (A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ)
    (hA : A*A.transpose = lowerFamilyCovariance r m P.variance) :
    gaussianMaximumMean A = lowerGridGaussianMean r m P.scale (Real.sqrt P.variance) := by
  apply gaussianMaximumMean_lowerGrid
  exact hA.trans (lowerFamilyCovariance_eq_gaussianGram P r m)

theorem lowerFamilyGaussian_width_bounds (P : SymmetricFamilyParameters) {r m : ℕ}
    (hr : 1≤r) (hm : 1≤m) (A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ)
    (hA : A*A.transpose = lowerFamilyCovariance r m P.variance) :
    P.scale*independentAbsGaussianMean r ≤ gaussianMaximumMean A ∧
      gaussianMaximumMean A ≤ P.scale*independentAbsGaussianMean r+
        Real.sqrt P.variance*independentAbsGaussianMean m := by
  rw [lowerFamilyGaussianMaximumMean_eq P A hA]
  constructor
  · simpa only [abs_of_nonneg P.scale_pos.le] using
      lowerGridGaussianMean_lower hr hm P.scale (Real.sqrt P.variance)
  · simpa only [abs_of_nonneg P.scale_pos.le,abs_of_nonneg (Real.sqrt_nonneg P.variance)] using
      lowerGridGaussianMean_upper r m P.scale (Real.sqrt P.variance)

end
end RectangleCLTArxivV1
