import RectangleCLTCompanion.SplitV4.SymmetricFamilyPolynomial
import RectangleCLTCompanion.SplitV4.SymmetricBoundedParameters

/-! Actual polynomial moment budgets from the explicit sparse-family parameter bounds. -/
open MeasureTheory ProbabilityTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem family_polynomialIndependent_of_rare_parameters (P : SymmetricFamilyParameters)
    {n m : ℕ} (hn : 1 ≤ n) {q B : ℝ} (hq : 2 < q) (hB : 2 ≤ B)
    (hEnvelope : P.amplitude*P.theta^(1/q) ≤ B/2)
    (hFourth : P.theta*P.pi*P.amplitude^4 ≤ B^2/16) :
    PolynomialIndependentHypotheses (familyArrayLaw P n m) (familyRawObservations P) q B := by
  apply symmetricFamily_polynomialIndependent P hn (by linarith : 1 ≤ q)
  · have hs := familyScale_le_one P
    linarith
  · have hv := P.variance_lt_half
    change P.variance < 1/2 at hv
    nlinarith only [hv, hB, hFourth, sq_nonneg P.variance, sq_nonneg (B-2)]

end
end RectangleCLT.Companion.SplitV4
