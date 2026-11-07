import RectangleCLTCompanion.SplitV4.SymmetricPolynomialUniform

/-! Literal polynomial sparse rate and its actual-model uniform upper bound. -/
open MeasureTheory
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def polynomialSparseParameter (n p : ℕ) (B q : ℝ) : ℝ := B*((n : ℝ)/dimensionLog p)^(2/q-1/2)
def polynomialSparseRate (n p : ℕ) (B q : ℝ) : ℝ :=
  B*dimensionLog p^(3/2-1/q)/((n : ℝ)^(1/2-1/q)*
    Real.log (Real.exp 1+polynomialSparseParameter n p B q)^(1-1/q))
def polynomialCoordinateRate (n p : ℕ) (B : ℝ) : ℝ :=
  B^(1/2 : ℝ)*dimensionLog p^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)

theorem polynomialBennettObservationRate_eq_sparse (n p : ℕ) (B q : ℝ) :
    polynomialBennettObservationRate n p B q = polynomialCoordinateRate n p B+polynomialSparseRate n p B q := rfl

theorem polynomialWorstDistance_sparse_le {n p : ℕ} {B q : ℝ}
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hq : 2 < q) (hB : 1 ≤ B)
    (hCoordinate : polynomialCoordinateRate n p B ≤ polynomialSparseRate n p B q) :
    polynomialWorstDistance.{0} q B p n ≤ 2*polynomialUniversalConstant q*polynomialSparseRate n p B q := by
  have hC : 0 ≤ polynomialUniversalConstant q := zero_le_one.trans (one_le_polynomialUniversalConstant q)
  have hh := polynomialMomentWorstDistanceCLT.{0} hp hn hq hB
  have hRate := (min_le_right (1 : ℝ) (polynomialCombinedRate n p B q)).trans
    (min_le_left (polynomialBennettObservationRate n p B q) (polynomialEnvelopeTransferRate n p B q))
  have hBennett := hh.trans (mul_le_mul_of_nonneg_left hRate hC)
  rw [polynomialBennettObservationRate_eq_sparse] at hBennett
  have hFinal := mul_le_mul_of_nonneg_left (add_le_add_right hCoordinate (polynomialSparseRate n p B q)) hC
  exact hBennett.trans (hFinal.trans_eq (by ring))

end
end RectangleCLT.Companion.SplitV4
