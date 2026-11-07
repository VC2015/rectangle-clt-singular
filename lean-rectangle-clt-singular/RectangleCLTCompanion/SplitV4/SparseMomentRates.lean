import RectangleCLTCompanion.SplitV4.SparseUniformBounds
import RectangleCLTCompanion.SplitV4.SparseFamily
import RectangleCLTCompanion.SplitV4.SymmetricBoundedLower

/-! Literal paper dimension, sparse parameter and sparse rate in p=m². -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseMomentK (n m : ℕ) (q B : ℝ) : ℝ := polynomialSparseParameter n (m*m) B q
def sparseMomentLowerRate (n m : ℕ) (q B : ℝ) : ℝ := polynomialSparseRate n (m*m) B q

theorem sparseMomentK_eq (n m : ℕ) (hm : 2 ≤ m) (q B : ℝ) :
    sparseMomentK n m q B = sparseLowerK n (Real.log (m : ℝ)) q B := by
  rw [sparseMomentK, polynomialSparseParameter, dimensionLog_square m (by omega), sparseLowerK]

theorem sparseMomentLowerRate_eq (n m : ℕ) (hm : 2 ≤ m) (q B : ℝ) :
    sparseMomentLowerRate n m q B = sparseLowerRate n (Real.log (m : ℝ)) q B := by
  rw [sparseMomentLowerRate, polynomialSparseRate, polynomialSparseParameter,
    dimensionLog_square m (by omega), sparseLowerRate, sparseLowerK]

theorem sparseMomentK_pos {n m : ℕ} {q B : ℝ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hB : 2 ≤ B) :
    0 < sparseMomentK n m q B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog (m*m) := by
    rw [dimensionLog_square m (by omega)]
    have hl := Real.log_pos (show (1 : ℝ) < m by exact_mod_cast hm)
    linarith
  unfold sparseMomentK polynomialSparseParameter
  exact mul_pos (by linarith) (Real.rpow_pos_of_pos (div_pos hN hL) _)

theorem sparseMomentLowerRate_pos {n m : ℕ} {q B : ℝ} (hn : 1 ≤ n) (hm : 2 ≤ m) (hB : 2 ≤ B) :
    0 < sparseMomentLowerRate n m q B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog (m*m) := by
    rw [dimensionLog_square m (by omega)]
    have hl := Real.log_pos (show (1 : ℝ) < m by exact_mod_cast hm)
    linarith
  have hK := sparseMomentK_pos (q := q) hn hm hB
  have hlog : 0 < Real.log (Real.exp 1+sparseMomentK n m q B) := Real.log_pos (by
    have he : (1 : ℝ) < Real.exp 1 := Real.one_lt_exp_iff.mpr (by norm_num)
    linarith)
  unfold sparseMomentLowerRate polynomialSparseRate
  exact div_pos (mul_pos (by linarith) (Real.rpow_pos_of_pos hL _))
    (mul_pos (Real.rpow_pos_of_pos hN _) (Real.rpow_pos_of_pos hlog _))

end
end RectangleCLT.Companion.SplitV4
