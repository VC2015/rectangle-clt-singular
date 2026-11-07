import RectangleCLTCompanion.SplitV4.LogisticDerivativeEnvelope
import RectangleCLTCompanion.SplitV4.DerivativeEnvelopeStability

/-! The all-order canonical bound in the paper's actual face coordinates. -/
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def scaledFaceLinearMaps {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (h : ℝ)
    (j : Fin m) : Vector r →L[ℝ] ℝ :=
  h⁻¹ • (faceDotLinear (U j)).toContinuousLinearMap

theorem scaledFaceLinearMaps_apply {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ) (h : ℝ)
    (j : Fin m) (x : Vector r) : scaledFaceLinearMaps U h j x = faceDot (U j) x/h := by
  change h⁻¹*faceDot (U j) x = faceDot (U j) x/h
  ring

theorem linearLogistic_scaledFaces {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    (a : Vector m) (h : ℝ) :
    linearLogistic (scaledFaceLinearMaps U h) (fun j => -a j/h) = logisticNullWeight U a h := by
  funext x
  unfold linearLogistic linearExpTotal reciprocalOnePlus logisticNullWeight
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  rw [scaledFaceLinearMaps_apply]
  congr 1
  ring

theorem linearFaceNorm_scaledFaces {m r : ℕ} (U : Matrix (Fin m) (Fin r) ℝ)
    {h : ℝ} (hh : 0 < h) (z : Vector r) :
    linearFaceNorm (scaledFaceLinearMaps U h) z = faceProjectionNorm U z/h := by
  have he : (fun j => scaledFaceLinearMaps U h j z) = h⁻¹ • U.mulVec z := by
    funext j
    rw [scaledFaceLinearMaps_apply]
    simp only [Pi.smul_apply,smul_eq_mul,Matrix.mulVec,faceDot,dotProduct]
    ring
  rw [linearFaceNorm,he,norm_smul,Real.norm_eq_abs,abs_inv,abs_of_pos hh]
  simp only [faceProjectionNorm,div_eq_mul_inv,mul_comm]

theorem abs_iteratedFDeriv_logisticNullWeight_le {m r q : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (hq : 1 ≤ q) (x : Vector r) (z : Fin q → Vector r) :
    |iteratedFDeriv ℝ q (logisticNullWeight U a h) x z| ≤
      (logisticDerivativePartitionConstant q/h^q)*logisticNullWeight U a h x*
        (1-logisticNullWeight U a h x)*∏ i, faceProjectionNorm U (z i) := by
  have hb := abs_iteratedFDeriv_linearLogistic_le (scaledFaceLinearMaps U h) (fun j => -a j/h) hq x z
  rw [linearLogistic_scaledFaces] at hb
  simp_rw [linearFaceNorm_scaledFaces U hh] at hb
  rw [Finset.prod_div_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin] at hb
  convert hb using 1 <;> ring

def allOrderLogisticEnvelopeConstant (q : ℕ) : ℝ := Real.exp 3*logisticDerivativePartitionConstant q

theorem allOrderLogisticEnvelopeConstant_nonneg (q : ℕ) :
    0 ≤ allOrderLogisticEnvelopeConstant q :=
  mul_nonneg (Real.exp_nonneg _) (logisticDerivativePartitionConstant_nonneg q)

theorem abs_iteratedFDeriv_logisticNullWeight_shift_le {m r q : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {h : ℝ} (hh : 0 < h)
    (hq : 1 ≤ q) (x : Vector r) (z : Fin q → Vector r) {v : Vector r}
    (hv : faceProjectionNorm U v ≤ h) :
    |iteratedFDeriv ℝ q (logisticNullWeight U a h) (x+v) z| ≤
      (allOrderLogisticEnvelopeConstant q/h^q)*logisticNullWeight U a h x*
        (1-logisticNullWeight U a h x)*∏ i, faceProjectionNorm U (z i) := by
  have hb := abs_iteratedFDeriv_logisticNullWeight_le U a hh hq (x+v) z
  have hs := logistic_smallerEnvelope_shift_le U a hh x hv
  have hK : 0 ≤ logisticDerivativePartitionConstant q/h^q :=
    div_nonneg (logisticDerivativePartitionConstant_nonneg q) (pow_nonneg hh.le q)
  have hP : 0 ≤ ∏ i, faceProjectionNorm U (z i) :=
    Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hm := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hs hK) hP
  apply hb.trans
  convert hm using 1 <;> dsimp [allOrderLogisticEnvelopeConstant] <;> ring

end
end RectangleCLT.Companion.SplitV4
