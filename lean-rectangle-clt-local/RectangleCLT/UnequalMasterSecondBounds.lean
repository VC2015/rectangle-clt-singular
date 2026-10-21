import RectangleCLT.GlobalSecondAverage
import RectangleCLT.UnequalMasterStatement

/-! All three actual quadratic alternatives in the unequal-covariance
master estimate, retaining the omitted-zero global convention. -/

open MeasureTheory

namespace RectangleCLT

noncomputable section

def unequalSecondIntegralConstant : ℝ :=
  1 + globalSecondTimeConstant + FaceSmoother.proxySecondConstant +
    3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)

theorem unequalSecondIntegralConstant_pos : 0 < unequalSecondIntegralConstant := by
  have hK : 0 ≤ 3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant) := by
    unfold interpolationShortScaleConstant
    positivity
  unfold unequalSecondIntegralConstant
  linarith [globalSecondTimeConstant_pos, FaceSmoother.proxySecondConstant_pos]

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem selectorSecondAbsoluteSum_time_le_unequal_min
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hc : 0 < pairGap (A * A.transpose)) (hband : 12 * δ ≤ s.bandwidth)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤
      unequalSecondIntegralConstant * Real.sqrt (dimensionLog p) *
        masterSecondCoefficient (dimensionLog p) (fullCovarianceScale (A * A.transpose))
          (pairGap (A * A.transpose)) s.bandwidth / Real.sqrt t := by
  let Q := A * A.transpose
  let L := dimensionLog p
  let C := unequalSecondIntegralConstant
  let K := 3 * (75 * (Real.exp 2) ^ 5 * interpolationShortScaleConstant)
  let D := C * Real.sqrt L / Real.sqrt t
  have hC : 0 ≤ C := unequalSecondIntegralConstant_pos.le
  have hK : 0 ≤ K := by dsimp [K]; unfold interpolationShortScaleConstant; positivity
  dsimp only [K] at hK
  have hL : 0 ≤ L := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hsL : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL
  have hrt : 0 < Real.sqrt t := Real.sqrt_pos.mpr ht
  have hrt1 : Real.sqrt t ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht1.le
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hKC : K ≤ C := by
    dsimp [K, C, unequalSecondIntegralConstant]
    linarith [globalSecondTimeConstant_pos, proxySecondConstant_pos]
  have hPC : proxySecondConstant ≤ C := by
    dsimp [C, unequalSecondIntegralConstant]
    linarith [globalSecondTimeConstant_pos, hK]
  have hGC : globalSecondTimeConstant ≤ C := by
    dsimp [C, unequalSecondIntegralConstant]
    linarith [proxySecondConstant_pos, hK]
  have hshort : s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤ D * (1 / s.bandwidth) := by
    have hh := s.selectorSecondAbsoluteSum_shortScale_le_proxy μ ξ hdata hp hunit
      A hdiag hband ht.le ht1.le
    have hnum : K * Real.sqrt L / s.bandwidth ≤ C * Real.sqrt L / s.bandwidth :=
      div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hKC (Real.sqrt_nonneg L)) s.bandwidth_pos.le
    have hpos : 0 ≤ C * Real.sqrt L / s.bandwidth :=
      div_nonneg (mul_nonneg hC (Real.sqrt_nonneg L)) s.bandwidth_pos.le
    have htime : C * Real.sqrt L / s.bandwidth ≤
        (C * Real.sqrt L / s.bandwidth) / Real.sqrt t := by
      apply (le_div_iff₀ hrt).mpr
      exact mul_le_of_le_one_right hpos hrt1
    exact hh.trans ((hnum.trans htime).trans_eq (by dsimp [D]; ring))
  have hpair : s.selectorSecondAbsoluteSum (gaussianLaw (Real.sqrt t • A)) μ ξ 0
      (thinningProbability t) (thinningScale t) ≤ D * (Real.sqrt L / pairGap Q) := by
    have hh := s.selectorSecondAbsoluteSum_time_le_proxy μ ξ hdata hp hunit
      A hdiag hc hband ht ht1
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hPC hL)
      (mul_nonneg hc.le hrt.le)
    apply hh.trans (hm.trans_eq ?_)
    change C * L / (pairGap Q * Real.sqrt t) = D * (Real.sqrt L / pairGap Q)
    calc
      _ = C * (Real.sqrt L) ^ 2 / (pairGap Q * Real.sqrt t) := by rw [hsL]
      _ = _ := by dsimp [D]; ring
  change _ ≤ C * Real.sqrt L *
    masterSecondCoefficient L (fullCovarianceScale Q) (pairGap Q) s.bandwidth / Real.sqrt t
  rw [mul_div_right_comm]
  change _ ≤ D * masterSecondCoefficient L (fullCovarianceScale Q) (pairGap Q) s.bandwidth
  unfold masterSecondCoefficient
  apply le_mul_optionalMin hD
  · rw [mul_min_of_nonneg _ _ hD]
    exact le_min hpair hshort
  · intro hb
    have hν : 0 < fullEigenvalue Q := Real.sqrt_pos.mp hb
    have hPSD : Q.PosSemidef := by
      simpa only [Q, Matrix.conjTranspose_eq_transpose_of_trivial] using
        Matrix.posSemidef_self_mul_conjTranspose A
    have hh := s.selectorSecondAbsoluteSum_time_le_full_eigenvalue μ ξ hdata hp hunit
      A hdiag hν (fullEigenvalue_lower hPSD) hband ht ht1
    have hm := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hGC hL)
      (mul_nonneg (Real.sqrt_nonneg (fullEigenvalue Q)) hrt.le)
    apply hh.trans (hm.trans_eq ?_)
    change C * L / (fullCovarianceScale Q * Real.sqrt t) =
      D * (Real.sqrt L / fullCovarianceScale Q)
    calc
      _ = C * (Real.sqrt L) ^ 2 / (fullCovarianceScale Q * Real.sqrt t) := by rw [hsL]
      _ = _ := by dsimp [D]; ring

end FaceSmoother

end

end RectangleCLT
