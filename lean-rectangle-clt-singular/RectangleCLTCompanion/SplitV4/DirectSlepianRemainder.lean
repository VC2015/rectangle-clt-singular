import RectangleCLTCompanion.SplitV4.DirectSlepianFourth
import RectangleCLTCompanion.SplitV4.SlepianLaw

/-! The actual Slepian fourth remainder is bounded after its positive
coordinate weights are restored to the common full point. -/

open MeasureTheory Set
open scoped BigOperators Interval
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def directSlepianFourthFlagsA : Fin 4 → Bool := fun _ => true
def directSlepianFourthFlagsB : Fin 4 → Bool := ![false, false, true, true]
def directSlepianFourthFlagsC : Fin 4 → Bool := ![false, false, false, true]

set_option maxHeartbeats 1000000 in
theorem directSlepianFourthPathIntegrand_eq_copy_patterns
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0 1
      (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r =
    seededFourthKernel (Real.sqrt (1-v)) (-(1/2 : ℝ)) r*
      directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsA +
    ((1-v)/2*(1-r))*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsB +
    ((1-v)/4)*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsC := by
  classical
  let kA := seededFourthKernel (Real.sqrt (1-v)) (-(1/2 : ℝ)) r
  let kB := (1-v)/2*(1-r)
  let kC := (1-v)/4
  have hfun (i : Fin n) (z : (Vector p × Ω) × (Ω × Ω)) :
      genericManuscriptFourthCombination s.F
        (0+Real.sqrt v • z.1.1+Real.sqrt (1-v) •
          maskObservationSum ξ (Function.update (fun _ => true) i false) z.1.2)
        (ξ i z.2.1) (ξ i z.2.2) (Real.sqrt (1-v)) (-(1/2 : ℝ)) v r =
      kA*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsA i z+
      kB*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsB i z+
      kC*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsC i z := by
    unfold genericManuscriptFourthCombination directSlepianFourthCopyTensor directSlepianFourthPoint
    simp only [zero_add, maskObservationSum_all_true_deleted]
    have he : (1-v)/6*(1-(-(1/2 : ℝ))) = kC := by dsimp [kC]; ring
    rw [he]
    rfl
  have hdA := directSlepian_fourth_copy_data μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 directSlepianFourthFlagsA
  have hdB := directSlepian_fourth_copy_data μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 directSlepianFourthFlagsB
  have hdC := directSlepian_fourth_copy_data μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 directSlepianFourthFlagsC
  unfold genericManuscriptFourthPathIntegrand
  simp only [maskWeight_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp_rw [hfun]
  have hlin (i : Fin n) :
      (∫ z, kA*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsA i z+
        kB*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsB i z+
        kC*directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsC i z
        ∂((gaussianLaw A).prod μ).prod (μ.prod μ)) =
      kA*(∫ z, directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsA i z
        ∂((gaussianLaw A).prod μ).prod (μ.prod μ))+
      kB*(∫ z, directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsB i z
        ∂((gaussianLaw A).prod μ).prod (μ.prod μ))+
      kC*(∫ z, directSlepianFourthCopyTensor s ξ v r directSlepianFourthFlagsC i z
        ∂((gaussianLaw A).prod μ).prod (μ.prod μ)) := by
    have hAB := integral_add ((hdA.1 i).const_mul kA) ((hdB.1 i).const_mul kB)
    have hABC := integral_add (((hdA.1 i).const_mul kA).add ((hdB.1 i).const_mul kB)) ((hdC.1 i).const_mul kC)
    simp only [Pi.add_apply] at hAB hABC
    rw [hABC, hAB, integral_const_mul,
      integral_const_mul, integral_const_mul]
  simp_rw [hlin]
  unfold directSlepianCopyFourthIntegrand
  simp only [Finset.sum_add_distrib, Finset.mul_sum]
  rfl

def directInitializationRemainderConstant : ℝ := 3*directInitializationFourthConstant

theorem direct_slepian_scalar_kernel_bounds {v r : ℝ}
    (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |seededFourthKernel (Real.sqrt (1-v)) (-(1/2 : ℝ)) r| ≤ 1 ∧
      |(1-v)/2*(1-r)| ≤ 1 ∧ |(1-v)/4| ≤ 1 := by
  have hv : 0 ≤ 1-v := by linarith
  have hvr : 1-v ≤ 1 := by linarith
  have hr : 0 ≤ 1-r := by linarith
  have hrr : 1-r ≤ 1 := by linarith
  have hrsq : (1-r)^2 ≤ 1 := by nlinarith
  have hpA := mul_le_mul hvr hrsq (sq_nonneg (1-r)) zero_le_one
  have hpB := mul_le_mul hvr hrr hr zero_le_one
  rw [show (-(1/2 : ℝ)) = (-1/2 : ℝ) by ring, slepian_fourth_kernel, Real.sq_sqrt hv]
  refine ⟨?_, ?_, ?_⟩
  · rw [show -(1-v)/4*(1-r)^2 = -((1-v)*(1-r)^2)/4 by ring,
      abs_div, abs_neg, abs_of_nonneg (mul_nonneg hv (sq_nonneg _))]
    norm_num
    nlinarith
  · rw [show (1-v)/2*(1-r) = ((1-v)*(1-r))/2 by ring, abs_div,
      abs_of_nonneg (mul_nonneg hv hr)]
    norm_num
    nlinarith
  · rw [abs_div, abs_of_nonneg hv]
    norm_num
    linarith

theorem abs_directSlepianFourthPathIntegrand_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v r : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) (hr0 : 0 ≤ r) (hr1 : r ≤ 1) :
    |genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0 1
      (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r| ≤
      directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
  let M := directInitializationFourthConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3
  have hcopy (b : Fin 4 → Bool) : |directSlepianCopyFourthIntegrand s μ ξ A v r b| ≤ M :=
    abs_directSlepianCopyFourthIntegrand_le μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1 b
  have hk := direct_slepian_scalar_kernel_bounds hv0 hv1 hr0 hr1
  have hmul (a J : ℝ) (ha : |a| ≤ 1) (hJ : |J| ≤ M) : |a*J| ≤ M := by
    rw [abs_mul]
    exact (mul_le_mul ha hJ (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  rw [directSlepianFourthPathIntegrand_eq_copy_patterns μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr0 hr1]
  have hA' := hmul _ _ hk.1 (hcopy directSlepianFourthFlagsA)
  have hB' := hmul _ _ hk.2.1 (hcopy directSlepianFourthFlagsB)
  have hC' := hmul _ _ hk.2.2 (hcopy directSlepianFourthFlagsC)
  have htri := (abs_add_le
    (seededFourthKernel (Real.sqrt (1-v)) (-(1/2 : ℝ)) r*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsA +
      ((1-v)/2*(1-r))*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsB)
    (((1-v)/4)*directSlepianCopyFourthIntegrand s μ ξ A v r directSlepianFourthFlagsC)).trans
      (add_le_add_right (abs_add_le _ _) _)
  calc
    _ ≤ 3*M := by linarith
    _ = _ := by dsimp [M, directInitializationRemainderConstant]; ring

theorem abs_directSlepianFourthRemainder_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} [NeZero p]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ s₃ s₄ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hmom : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hfaces : s.faces = Finset.univ) (hband : 4*δ ≤ s.bandwidth)
    {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    |directSlepianFourthRemainder s μ ξ A v| ≤
      directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3 := by
  have hh := intervalIntegral.norm_integral_le_of_norm_le_const (a := (0 : ℝ)) (b := 1)
    (f := fun r => genericManuscriptFourthPathIntegrand μ (gaussianLaw A) s.F ξ 0 1
      (Real.sqrt (1-v)) (Real.sqrt v) (-(1/2 : ℝ)) v r)
    (C := directInitializationRemainderConstant*s₄*Real.sqrt (dimensionLog p)/s.bandwidth^3)
    (fun r hr => by
      rw [uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      simpa only [Real.norm_eq_abs] using
        abs_directSlepianFourthPathIntegrand_le μ ξ h hmom hunit A hA s hfaces hband hv0 hv1 hr.1.le hr.2)
  simpa only [Real.norm_eq_abs, sub_zero, abs_one, mul_one, directSlepianFourthRemainder] using hh

end
end RectangleCLT.Companion.SplitV4
