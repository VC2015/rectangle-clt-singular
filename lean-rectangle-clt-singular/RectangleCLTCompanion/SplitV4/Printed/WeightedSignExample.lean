import RectangleCLTCompanion.SplitV4.Printed.ObservationRates
import RectangleCLTCompanion.SplitV4.RelativeMain

/-! The centered sign-vector example at frozen manuscript lines 182--184.
No independence among the coordinates of a sign vector is imposed. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem relativeRate_le_of_fourth_cost {δ s₄ L C : ℝ} (hδ : 0≤δ) (hL : 0≤L) (hC : 0≤C)
    (hcost : s₄*D_L δ L≤C*δ^2) :
    relativeRate δ s₄ L≤(1+Real.sqrt C)*δ*L^(3/2:ℝ) := by
  have hs := Real.sqrt_le_sqrt hcost
  rw [Real.sqrt_mul hC,Real.sqrt_sq_eq_abs,abs_of_nonneg hδ] at hs
  have hm := mul_le_mul_of_nonneg_left hs (Real.rpow_nonneg hL (3/2:ℝ))
  unfold relativeRate
  nlinarith only [hm]

theorem relativeRate_smoothing_lower {δ s₄ L : ℝ} (hL : 0≤L) :
    δ*L^(3/2:ℝ)≤relativeRate δ s₄ L := by
  unfold relativeRate
  nlinarith only [mul_nonneg (Real.rpow_nonneg hL (3/2:ℝ)) (Real.sqrt_nonneg (s₄*D_L δ L))]

def weightedSignRows {Ω : Type*} {n p : ℕ} (a : Fin n → ℝ)
    (R : Fin n → Ω → Vector p) : Fin n → Ω → Vector p := fun i ω => a i • R i ω

theorem weighted_sign_bounded {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    {μ : Measure Ω} {R : Fin n → Ω → Vector p}
    (hR : BoundedIndependentHypotheses μ R 1) (a : Fin n → ℝ)
    {δ : ℝ} (hδ : 0≤δ) (ha : ∀i,|a i|≤δ) :
    BoundedIndependentHypotheses μ (weightedSignRows a R) δ := by
  refine ⟨fun i => measurable_const.smul (hR.measurable i),?_,?_,?_,hδ⟩
  · exact hR.independent.comp (fun i x => a i • x) (fun i => measurable_const.smul measurable_id)
  · intro i j
    simp only [weightedSignRows,Pi.smul_apply,smul_eq_mul,integral_const_mul,hR.centered,mul_zero]
  · intro i
    filter_upwards [hR.bounded i] with ω hω
    simpa only [weightedSignRows,norm_smul,Real.norm_eq_abs,mul_one] using
      (mul_le_mul_of_nonneg_left hω (abs_nonneg (a i))).trans (by simpa using ha i)

theorem weighted_sign_second_moment {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    {μ : Measure Ω} {R : Fin n → Ω → Vector p}
    (hc : ∀i j,(∫ω,R i ω j ∂μ)=0)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀i,covariance μ (R i)=S)
    (a : Fin n → ℝ) (i : Fin n) (j k : Fin p) :
    (∫ω,weightedSignRows a R i ω j*weightedSignRows a R i ω k ∂μ)=(a i)^2*S j k := by
  have he : (∫ω,R i ω j*R i ω k ∂μ)=S j k := by
    have hh := congrArg (fun A => A j k) (hS i)
    simpa only [covariance,hc,mul_zero,sub_zero] using hh
  have hf : (fun ω => weightedSignRows a R i ω j*weightedSignRows a R i ω k)=
      (fun ω => (a i)^2*(R i ω j*R i ω k)) := by funext ω; simp only [weightedSignRows,Pi.smul_apply,smul_eq_mul]; ring
  rw [hf,integral_const_mul,he]

/-- Both genuine fourth-moment matrices, including the independent-copy
matrix, are exactly `(sum a_i^4) S` for centered sign-vector copies. -/
theorem weighted_sign_fourth_matrices {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Fin n → Ω → Vector p}
    (hc : ∀i j,(∫ω,R i ω j ∂μ)=0)
    (hsign : ∀i j,∀ᵐ ω ∂μ,(R i ω j)^2=1)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀i,covariance μ (R i)=S)
    (a : Fin n → ℝ) (j : Fin p) :
    relativeFourthMatrix μ (weightedSignRows a R) j=(∑i,(a i)^4)•S ∧
    relativeFreshFourthMatrix μ (weightedSignRows a R) j=(∑i,(a i)^4)•S := by
  have hs (i : Fin n) : (∫ω,weightedSignRows a R i ω j^2 ∂μ)=(a i)^2 := by
    have he : (fun ω => weightedSignRows a R i ω j^2)=ᵐ[μ] (fun _ => (a i)^2) := by
      filter_upwards [hsign i j] with ω hω
      simp only [weightedSignRows,Pi.smul_apply,smul_eq_mul,mul_pow,hω,mul_one]
    rw [integral_congr_ae he]
    simp
  constructor
  · ext k l
    simp only [relativeFourthMatrix,restorationCoefficient,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have he : (fun ω => weightedSignRows a R i ω j^2*
        (weightedSignRows a R i ω k*weightedSignRows a R i ω l))=ᵐ[μ]
        (fun ω => (a i)^4*(R i ω k*R i ω l)) := by
      filter_upwards [hsign i j] with ω hω
      simp only [weightedSignRows,Pi.smul_apply,smul_eq_mul,mul_pow,hω]
      ring
    rw [integral_congr_ae he,integral_const_mul]
    have hh := congrArg (fun A => A k l) (hS i)
    have hh' : (∫ω,R i ω k*R i ω l ∂μ)=S k l := by
      simpa only [covariance,hc,mul_zero,sub_zero] using hh
    rw [hh']
  · ext k l
    simp only [relativeFreshFourthMatrix,Matrix.smul_apply,smul_eq_mul,Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hs,weighted_sign_second_moment hc S hS]
    ring

theorem weighted_sign_sum_covariance {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Fin n → Ω → Vector p}
    (hR : BoundedIndependentHypotheses μ R 1)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀i,covariance μ (R i)=S)
    (a : Fin n → ℝ) (ha2 : ∑i,(a i)^2=1) :
    covariance μ (sumVector (weightedSignRows a R))=S := by
  let δ := ∑i,|a i|
  have hδ : 0≤δ := Finset.sum_nonneg (fun i _ => abs_nonneg (a i))
  have ha : ∀i,|a i|≤δ := fun i => Finset.single_le_sum (fun j _ => abs_nonneg (a j)) (Finset.mem_univ i)
  have hw := weighted_sign_bounded hR a hδ ha
  ext j k
  rw [hw.covariance_sum]
  simp_rw [weighted_sign_second_moment hR.centered S hS]
  rw [←Finset.sum_mul,ha2,one_mul]

theorem weighted_sign_current_relative_bound {Ω : Type*} [MeasurableSpace Ω] {n p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {R : Fin n → Ω → Vector p}
    (hR : BoundedIndependentHypotheses μ R 1)
    (hsign : ∀i j,∀ᵐ ω ∂μ,(R i ω j)^2=1)
    (S : Matrix (Fin p) (Fin p) ℝ) (hS : ∀i,covariance μ (R i)=S)
    (hn : 1≤n) (hp : 1≤p) (a : Fin n → ℝ) (ha2 : ∑i,(a i)^2=1)
    {δ : ℝ} (hδ : 0≤δ) (ha : ∀i,|a i|≤δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=S) :
    rectangleDistance μ (sumVector (weightedSignRows a R)) A≤relativeUniversalConstant*
      min 1 (relativeRate δ (∑i,(a i)^4) (dimensionLog p)) := by
  have hw := weighted_sign_bounded hR a hδ ha
  have hcov := weighted_sign_sum_covariance hR S hS a ha2
  have hunit : ∀j,covariance μ (sumVector (weightedSignRows a R)) j j=1 := by
    intro j
    rw [hcov,←hS ⟨0,by omega⟩]
    simp only [covariance,hR.centered,mul_zero,sub_zero]
    have he : (fun ω => R ⟨0,by omega⟩ ω j*R ⟨0,by omega⟩ ω j)=ᵐ[μ] (fun _ => (1:ℝ)) := by
      filter_upwards [hsign ⟨0,by omega⟩ j] with ω hω
      simpa only [pow_two] using hω
    rw [integral_congr_ae he]
    simp
  apply relativeFourthMomentCLT μ hp _ hw hunit (Finset.sum_nonneg (fun i _ => by positivity))
  · intro j
    rw [(weighted_sign_fourth_matrices hR.centered hsign S hS a j).1,hcov]
    exact fun _ => le_rfl
  · intro j
    rw [(weighted_sign_fourth_matrices hR.centered hsign S hS a j).2,hcov]
    exact fun _ => le_rfl
  · rw [hcov]
    exact hA

def exceptionalSignDenominator (n : ℕ) : ℝ := Real.log (n : ℝ)+(n : ℝ)-1
def exceptionalSignWeight (n : ℕ) (i : Fin n) : ℝ :=
  if i.val=0 then Real.sqrt (Real.log (n : ℝ))/Real.sqrt (exceptionalSignDenominator n)
  else 1/Real.sqrt (exceptionalSignDenominator n)
def exceptionalSignEnvelope (n : ℕ) : ℝ := Real.sqrt (Real.log (n : ℝ))/Real.sqrt (exceptionalSignDenominator n)
def exceptionalSignFourth (n : ℕ) : ℝ :=
  ((Real.log (n : ℝ))^2+(n : ℝ)-1)/(exceptionalSignDenominator n)^2

theorem exceptional_denominator_pos {n : ℕ} (hn : 2≤n) : 0<exceptionalSignDenominator n := by
  have hN : (1:ℝ)<n := by exact_mod_cast hn
  have hlog : 0<Real.log (n : ℝ) := Real.log_pos hN
  unfold exceptionalSignDenominator
  linarith

theorem exceptional_fourth_nonneg {n : ℕ} (hn : 1≤n) : 0≤exceptionalSignFourth n := by
  have hN : (1:ℝ)≤n := by exact_mod_cast hn
  unfold exceptionalSignFourth
  exact div_nonneg (by nlinarith [sq_nonneg (Real.log (n : ℝ))]) (sq_nonneg _)

theorem exceptional_weight_power_sum {n : ℕ} (hn : 1≤n) (k : ℕ) :
    (∑i : Fin n,(exceptionalSignWeight n i)^k)=
      (Real.sqrt (Real.log (n : ℝ))/Real.sqrt (exceptionalSignDenominator n))^k+
      ((n : ℝ)-1)*(1/Real.sqrt (exceptionalSignDenominator n))^k := by
  cases n with
  | zero => omega
  | succ n => simp [Fin.sum_univ_succ,exceptionalSignWeight,Nat.cast_add,Nat.cast_one]

theorem exceptional_weight_normalization {n : ℕ} (hn : 2≤n) :
    (∑i : Fin n,(exceptionalSignWeight n i)^2)=1 ∧
    (∑i : Fin n,(exceptionalSignWeight n i)^4)=exceptionalSignFourth n := by
  have hln : 0<Real.log (n : ℝ) := Real.log_pos (by exact_mod_cast hn)
  have hN : (1:ℝ)<n := by exact_mod_cast hn
  have hden : 0<exceptionalSignDenominator n := by unfold exceptionalSignDenominator; linarith
  constructor
  · rw [exceptional_weight_power_sum (by omega) 2,div_pow,div_pow,
      Real.sq_sqrt hln.le,Real.sq_sqrt hden.le,one_pow]
    unfold exceptionalSignDenominator at hden ⊢
    field_simp [hden.ne']
    <;> ring
  · rw [exceptional_weight_power_sum (by omega) 4,div_pow,div_pow,one_pow]
    have hs4 (x : ℝ) (hx : 0≤x) : (Real.sqrt x)^4=x^2 := by
      rw [show (4:ℕ)=2*2 by norm_num,pow_mul,Real.sq_sqrt hx]
    rw [hs4 _ hln.le,hs4 _ hden.le]
    unfold exceptionalSignFourth
    ring

theorem exceptional_weight_envelope {n : ℕ} (hn : 2≤n) (hlog : 1≤Real.log (n : ℝ)) :
    0<exceptionalSignEnvelope n ∧ ∀i : Fin n,|exceptionalSignWeight n i|≤exceptionalSignEnvelope n := by
  have hln : 0<Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hN : (1:ℝ)<n := by exact_mod_cast hn
  have hden : 0<exceptionalSignDenominator n := by unfold exceptionalSignDenominator; linarith
  refine ⟨div_pos (Real.sqrt_pos.mpr hln) (Real.sqrt_pos.mpr hden),?_⟩
  intro i
  unfold exceptionalSignWeight exceptionalSignEnvelope
  split_ifs
  · rw [abs_of_pos (div_pos (Real.sqrt_pos.mpr hln) (Real.sqrt_pos.mpr hden))]
  · rw [abs_of_pos (one_div_pos.mpr (Real.sqrt_pos.mpr hden))]
    exact div_le_div_of_nonneg_right (Real.one_le_sqrt.mpr hlog) (Real.sqrt_nonneg _)

end
end RectangleCLT.Companion.SplitV4.Printed
