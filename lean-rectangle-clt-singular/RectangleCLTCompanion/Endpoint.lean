import RectangleCLT.BoundedEnvelope
import RectangleCLT.GaussianEnvelope
import Mathlib.Algebra.Order.Floor.Semiring

/-! Covariance-free endpoint smoothing by finitely many deterministic common
threshold shifts. No random radius or extra exponential moment is needed. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable def endpointBoundedConstant : ℝ := 4294967296 * (2 * Real.exp 1 + 2)
noncomputable def endpointGaussianConstant : ℝ := Real.exp (3 / 2 : ℝ) * (2 * Real.exp 1 + 2)
noncomputable def endpointConstant : ℝ := endpointBoundedConstant + endpointGaussianConstant

theorem endpointBoundedConstant_nonneg : 0 ≤ endpointBoundedConstant := by
  unfold endpointBoundedConstant
  positivity

theorem endpointGaussianConstant_nonneg : 0 ≤ endpointGaussianConstant := by
  unfold endpointGaussianConstant
  positivity

theorem endpointConstant_nonneg : 0 ≤ endpointConstant :=
  add_nonneg endpointBoundedConstant_nonneg endpointGaussianConstant_nonneg

end RectangleCLT.Companion

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

@[simp] theorem shiftOffsets_zero : s.shiftOffsets 0 = s := by
  cases s
  simp [shiftOffsets]

theorem shiftOffsets_add (a b : ℝ) :
    (s.shiftOffsets a).shiftOffsets b = s.shiftOffsets (a + b) := by
  cases s
  simp only [shiftOffsets]
  congr 1
  funext f
  ring

def offsetVariance (a : ℝ) (x : Vector p) : ℝ :=
  (s.shiftOffsets a).F x * (1 - (s.shiftOffsets a).F x)

theorem offsetVariance_nonneg (a : ℝ) (x : Vector p) : 0 ≤ s.offsetVariance a x :=
  mul_nonneg ((s.shiftOffsets a).F_pos x).le (sub_nonneg.mpr ((s.shiftOffsets a).F_le_one x))

private theorem logistic_increment {T E : ℝ} (hT : 0 ≤ T) (hE : 1 ≤ E) :
    E / (E + T) - 1 / (1 + T) ≤
      (E - 1) * (1 / (1 + T) * (1 - 1 / (1 + T))) := by
  have h1 : 0 < 1 + T := by positivity
  have h2 : 0 < E + T := by linarith
  calc
    _ = ((E - 1) * (T / (1 + T))) * (1 / (E + T)) := by field_simp; ring
    _ ≤ ((E - 1) * (T / (1 + T))) * (1 / (1 + T)) :=
      mul_le_mul_of_nonneg_left (one_div_le_one_div_of_le h1 (by linarith))
        (mul_nonneg (sub_nonneg.mpr hE) (div_nonneg hT h1.le))
    _ = _ := by field_simp

/-- One bandwidth of common threshold translation costs one smaller
envelope, up to the fixed factor `exp 1−1`. -/
theorem shiftOffsets_increment_le (a : ℝ) (x : Vector p) :
    (s.shiftOffsets (a + s.bandwidth)).F x - (s.shiftOffsets a).F x ≤
      (Real.exp 1 - 1) * s.offsetVariance a x := by
  let t := s.shiftOffsets a
  have ht : t.bandwidth = s.bandwidth := rfl
  have hE : 1 ≤ Real.exp 1 := Real.one_le_exp (by norm_num)
  have hnext : (s.shiftOffsets (a + s.bandwidth)).F x =
      Real.exp 1 / (Real.exp 1 + (t.weights x).T) := by
    rw [← s.shiftOffsets_add a s.bandwidth, t.shiftOffsets_F]
    rw [ht, show -s.bandwidth / s.bandwidth = -(1 : ℝ) by field_simp [s.bandwidth_pos.ne'],
      Real.exp_neg]
    field_simp
  rw [hnext]
  exact logistic_increment (t.weights x).T_nonneg hE

theorem shiftOffsets_F_nat_sub_le (N : ℕ) (x : Vector p) :
    (s.shiftOffsets ((N : ℝ) * s.bandwidth)).F x - s.F x ≤
      (Real.exp 1 - 1) * ∑ j ∈ Finset.range N, s.offsetVariance ((j : ℝ) * s.bandwidth) x := by
  induction N with
  | zero => simp
  | succ N ih =>
      have hh := s.shiftOffsets_increment_le ((N : ℝ) * s.bandwidth) x
      rw [Finset.sum_range_succ]
      have heq : ((N + 1 : ℕ) : ℝ) * s.bandwidth = (N : ℝ) * s.bandwidth + s.bandwidth := by
        push_cast
        ring
      rw [heq]
      nlinarith

theorem half_le_shiftOffsets_F_inside (hp : 1 ≤ p) (x : Vector p) (hx : s.Inside x) :
    1 / 2 ≤ (s.shiftOffsets ((Nat.ceil (dimensionLog p) : ℝ) * s.bandwidth)).F x := by
  have hT : (s.weights x).T ≤ 2 * (p : ℝ) := by
    calc
      _ ≤ ∑ _f : Face p, (1 : ℝ) := Finset.sum_le_sum (fun f _ => s.inside_weights_le_one x hx f)
      _ = _ := by simp [Fintype.card_prod]; ring
  have hexp : 2 * (p : ℝ) ≤ Real.exp (Nat.ceil (dimensionLog p) : ℝ) := by
    have he : 2 ≤ Real.exp (1 : ℝ) := by linarith [Real.add_one_le_exp (1 : ℝ)]
    calc
      _ ≤ Real.exp 1 * (p : ℝ) := mul_le_mul_of_nonneg_right he (Nat.cast_nonneg _)
      _ = Real.exp (dimensionLog p) := (Real.exp_log (mul_pos (Real.exp_pos _) (by exact_mod_cast hp))).symm
      _ ≤ _ := Real.exp_le_exp.mpr (Nat.le_ceil _)
  have hTs : ((s.shiftOffsets ((Nat.ceil (dimensionLog p) : ℝ) * s.bandwidth)).weights x).T ≤ 1 := by
    rw [s.shiftOffsets_T, show -((Nat.ceil (dimensionLog p) : ℝ) * s.bandwidth) /
      s.bandwidth = -(Nat.ceil (dimensionLog p) : ℝ) by field_simp [s.bandwidth_pos.ne'], Real.exp_neg]
    calc
      _ ≤ (Real.exp (Nat.ceil (dimensionLog p) : ℝ))⁻¹ *
          Real.exp (Nat.ceil (dimensionLog p) : ℝ) :=
        mul_le_mul_of_nonneg_left (hT.trans hexp) (inv_nonneg.mpr (Real.exp_nonneg _))
      _ = 1 := inv_mul_cancel₀ (Real.exp_ne_zero _)
  change 1 / 2 ≤ 1 / (1 + _)
  apply (div_le_div_iff₀ (by norm_num : (0 : ℝ) < 2)
    ((s.shiftOffsets ((Nat.ceil (dimensionLog p) : ℝ) * s.bandwidth)).weights x).denominator_pos).mpr
  linarith

theorem endpoint_error_le_offsetVariances (hp : 1 ≤ p) (x : Vector p) :
    |s.F x - s.indicator x| ≤
      (Real.exp 1 - 1) * ∑ j ∈ Finset.range (Nat.ceil (dimensionLog p)),
        s.offsetVariance ((j : ℝ) * s.bandwidth) x +
      2 * s.offsetVariance ((Nat.ceil (dimensionLog p) : ℝ) * s.bandwidth) x +
      2 * s.offsetVariance 0 x := by
  classical
  let N := Nat.ceil (dimensionLog p)
  let b := (N : ℝ) * s.bandwidth
  let f := s.F x
  let g := (s.shiftOffsets b).F x
  have htel := s.shiftOffsets_F_nat_sub_le N x
  have hC : 0 ≤ Real.exp 1 - 1 := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hsum : 0 ≤ (Real.exp 1 - 1) * ∑ j ∈ Finset.range N,
      s.offsetVariance ((j : ℝ) * s.bandwidth) x :=
    mul_nonneg hC (Finset.sum_nonneg (fun j _ => s.offsetVariance_nonneg _ _))
  have hv0 := s.offsetVariance_nonneg 0 x
  have hvb := s.offsetVariance_nonneg b x
  have hf0 : 0 ≤ f := (s.F_pos x).le
  have hf1 : f ≤ 1 := s.F_le_one x
  have hg1 : g ≤ 1 := (s.shiftOffsets b).F_le_one x
  have hv0eq : s.offsetVariance 0 x = f * (1 - f) := by simp [offsetVariance, f]
  have hvbeq : s.offsetVariance b x = g * (1 - g) := rfl
  by_cases hx : s.Inside x
  · have hgh : 1 / 2 ≤ g := s.half_le_shiftOffsets_F_inside hp x hx
    have htail : 1 - g ≤ 2 * s.offsetVariance b x := by
      rw [hvbeq]
      nlinarith [mul_nonneg (sub_nonneg.mpr hgh) (sub_nonneg.mpr hg1)]
    simp only [indicator, if_pos hx, abs_of_nonpos (sub_nonpos.mpr (s.F_le_one x))]
    change -(f - 1) ≤ _
    change g - f ≤ _ at htel
    nlinarith
  · have hfh : f < 1 / 2 := by
      have hh := s.outside_half_lt_theta x hx
      change (1 / 2 : ℝ) < 1 - f at hh
      linarith
    have htail : f ≤ 2 * s.offsetVariance 0 x := by
      rw [hv0eq]
      nlinarith [mul_nonneg hf0 (sub_nonneg.mpr hfh.le)]
    simp only [indicator, if_neg hx, sub_zero, abs_of_pos (s.F_pos x)]
    change f ≤ _
    nlinarith

theorem integrable_offsetVariance {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsFiniteMeasure μ] (W : Ω → Vector p) (hW : Measurable W) (a : ℝ) :
    Integrable (fun ω => s.offsetVariance a (W ω)) μ :=
  (s.shiftOffsets a).integrable_smallerEnvelope W hW

/-- A deterministic finite telescope converts uniform smaller-envelope
expectations into the unrestricted endpoint estimate. -/
theorem integral_endpoint_error_le_of_offsetVariance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (hp : 1 ≤ p) {K : ℝ} (hK : 0 ≤ K)
    (hvar : ∀ a : ℝ, (∫ ω, s.offsetVariance a (W ω) ∂μ) ≤ K) :
    (∫ ω, |s.F (W ω) - s.indicator (W ω)| ∂μ) ≤
      (2 * (Real.exp 1 - 1) + 4) * dimensionLog p * K := by
  let N := Nat.ceil (dimensionLog p)
  let b := (N : ℝ) * s.bandwidth
  let C := Real.exp 1 - 1
  have hC : 0 ≤ C := sub_nonneg.mpr (Real.one_le_exp (by norm_num))
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hN : (N : ℝ) ≤ 2 * dimensionLog p := Nat.ceil_le_two_mul (by
    have hh : (1 / 2 : ℝ) ≤ dimensionLog p := (by norm_num : (1 / 2 : ℝ) ≤ 1).trans hL
    simpa only [one_div] using hh)
  have hi := integrable_finset_sum (Finset.range N)
    (fun j _ => s.integrable_offsetVariance W hW ((j : ℝ) * s.bandwidth) (μ := μ))
  have hib := s.integrable_offsetVariance W hW b (μ := μ)
  have hi0 := s.integrable_offsetVariance W hW 0 (μ := μ)
  have hb := integral_mono_of_nonneg (ae_of_all μ (fun ω => abs_nonneg (s.F (W ω) - s.indicator (W ω))))
    (((hi.const_mul C).add (hib.const_mul 2)).add (hi0.const_mul 2))
    (ae_of_all μ (fun ω => s.endpoint_error_le_offsetVariances hp (W ω)))
  have hsum₁ := integral_add ((hi.const_mul C).add (hib.const_mul 2)) (hi0.const_mul 2)
  have hsum₂ := integral_add (hi.const_mul C) (hib.const_mul 2)
  simp only [Pi.add_apply] at hb hsum₁ hsum₂
  rw [hsum₁, hsum₂] at hb
  simp only [integral_const_mul] at hb
  rw [integral_finset_sum (Finset.range N)
    (fun j _ => s.integrable_offsetVariance W hW ((j : ℝ) * s.bandwidth) (μ := μ))] at hb
  have hs : (∑ j ∈ Finset.range N, ∫ ω, s.offsetVariance ((j : ℝ) * s.bandwidth) (W ω) ∂μ) ≤
      (N : ℝ) * K := by
    exact (Finset.sum_le_sum (s := Finset.range N)
      (fun j _ => hvar ((j : ℝ) * s.bandwidth))).trans_eq (by simp)
  have hh := add_le_add (add_le_add (mul_le_mul_of_nonneg_left hs hC)
    (mul_le_mul_of_nonneg_left (hvar b) (by norm_num : (0 : ℝ) ≤ 2)))
      (mul_le_mul_of_nonneg_left (hvar 0) (by norm_num : (0 : ℝ) ≤ 2))
  apply hb.trans (hh.trans _)
  have hn := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hN hC) hK
  have hkL := mul_le_mul_of_nonneg_right hL hK
  dsimp only [C] at *
  nlinarith

/-- Actual endpoint smoothing for independent bounded observations. Only
the coordinate variances are normalized; the full covariance may be singular. -/
theorem bounded_endpoint_error_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (hδh : δ ≤ s.bandwidth) (r : Vector p) :
    (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) ≤
      Companion.endpointBoundedConstant * s.bandwidth * Real.sqrt (dimensionLog p) * dimensionLog p := by
  let K := 4294967296 * s.bandwidth * Real.sqrt (dimensionLog p)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (by norm_num) s.bandwidth_pos.le) (Real.sqrt_nonneg _)
  have hvar (a : ℝ) : (∫ ω, s.offsetVariance a (sumVector ξ ω + r) ∂μ) ≤ K := by
    have hh := h.integral_smallerEnvelope_le hp (by norm_num : (0 : ℝ) < 1)
      hunit (s.shiftOffsets a) r
    simp only [div_one] at hh
    change (∫ ω, s.offsetVariance a (sumVector ξ ω + r) ∂μ) ≤
      2147483648 * (s.bandwidth + δ) * Real.sqrt (dimensionLog p) at hh
    apply hh.trans
    exact mul_le_mul_of_nonneg_right (by nlinarith) (Real.sqrt_nonneg _)
  have hh := s.integral_endpoint_error_le_of_offsetVariance μ (fun ω => sumVector ξ ω + r)
    (h.measurable_sum.add_const r) hp hK hvar
  convert hh using 1
  dsimp only [Companion.endpointBoundedConstant, K]
  ring

/-- Actual Gaussian endpoint smoothing with arbitrary singular covariance
and normalized marginal variances. No concentration limit is used. -/
theorem gaussian_endpoint_error_le (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (r : Vector p) :
    (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      Companion.endpointGaussianConstant * s.bandwidth * Real.sqrt (dimensionLog p) * dimensionLog p := by
  let K := Real.exp (3 / 2 : ℝ) * s.bandwidth * Real.sqrt (dimensionLog p)
  have hK : 0 ≤ K := mul_nonneg (mul_nonneg (Real.exp_nonneg _) s.bandwidth_pos.le) (Real.sqrt_nonneg _)
  have hvar (a : ℝ) : (∫ x : Vector p, s.offsetVariance a (x + r) ∂gaussianLaw A) ≤ K := by
    have hh := gaussian_expected_variance_le_of_diagonal hp (s.shiftOffsets a) A
      (by norm_num : (0 : ℝ) < 1) hdiag r
    simpa only [div_one] using hh
  have hh := s.integral_endpoint_error_le_of_offsetVariance (gaussianLaw A) (fun x => x + r)
    (measurable_id.add_const r) hp hK hvar
  convert hh using 1
  dsimp only [Companion.endpointGaussianConstant, K]
  ring

theorem bounded_gaussian_endpoint_error_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {n : ℕ} {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hδh : δ ≤ s.bandwidth) (r : Vector p) :
    (∫ ω, |s.F (sumVector ξ ω + r) - s.indicator (sumVector ξ ω + r)| ∂μ) +
      (∫ x : Vector p, |s.F (x + r) - s.indicator (x + r)| ∂gaussianLaw A) ≤
      Companion.endpointConstant * s.bandwidth * Real.sqrt (dimensionLog p) * dimensionLog p := by
  exact (add_le_add (s.bounded_endpoint_error_le h hp hunit hδh r)
    (s.gaussian_endpoint_error_le hp A hdiag r)).trans_eq (by
      unfold Companion.endpointConstant
      ring)

end
end RectangleCLT.FaceSmoother
