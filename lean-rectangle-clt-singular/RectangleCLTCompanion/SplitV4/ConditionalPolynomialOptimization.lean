import RectangleCLTCompanion.SplitV4.ConditionalPolynomial

/-! Optimizing the actual conditional-truncation threshold to obtain
Proposition 2, with the paper's envelope rate and logarithmic exponent. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def polynomialEnvelopeTransferRate (n p : ℕ) (B q : ℝ) : ℝ :=
  polynomialEnvelopeV n p B q * dimensionLog n ^ (1 / 2 - 1 / q)

def polynomialTruncationThreshold (n p : ℕ) (B q : ℝ) : ℝ :=
  2 * B * ((n : ℝ) / (dimensionLog p * dimensionLog n)) ^ (1 / q)

theorem polynomialEnvelopeTransferRate_eq_ratio {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B q : ℝ) :
    polynomialEnvelopeTransferRate n p B q =
      B * dimensionLog p * ((dimensionLog p * dimensionLog n) / (n : ℝ)) ^ (1 / 2 - 1 / q) := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hD : 0 < dimensionLog n := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  unfold polynomialEnvelopeTransferRate polynomialEnvelopeV
  rw [Real.div_rpow (mul_nonneg hL.le hD.le) hN.le, Real.mul_rpow hL.le hD.le,
    show (3 / 2 : ℝ) - 1 / q = 1 + (1 / 2 - 1 / q) by ring,
    Real.rpow_add hL, Real.rpow_one]
  ring

theorem polynomialTruncationThreshold_ge {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {B q : ℝ} (hB : 0 ≤ B) (hq : 0 < q)
    (hlarge : dimensionLog p * dimensionLog n ≤ n) :
    2 * B ≤ polynomialTruncationThreshold n p B q := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hD : 0 < dimensionLog n := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  have hr : 1 ≤ (n : ℝ) / (dimensionLog p * dimensionLog n) :=
    (one_le_div (mul_pos hL hD)).mpr hlarge
  have hpw := Real.one_le_rpow hr (one_div_nonneg.mpr hq.le)
  have hm := mul_le_mul_of_nonneg_left hpw (by positivity : 0 ≤ 2 * B)
  simpa only [mul_one, polynomialTruncationThreshold] using hm

theorem polynomialTruncation_first_term {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (B q : ℝ) :
    polynomialTruncationThreshold n p B q / Real.sqrt (n : ℝ) *
      dimensionLog p ^ (3 / 2 : ℝ) * Real.sqrt (dimensionLog n) =
        2 * polynomialEnvelopeTransferRate n p B q := by
  let N := (n : ℝ)
  let L := dimensionLog p
  let D := dimensionLog n
  let b := 1 / q
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hD : 0 < D := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  have hNp : N ^ (1 / 2 - b) * N ^ b = N ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hLp : L ^ (3 / 2 - b) * L ^ b = L ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hDp : D ^ (1 / 2 - b) * D ^ b = D ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hD]
    congr 1
    ring
  change (2 * B * (N / (L * D)) ^ b) / Real.sqrt N * L ^ (3 / 2 : ℝ) * Real.sqrt D =
    2 * (B * L ^ (3 / 2 - b) / N ^ (1 / 2 - b) * D ^ (1 / 2 - b))
  rw [Real.div_rpow hN.le (mul_nonneg hL.le hD.le), Real.mul_rpow hL.le hD.le,
    Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  rw [← hLp, ← hDp, ← hNp]
  field_simp
  ring

theorem polynomialTruncation_covariance_term_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {B q : ℝ} (hB : 0 < B) (hq : 2 < q) :
    dimensionLog p * Real.sqrt
      (truncationVarianceBudget B (polynomialTruncationThreshold n p B q) q) ≤
        polynomialEnvelopeTransferRate n p B q := by
  let N := (n : ℝ)
  let L := dimensionLog p
  let D := dimensionLog n
  let a := 1 / 2 - 1 / q
  let r := N / (L * D)
  let u := r ^ (1 / q)
  have hN : 0 < N := by dsimp [N]; exact_mod_cast hn
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hD : 0 < D := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hn)
  have hr : 0 < r := div_pos hN (mul_pos hL hD)
  have hu : 0 < u := Real.rpow_pos_of_pos hr _
  have hpow : (2 * B * u) ^ (2 - q) ≤ (B * u) ^ (2 - q) :=
    Real.rpow_le_rpow_of_exponent_nonpos (mul_pos hB hu) (by nlinarith) (by linarith)
  have hv : truncationVarianceBudget B (polynomialTruncationThreshold n p B q) q ≤
      (B * r ^ (-a)) ^ 2 := by
    have hb := mul_le_mul_of_nonneg_left hpow (Real.rpow_nonneg hB.le q)
    have he : B ^ q * (B * u) ^ (2 - q) = (B * r ^ (-a)) ^ 2 := by
      rw [Real.mul_rpow hB.le hu.le]
      calc
        _ = (B ^ q * B ^ (2 - q)) * u ^ (2 - q) := by ring
        _ = B ^ (2 : ℝ) * r ^ ((1 / q) * (2 - q)) := by
          rw [← Real.rpow_add hB]
          dsimp only [u]
          rw [← Real.rpow_mul hr.le]
          congr 2
          ring
        _ = B ^ (2 : ℝ) * r ^ ((-a) * 2) := by
          congr 2
          dsimp only [a]
          field_simp
          ring
        _ = _ := by rw [Real.rpow_mul hr.le, Real.rpow_two, Real.rpow_two, mul_pow]
    exact hb.trans_eq he
  have hs : Real.sqrt
      (truncationVarianceBudget B (polynomialTruncationThreshold n p B q) q) ≤ B * r ^ (-a) := by
    exact Real.sqrt_le_iff.mpr ⟨mul_nonneg hB.le (Real.rpow_nonneg hr.le _), hv⟩
  have he : polynomialEnvelopeTransferRate n p B q = L * (B * r ^ (-a)) := by
    rw [polynomialEnvelopeTransferRate_eq_ratio hp hn]
    have hinv : (dimensionLog p * dimensionLog n) / (n : ℝ) = r⁻¹ := by
      dsimp only [r, N, L, D]
      rw [inv_div]
    rw [hinv, Real.inv_rpow hr.le, ← Real.rpow_neg hr.le]
    ring
  rw [he]
  exact mul_le_mul_of_nonneg_left hs hL.le

theorem polynomialEnvelopeV_le_transferRate {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {B q : ℝ} (hB : 0 ≤ B) (hq : 2 < q) :
    polynomialEnvelopeV n p B q ≤ polynomialEnvelopeTransferRate n p B q := by
  have ha : 0 ≤ (1 / 2 : ℝ) - 1 / q := by
    have hqp : 0 < q := by linarith
    have hrec : 1 / q ≤ (1 / 2 : ℝ) := (div_le_iff₀ hqp).mpr (by linarith)
    linarith
  have hpw := Real.one_le_rpow (log_exp_mul_nat_ge_one hn) ha
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hV : 0 ≤ polynomialEnvelopeV n p B q := by unfold polynomialEnvelopeV; positivity
  have hm := mul_le_mul_of_nonneg_left hpw hV
  simpa only [mul_one, polynomialEnvelopeTransferRate] using hm

theorem polynomialTruncation_threshold_rate_le {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {B q : ℝ} (hB : 0 < B) (hq : 2 < q) :
    conditionalPolynomialThresholdRate n p B (polynomialTruncationThreshold n p B q) q ≤
      4 * polynomialEnvelopeTransferRate n p B q := by
  unfold conditionalPolynomialThresholdRate
  rw [polynomialTruncation_first_term hp hn]
  have hc := polynomialTruncation_covariance_term_le hp hn hB hq
  have hv := polynomialEnvelopeV_le_transferRate hp hn hB.le hq
  linarith

theorem polynomialEnvelopeTransferRate_ge_one_of_small {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    {B q : ℝ} (hB : 1 ≤ B) (hq : 2 < q)
    (hsmall : (n : ℝ) ≤ dimensionLog p * dimensionLog n) :
    1 ≤ polynomialEnvelopeTransferRate n p B q := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hratio : 1 ≤ (dimensionLog p * dimensionLog n) / (n : ℝ) :=
    (one_le_div hN).mpr hsmall
  have ha : 0 ≤ (1 / 2 : ℝ) - 1 / q := by
    have hqp : 0 < q := by linarith
    have hrec : 1 / q ≤ (1 / 2 : ℝ) := (div_le_iff₀ hqp).mpr (by linarith)
    linarith
  have hpw := Real.one_le_rpow hratio ha
  rw [polynomialEnvelopeTransferRate_eq_ratio hp hn]
  exact one_le_mul_of_one_le_of_one_le (one_le_mul_of_one_le_of_one_le hB hL) hpw

def polynomialEnvelopeTransferConstant : ℝ := 4 * conditionalPolynomialConstant

theorem one_le_polynomialEnvelopeTransferConstant : 1 ≤ polynomialEnvelopeTransferConstant := by
  unfold polynomialEnvelopeTransferConstant
  linarith [one_le_conditionalPolynomialConstant]

/-- Proposition 2, on every original probability space and every genuine
independent centered envelope-moment array. The Gaussian covariance may be
singular and the observation laws need not coincide. -/
theorem polynomialEnvelopeTransfer
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) {B q : ℝ} (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hB : 1 ≤ B) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hfactor : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      polynomialEnvelopeTransferConstant * min 1 (polynomialEnvelopeTransferRate n p B q) := by
  by_cases hlarge : dimensionLog p * dimensionLog n ≤ (n : ℝ)
  · have hT := polynomialTruncationThreshold_ge hp hn (zero_le_one.trans hB)
      (by linarith : 0 < q) hlarge
    have hh := polynomialEnvelope_threshold_of_average_variances μ X hX hind hp hn hB hT hq
      hmoment hbudget hcenter haverage A hfactor
    have hrate := min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4)
      (polynomialTruncation_threshold_rate_le hp hn (zero_lt_one.trans_le hB) hq)
    have hc := mul_le_mul_of_nonneg_left hrate
      (zero_le_one.trans one_le_conditionalPolynomialConstant)
    exact hh.trans (hc.trans_eq (by unfold polynomialEnvelopeTransferConstant; ring))
  · have hr := polynomialEnvelopeTransferRate_ge_one_of_small hp hn hB hq (le_of_not_ge hlarge)
    rw [min_eq_left hr, mul_one]
    exact (rectangleDistance_le_one _ _ _).trans one_le_polynomialEnvelopeTransferConstant

end
end RectangleCLT.Companion.SplitV4
