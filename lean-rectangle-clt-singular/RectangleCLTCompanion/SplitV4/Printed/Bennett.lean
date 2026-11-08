import RectangleCLTCompanion.SplitV4.Printed.LargeIncrement
import RectangleCLTCompanion.SplitV4.BennettPolynomial

/-! Proposition 3 reassembled with the printed G.1 Bernstein route. The
preserved scalar regime proofs supply the exact small-K calibration,
Cauchy--Schwarz tail variance, logarithmic denominator comparison and
large-K log-power bounds. They are retained without additional premises. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
set_option autoImplicit false
variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {p n : ℕ} {q A t u : ℝ}

theorem bennett_polynomial_small_regime
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 ≤ A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q)
    (hK : bennettPolynomialParameter q d A (dimensionLog p) ≤ 1) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettSmallRegimeConstant q * bennettBaseScale d (dimensionLog p) := by
  let L := dimensionLog p
  let U := bennettBaseScale d L
  let V := bennettEnvelopeScale q A L
  let t := U / L ^ (3 / 2 : ℝ)
  let Ctail := 4 * (2 : ℝ) ^ (q / 2)
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 < U := bennettBaseScale_pos hd hL
  have ht : 0 < t := div_pos hU (Real.rpow_pos_of_pos hL _)
  have hV : 0 ≤ V := mul_nonneg hA (Real.rpow_nonneg hL.le _)
  have hVU : V ≤ U := by
    have hr : 0 ≤ V / U := div_nonneg hV hU.le
    have hk : (V / U) ^ 2 ≤ 1 := hK
    exact (div_le_one hU).mp (by nlinarith)
  have hLp : 0 < L ^ (3 / 2 : ℝ) := Real.rpow_pos_of_pos hL _
  have hpow : L ^ (3 / 2 - 1 / q : ℝ) * L ^ (1 / q) = L ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_add hL]
    congr 1
    ring
  have hratio : A / t ≤ L ^ (1 / q) := by
    apply (div_le_iff₀ ht).mpr
    change A ≤ L ^ (1 / q) * (U / L ^ (3 / 2 : ℝ))
    rw [← mul_div_assoc]
    apply (le_div_iff₀ hLp).mpr
    have hh := mul_le_mul_of_nonneg_right hVU (Real.rpow_nonneg hL.le (1 / q))
    change (A * L ^ (3 / 2 - 1 / q : ℝ)) * L ^ (1 / q) ≤ U * L ^ (1 / q) at hh
    calc
      _ = (A * L ^ (3 / 2 - 1 / q : ℝ)) * L ^ (1 / q) := by rw [mul_assoc, hpow]
      _ ≤ U * L ^ (1 / q) := hh
      _ = _ := mul_comm _ _
  have hcal := bennett_small_calibration_identities hd hL
  have h32 : L ^ (3 / 2 : ℝ) = Real.sqrt L * L := by
    calc
      _ = L ^ ((1 / 2 : ℝ) + 1) := by congr 1; ring
      _ = L ^ (1 / 2 : ℝ) * L ^ (1 : ℝ) := Real.rpow_add hL _ _
      _ = _ := by rw [← Real.sqrt_eq_rpow, Real.rpow_one]
  have hfirst : t * Real.sqrt L * L = U := by
    calc
      _ = t * L ^ (3 / 2 : ℝ) := by rw [h32]; ring
      _ = U := hcal.1
  have hsecond : L * Real.sqrt (d ^ 2) / t = U := by
    rw [Real.sqrt_sq hd.le]
    simpa only [mul_comm] using hcal.2.1
  have hthird : Real.sqrt L * d ^ 2 / t ^ 3 = U := by
    simpa only [mul_comm] using hcal.2.2
  have hLhalf : (L ^ (1 / q)) ^ (q / 2) = Real.sqrt L := by
    rw [← Real.rpow_mul hL.le, Real.sqrt_eq_rpow]
    congr 1
    field_simp
  have hv := pairedTailVariance_polynomial_rate ξ hξ hd.le (by linarith : 1 ≤ q)
    hA ht hi4 hfourth hmoment hbudget
  have hv' : pairedTailVariance μ ξ t ≤ Ctail * d * Real.sqrt L := by
    have hr := Real.rpow_le_rpow (div_nonneg hA ht.le) hratio (by linarith : 0 ≤ q / 2)
    rw [hLhalf] at hr
    exact hv.trans (mul_le_mul_of_nonneg_left hr (by positivity))
  have htermv : Real.sqrt L * pairedTailVariance μ ξ t / t ≤ Ctail * U := by
    calc
      _ ≤ Real.sqrt L * (Ctail * d * Real.sqrt L) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv' (Real.sqrt_nonneg _)) ht.le
      _ = Ctail * (d * L / t) := by
        have heq : Real.sqrt L * (Ctail * d * Real.sqrt L) = Ctail * d * L := by
          calc
            _ = Ctail * d * (Real.sqrt L) ^ 2 := by ring
            _ = _ := by rw [Real.sq_sqrt hL.le]
        rw [heq]
        ring
      _ = _ := by rw [hcal.2.1]
  have hLq : (L ^ (1 / q)) ^ q = L := by
    rw [← Real.rpow_mul hL.le, one_div_mul_cancel hq0.ne', Real.rpow_one]
  have hApow : A ^ q ≤ t ^ q * L := by
    have ha : A ≤ t * L ^ (1 / q) := by
      simpa only [mul_comm] using (div_le_iff₀ ht).mp hratio
    have hh := Real.rpow_le_rpow hA ha hq0.le
    rw [Real.mul_rpow ht.le (Real.rpow_nonneg hL.le _), hLq] at hh
    exact hh
  have htpow : t ^ q / t ^ (q - 1) = t := by
    rw [← Real.rpow_sub ht, show q - (q - 1) = 1 by ring, Real.rpow_one]
  have hM := pairedTailExpectedMaximum_direct_bound ξ hξ hq1 hA ht hmoment hbudget
  have hM' : pairedTailExpectedMaximum μ ξ t ≤ (2 : ℝ) ^ q * t * L := by
    calc
      _ ≤ (2 * A) ^ q / t ^ (q - 1) := hM
      _ = (2 : ℝ) ^ q * A ^ q / t ^ (q - 1) := by rw [Real.mul_rpow (by norm_num) hA]
      _ ≤ (2 : ℝ) ^ q * (t ^ q * L) / t ^ (q - 1) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hApow (Real.rpow_nonneg (by norm_num) _))
          (Real.rpow_nonneg ht.le _)
      _ = (2 : ℝ) ^ q * (t ^ q / t ^ (q - 1)) * L := by ring
      _ = _ := by rw [htpow]
  have htermM : Real.sqrt L * pairedTailExpectedMaximum μ ξ t ≤ (2 : ℝ) ^ q * U := by
    have hh := mul_le_mul_of_nonneg_left hM' (Real.sqrt_nonneg L)
    have heq : Real.sqrt L * ((2 : ℝ) ^ q * t * L) = (2 : ℝ) ^ q * U := by
      calc
        _ = (2 : ℝ) ^ q * (t * Real.sqrt L * L) := by ring
        _ = _ := by rw [hfirst]
    exact hh.trans_eq heq
  have hrate : largeIncrementBandwidthRate L (d ^ 2)
      (pairedTailVariance μ ξ t) (pairedTailExpectedMaximum μ ξ t) t ≤
        (3 + Ctail + (2 : ℝ) ^ q) * U := by
    unfold largeIncrementBandwidthRate
    rw [hfirst, hsecond, hthird]
    linarith
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hi4 hunit G hG
    (sq_nonneg d) hfourth ht
  have hC : 0 ≤ largeIncrementMasterConstant := zero_le_one.trans one_le_largeIncrementMasterConstant
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hrate hC
  convert hh using 1 <;> unfold bennettSmallRegimeConstant <;> dsimp [Ctail, U] <;> ring

set_option maxHeartbeats 2000000 in

theorem bennett_polynomial_large_regime
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 < A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q)
    (hK : 1 < bennettPolynomialParameter q d A (dimensionLog p)) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettLargeRegimeConstant q *
        (bennettEnvelopeScale q A (dimensionLog p) /
          bennettPolynomialLog q d A (dimensionLog p) ^ (1 - 1 / q)) := by
  let L := dimensionLog p
  let U := bennettBaseScale d L
  let V := bennettEnvelopeScale q A L
  let K := bennettPolynomialParameter q d A L
  let ell := bennettParameterLog K
  let r := V / ell ^ (1 - 1 / q)
  let t := r / L ^ (3 / 2 : ℝ)
  let u := ell * t
  let Ct := bennettTailConstant q
  let α := bennettLogComparisonConstant q
  let Cr := bennettRatioConstant q
  have hq0 : 0 < q := by linarith
  have hq1 : 1 < q := by linarith
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 < U := bennettBaseScale_pos hd hL
  have hV : 0 < V := mul_pos hA (Real.rpow_pos_of_pos hL _)
  have hK1 : 1 < K := hK
  have hK0 : 0 < K := zero_lt_one.trans hK1
  have hell1 : 1 ≤ ell := bennettParameterLog_ge_one hK1.le
  have hell : 0 < ell := zero_lt_one.trans_le hell1
  have hr : 0 < r := div_pos hV (Real.rpow_pos_of_pos hell _)
  have ht : 0 < t := div_pos hr (Real.rpow_pos_of_pos hL _)
  have hu : 0 < u := mul_pos hell ht
  have hCt : 0 < Ct := bennettTailConstant_pos q
  have hα : 0 < α := bennettLogComparisonConstant_pos q
  have hCr : 0 < Cr := bennettRatioConstant_pos q
  have hUcal : U ^ 2 = d * L ^ (5 / 2 : ℝ) := bennettBaseScale_sq hd.le hL.le
  have hKV : V ^ 2 = K * U ^ 2 := by
    change V ^ 2 = (V / U) ^ 2 * U ^ 2
    rw [div_pow, div_mul_cancel₀ _ (pow_ne_zero 2 hU.ne')]
  have hVdef : V = A * L ^ (3 / 2 - 1 / q : ℝ) := rfl
  have hrV : r * ell ^ (1 - 1 / q) = V := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hell _).ne'
  have htR : t * L ^ (3 / 2 : ℝ) = r := div_mul_cancel₀ _ (Real.rpow_pos_of_pos hL _).ne'
  have huDef : u = ell * t := rfl
  have hcal := bennett_large_calibration_identities hq0 hL hell hK0 hr ht hUcal hKV hVdef hrV htR huDef
  have htail := bennett_large_tail_identities hq0 hL hell hK0 hr ht hUcal hKV hVdef hrV htR huDef
  have hv : pairedTailVariance μ ξ t ≤ Ct * d * (A / t) ^ (q / 2) := by
    exact pairedTailVariance_polynomial_rate ξ hξ hd.le (by linarith : 1 ≤ q)
      hA.le ht hi4 hfourth hmoment hbudget
  have hvarcost : Real.sqrt L * pairedTailVariance μ ξ t / t ≤
      Ct * (r * ell ^ (2 * (1 - 1 / q) + (q - 1) / 2) / K) := by
    calc
      _ ≤ Real.sqrt L * (Ct * d * (A / t) ^ (q / 2)) / t :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hv (Real.sqrt_nonneg _)) ht.le
      _ = Ct * (Real.sqrt L * d * (A / t) ^ (q / 2) / t) := by ring
      _ = _ := by rw [hcal.2.2.2]
  have hMcost : Real.sqrt L * pairedTailExpectedMaximum μ ξ t ≤
      (2 / α + (2 : ℝ) ^ q) * r := by
    by_cases hvzero : pairedTailVariance μ ξ t = 0
    · rw [pairedTailExpectedMaximum_zero_of_variance_zero ξ hξ t hi4 hvzero, mul_zero]
      positivity
    have hvpos : 0 < pairedTailVariance μ ξ t := (pairedTailVariance_nonneg μ ξ t).lt_of_ne' hvzero
    have hvbar : 0 < Ct * d * (A / t) ^ (q / 2) := by positivity
    have hnum : 0 ≤ u ^ 2 * L := by positivity
    have hratioEq : u ^ 2 * L / (Ct * d * (A / t) ^ (q / 2)) =
        (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) := by
      calc
        _ = (1 / Ct) * (u ^ 2 * L / (d * (A / t) ^ (q / 2))) := by
          simp only [div_eq_mul_inv, mul_inv_rev]
          ring
        _ = _ := by rw [htail.2.2]; ring
    have hratio : (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) ≤
        u ^ 2 * L / pairedTailVariance μ ξ t := by
      rw [← hratioEq]
      apply (div_le_div_iff₀ hvbar hvpos).mpr
      exact mul_le_mul_of_nonneg_left hv hnum
    have hlog := Real.log_le_log
      (show 0 < 1 + (1 / Ct) * K * ell ^ (2 / q - (q - 1) / 2) by positivity)
      (add_le_add_left hratio 1)
    have hdenlower : α * ell ≤ Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) :=
      (bennettLogComparisonConstant_bound q K hK1.le).trans hlog
    have hdenpos : 0 < Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) :=
      (mul_pos hα hell).trans_le hdenlower
    have hfrac : (2 * Real.sqrt L * u * L) /
        Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) ≤ (2 / α) * r := by
      calc
        _ ≤ (2 * Real.sqrt L * u * L) / (α * ell) := by
          apply (div_le_div_iff₀ hdenpos (mul_pos hα hell)).mpr
          exact mul_le_mul_of_nonneg_left hdenlower (by positivity)
        _ = _ := by
          have heq : 2 * Real.sqrt L * u * L = 2 * (r * ell) := by
            calc
              _ = 2 * (Real.sqrt L * u * L) := by ring
              _ = _ := by rw [htail.1]
          rw [heq]
          field_simp [hα.ne', hell.ne']
          ring
    have hrem : Real.sqrt L * ((2 * A) ^ q / u ^ (q - 1)) = (2 : ℝ) ^ q * r := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hA.le]
      calc
        _ = (2 : ℝ) ^ q * (Real.sqrt L * A ^ q / u ^ (q - 1)) := by ring
        _ = _ := by rw [htail.2.1]
    have hM := pairedTailExpectedMaximum_bennett_bound ξ hξ hind hp t hq1 hA.le hu hi4 hmoment hbudget
    calc
      _ ≤ Real.sqrt L * (2 * u * L / Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) +
          (2 * A) ^ q / u ^ (q - 1)) :=
        mul_le_mul_of_nonneg_left hM (Real.sqrt_nonneg _)
      _ = (2 * Real.sqrt L * u * L) / Real.log (1 + u ^ 2 * L / pairedTailVariance μ ξ t) +
          Real.sqrt L * ((2 * A) ^ q / u ^ (q - 1)) := by ring
      _ ≤ (2 / α) * r + (2 : ℝ) ^ q * r := add_le_add hfrac hrem.le
      _ = _ := by ring
  have hratios := bennettRatioConstant_bound q K hK1.le
  simp only [Real.rpow_two] at hratios
  have h32 : L ^ (3 / 2 : ℝ) = Real.sqrt L * L := by
    calc
      _ = L ^ ((1 / 2 : ℝ) + 1) := by congr 1; ring
      _ = L ^ (1 / 2 : ℝ) * L ^ (1 : ℝ) := Real.rpow_add hL _ _
      _ = _ := by rw [← Real.sqrt_eq_rpow, Real.rpow_one]
  have hfirst : t * Real.sqrt L * L = r := by
    calc
      _ = t * L ^ (3 / 2 : ℝ) := by rw [h32]; ring
      _ = _ := htR
  have hsecond : L * Real.sqrt (d ^ 2) / t ≤ Cr * r := by
    rw [Real.sqrt_sq hd.le, show L * d = d * L by ring, hcal.2.1]
    convert mul_le_mul_of_nonneg_left hratios.1 hr.le using 1 <;> ring
  have hthird : Real.sqrt L * d ^ 2 / t ^ 3 ≤ Cr * r := by
    rw [show Real.sqrt L * d ^ 2 = d ^ 2 * Real.sqrt L by ring, hcal.2.2.1]
    convert mul_le_mul_of_nonneg_left hratios.2.1 hr.le using 1 <;> ring
  have hvarfinal : Real.sqrt L * pairedTailVariance μ ξ t / t ≤ Ct * Cr * r := by
    apply hvarcost.trans
    convert mul_le_mul_of_nonneg_left hratios.2.2 (mul_nonneg hCt.le hr.le) using 1 <;> ring
  have hrate : largeIncrementBandwidthRate L (d ^ 2)
      (pairedTailVariance μ ξ t) (pairedTailExpectedMaximum μ ξ t) t ≤
        (1 + (2 + Ct) * Cr + 2 / α + (2 : ℝ) ^ q) * r := by
    unfold largeIncrementBandwidthRate
    rw [hfirst]
    nlinarith
  have hb := largeIncrementGaussianComparison_bandwidth μ hp ξ hξ hind hcenter hi4 hunit G hG
    (sq_nonneg d) hfourth ht
  have hC : 0 ≤ largeIncrementMasterConstant := zero_le_one.trans one_le_largeIncrementMasterConstant
  apply hb.trans
  have hh := mul_le_mul_of_nonneg_left hrate hC
  convert hh using 1 <;>
    simp only [bennettLargeRegimeConstant, Ct, Cr, α, r, ell, K, L, V,
      bennettPolynomialLog, bennettParameterLog] <;> ring

theorem bennettPolynomialCLT
    (hp : 1 ≤ p) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (sumVector ξ))
    {d : ℝ} (hd : 0 < d) (hq : 2 < q) (hA : 0 < A)
    (hfourth : ∀ j, (∑ i, ∫ ω, ξ i ω j ^ 4 ∂μ) ≤ d ^ 2)
    (hmoment : ∀ i, Integrable (fun ω => ‖ξ i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖ξ i ω‖ ^ q ∂μ) ≤ A ^ q) :
    rectangleDistance μ (sumVector ξ) G ≤
      bennettPolynomialConstant q * min 1 (bennettPolynomialRate q d A (dimensionLog p)) := by
  let L := dimensionLog p
  let R := bennettPolynomialRate q d A L
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hU : 0 ≤ bennettBaseScale d L := Real.sqrt_nonneg _
  have htail : 0 ≤ bennettEnvelopeScale q A L / bennettPolynomialLog q d A L ^ (1 - 1 / q) :=
    div_nonneg (mul_nonneg hA.le (Real.rpow_nonneg hL.le _))
      (Real.rpow_nonneg (zero_le_one.trans (one_le_bennettPolynomialLog q d A L)) _)
  have hC := one_le_bennettPolynomialConstant q
  have hC0 : 0 ≤ bennettPolynomialConstant q := zero_le_one.trans hC
  have hCs : bennettSmallRegimeConstant q ≤ bennettPolynomialConstant q := by
    have hh := le_max_left (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q)
    unfold bennettPolynomialConstant
    linarith
  have hCl : bennettLargeRegimeConstant q ≤ bennettPolynomialConstant q := by
    have hh := le_max_right (bennettSmallRegimeConstant q) (bennettLargeRegimeConstant q)
    unfold bennettPolynomialConstant
    linarith
  have hb : rectangleDistance μ (sumVector ξ) G ≤ bennettPolynomialConstant q * R := by
    by_cases hK : bennettPolynomialParameter q d A L ≤ 1
    · have hs := bennett_polynomial_small_regime hp ξ hξ hind hcenter hi4 hunit G hG hd hq hA.le
        hfourth hmoment hbudget hK
      have hh := mul_le_mul_of_nonneg_right hCs hU
      have hUR : bennettBaseScale d L ≤ R := le_add_of_nonneg_right htail
      exact hs.trans (hh.trans (mul_le_mul_of_nonneg_left hUR hC0))
    · have hl := bennett_polynomial_large_regime hp ξ hξ hind hcenter hi4 hunit G hG hd hq hA
        hfourth hmoment hbudget (lt_of_not_ge hK)
      have hh := mul_le_mul_of_nonneg_right hCl htail
      have hTR : bennettEnvelopeScale q A L / bennettPolynomialLog q d A L ^ (1 - 1 / q) ≤ R :=
        le_add_of_nonneg_left hU
      exact hl.trans (hh.trans (mul_le_mul_of_nonneg_left hTR hC0))
  change rectangleDistance μ (sumVector ξ) G ≤ bennettPolynomialConstant q * min 1 R
  by_cases hR : R ≤ 1
  · rw [min_eq_right hR]
    exact hb
  · rw [min_eq_left (le_of_not_ge hR), mul_one]
    exact (rectangleDistance_le_one μ (sumVector ξ) G).trans hC

theorem bennettPolynomialCLT_observations
    (hp : 1 ≤ p) (hn : 1 ≤ n) (X : Fin n → Ω → Vector p) (hX : ∀ i, Measurable (X i))
    (hind : iIndepFun X μ) (hcenter : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (hi4 : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ)
    (haverage : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1)
    (G : Matrix (Fin p) (Fin p) ℝ) (hG : G * G.transpose = covariance μ (normalizedObservationSum X))
    {B : ℝ} (hB : 1 ≤ B) (hq : 2 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖X i ω‖ ^ q) μ)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖ ^ q ∂μ) ≤ B ^ q)
    (hfourth : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 4 ∂μ) ≤ B ^ 2) :
    rectangleDistance μ (normalizedObservationSum X) G ≤
      bennettPolynomialConstant q * min 1
        (B ^ (1 / 2 : ℝ) * dimensionLog p ^ (5 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) +
          (B * dimensionLog p ^ (3 / 2 - 1 / q)) /
            ((n : ℝ) ^ (1 / 2 - 1 / q) *
              Real.log (Real.exp 1 + B * ((n : ℝ) / dimensionLog p) ^ (2 / q - 1 / 2)) ^ (1 - 1 / q))) := by
  let d := rawPolynomialFourthScale n B
  let A := rawPolynomialEnvelopeScale n B q
  let L := dimensionLog p
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hBpos : 0 < B := zero_lt_one.trans_le hB
  have hd : 0 < d := div_pos hBpos (Real.sqrt_pos.mpr hN)
  have hApos : 0 < A := mul_pos hBpos (Real.rpow_pos_of_pos hN _)
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hL2 (i : Fin n) (j : Fin p) : MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ :=
    coordinate_memLp_two_of_fourth_moment μ _ ((measurable_pi_apply j).comp (hX i)) (hi4 i j)
  have hG' : G * G.transpose = covariance μ (sumVector (normalizedSummands X)) := by
    simpa only [sumVector_normalizedSummands] using hG
  have hb := bennettPolynomialCLT hp (normalizedSummands X)
    (normalizedSummands_measurable hX) (normalizedSummands_independent hind)
    (normalizedSummands_centered hcenter) (normalizedSummands_fourth_integrable hi4)
    (normalizedSummands_unit_covariance hind hL2 hcenter haverage) G hG' hd hq hApos
    (normalized_coordinate_fourth_budget X hn hfourth)
    (normalized_q_envelope_integrable X q hmoment)
    (normalized_q_envelope_budget X hn hBpos.le (by linarith : 0 < q) hbudget)
  have hK : bennettPolynomialParameter q d A L = B * ((n : ℝ) / L) ^ (2 / q - 1 / 2) := by
    rw [bennettPolynomialParameter_eq hd hL]
    exact rawPolynomialParameter_eq hn hBpos hL
  have hrate : bennettPolynomialRate q d A L =
      B ^ (1 / 2 : ℝ) * L ^ (5 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ) +
        (B * L ^ (3 / 2 - 1 / q)) / ((n : ℝ) ^ (1 / 2 - 1 / q) *
          Real.log (Real.exp 1 + B * ((n : ℝ) / L) ^ (2 / q - 1 / 2)) ^ (1 - 1 / q)) := by
    unfold bennettPolynomialRate bennettBaseScale bennettEnvelopeScale bennettPolynomialLog
    rw [hK, rawPolynomialBaseScale_eq hn hBpos.le hL, rawPolynomialEnvelopeTerm_eq hn]
    rw [div_div]
  rw [sumVector_normalizedSummands] at hb
  change rectangleDistance μ (normalizedObservationSum X) G ≤
    bennettPolynomialConstant q * min 1 (bennettPolynomialRate q d A L) at hb
  rw [hrate] at hb
  exact hb

end
end RectangleCLT.Companion.SplitV4.Printed
