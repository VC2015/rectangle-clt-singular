import RectangleCLTCompanion.SplitV4.PolynomialMain
import RectangleCLTCompanion.SplitV4.Printed.Bennett
import RectangleCLTCompanion.SplitV4.SparseLowerLogScales
import RectangleCLTCompanion.SplitV4.SparseUniformBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Unnumbered polynomial regime calculations in the frozen manuscript,
Section `poly:transition` and the remarks after `lower:sparse`. -/

open MeasureTheory Set Filter Asymptotics
open scoped Topology
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def polynomialTransitionExponent (q : ℝ) : ℝ := 2 / q - 1 / 2

def polynomialTransitionParameter (B q r : ℝ) : ℝ := B * r ^ polynomialTransitionExponent q

theorem polynomialTransitionExponent_pos {q : ℝ} (hq : 2 < q) (hq4 : q < 4) :
    0 < polynomialTransitionExponent q := by
  have hqp : 0 < q := by linarith
  have h := (lt_div_iff₀ hqp).mpr (by linarith : (1 / 2 : ℝ) * q < 2)
  dsimp [polynomialTransitionExponent]
  linarith

theorem polynomialTransitionExponent_neg {q : ℝ} (hq : 4 < q) :
    polynomialTransitionExponent q < 0 := by
  have hqp : 0 < q := by linarith
  have h := (div_lt_iff₀ hqp).mpr (by linarith : (2 : ℝ) < 1 / 2 * q)
  dsimp [polynomialTransitionExponent]
  linarith

theorem polynomialTransitionParameter_tendsto_atTop {B q : ℝ} (hB : 0 < B)
    (hq : 2 < q) (hq4 : q < 4) {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => polynomialTransitionParameter B q (r n)) atTop atTop := by
  exact tendsto_const_nhds.pos_mul_atTop hB
    ((tendsto_rpow_atTop (polynomialTransitionExponent_pos hq hq4)).comp hr)

theorem polynomialTransitionParameter_tendsto_zero {B q : ℝ} (hq : 4 < q)
    {r : ℕ → ℝ} (hr : Tendsto r atTop atTop) :
    Tendsto (fun n => polynomialTransitionParameter B q (r n)) atTop (𝓝 0) := by
  have he := tendsto_rpow_neg_atTop (neg_pos.mpr (polynomialTransitionExponent_neg hq))
  simpa only [neg_neg, mul_zero, polynomialTransitionParameter] using (he.comp hr).const_mul B

@[simp] theorem polynomialTransitionParameter_four (B r : ℝ) :
    polynomialTransitionParameter B 4 r = B := by
  norm_num [polynomialTransitionParameter, polynomialTransitionExponent]

/-- The exact ratio used to identify which Bennett term dominates. -/
theorem bennettEnvelope_div_base_eq_sqrt_parameter {q d A L : ℝ}
    (hd : 0 < d) (hA : 0 ≤ A) (hL : 0 < L) :
    (bennettEnvelopeScale q A L / (bennettPolynomialLog q d A L) ^ (1 - 1 / q)) /
      bennettBaseScale d L =
      Real.sqrt (bennettPolynomialParameter q d A L) /
        (bennettPolynomialLog q d A L) ^ (1 - 1 / q) := by
  have hv : 0 ≤ bennettEnvelopeScale q A L := mul_nonneg hA (Real.rpow_nonneg hL.le _)
  rw [bennettPolynomialParameter, Real.sqrt_sq (div_nonneg hv (bennettBaseScale_pos hd hL).le)]
  ring

/-- Every fixed power of the Bennett logarithm is negligible relative to
`sqrt K`, giving the printed diverging ratio for 2<q<4. -/
theorem sqrt_div_bennett_log_tendsto_atTop (b : ℝ) {K : ℕ → ℝ}
    (hK : Tendsto K atTop atTop) :
    Tendsto (fun n => Real.sqrt (K n) / (Real.log (Real.exp 1 + K n)) ^ b)
      atTop atTop := by
  have hL : Tendsto (fun n => Real.log (Real.exp 1 + K n) / Real.log (K n)) atTop (𝓝 1) :=
    tendsto_log_exp_add_div_log K hK
  have hratio := (isLittleO_log_rpow_rpow_atTop b (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hpow := hL.rpow_const (p := b) (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  have hh := (hratio.comp hK).mul hpow
  simp only [Real.one_rpow, zero_mul] at hh
  have hz : Tendsto (fun n => (Real.log (Real.exp 1 + K n)) ^ b / Real.sqrt (K n))
      atTop (𝓝 0) := by
    apply hh.congr'
    filter_upwards [hK.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
    have hlog : 0 < Real.log (K n) := Real.log_pos hn
    rw [Real.div_rpow (Real.log_nonneg (by linarith [Real.exp_pos 1] : 1 ≤ Real.exp 1 + K n)) hlog.le,
      Real.sqrt_eq_rpow]
    field_simp [(Real.rpow_pos_of_pos hlog b).ne']
    ring
  have hpos : ∀ᶠ n : ℕ in atTop,
      0 < (Real.log (Real.exp 1 + K n)) ^ b / Real.sqrt (K n) := by
    filter_upwards [hK.eventually (eventually_gt_atTop (1 : ℝ))] with n hn
    exact div_pos (Real.rpow_pos_of_pos (Real.log_pos (by linarith [Real.add_one_le_exp 1])) _)
      (Real.sqrt_pos.mpr (by linarith))
  have ht := (tendsto_nhdsWithin_iff.mpr ⟨hz, hpos⟩ :
    Tendsto (fun n => (Real.log (Real.exp 1 + K n)) ^ b / Real.sqrt (K n)) atTop (𝓝[>] 0))
  simpa only [Function.comp_def, inv_div] using (tendsto_inv_nhdsGT_zero.comp ht)

/-- The explicit q=6 rate stated in the transition discussion. -/
theorem polynomialEnvelope_rates_six (n p : ℕ) (B : ℝ) :
    polynomialEnvelopeV n p B 6 = B * dimensionLog p ^ (4 / 3 : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ) ∧
    polynomialEnvelopeTransferRate n p B 6 =
      (B * dimensionLog p ^ (4 / 3 : ℝ) / (n : ℝ) ^ (1 / 3 : ℝ)) *
        dimensionLog n ^ (1 / 3 : ℝ) := by
  constructor <;> norm_num [polynomialEnvelopeV, polynomialEnvelopeTransferRate]

/-- For q>4 the polynomial decay exponent is strictly larger than 1/4. -/
theorem polynomial_decay_exponent_gt_quarter {q : ℝ} (hq : 4 < q) :
    (1 / 4 : ℝ) < 1 / 2 - 1 / q := by
  have h := (div_lt_iff₀ (by linarith : 0 < q)).mpr (by linarith : (1 : ℝ) < 1 / 4 * q)
  linarith

/-- The logarithm of the sparse parameter separates the three elementary
scale terms used in the front-of-paper sparse dimension remark. -/
theorem log_polynomialSparseParameter {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B q : ℝ} (hB : 0 < B) :
    Real.log (polynomialSparseParameter n p B q) =
      Real.log B + polynomialTransitionExponent q *
        (Real.log (n : ℝ) - Real.log (dimensionLog p)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  unfold polynomialSparseParameter polynomialTransitionExponent
  rw [Real.log_mul hB.ne' (Real.rpow_pos_of_pos (div_pos hN hL) _).ne',
    Real.log_rpow (div_pos hN hL), Real.log_div hN.ne' hL.ne']

/-- For fixed envelope the paper's log K=o(L) dimension condition follows
from log n=o(L); m→∞ gives L→∞ in the stated sparse setting. -/
theorem sparse_log_dimension_condition_of_log_n {B q : ℝ} (hB : 0 < B)
    {p : ℕ → ℕ} (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hL : Tendsto (fun n => dimensionLog (p n)) atTop atTop)
    (hlog : Tendsto (fun n : ℕ => Real.log (n : ℝ) / dimensionLog (p n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (polynomialSparseParameter n (p n) B q) /
      dimensionLog (p n)) atTop (𝓝 0) := by
  have hc := (tendsto_const_nhds (x := Real.log B)).div_atTop hL
  have hs := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hL
  have ht := hc.add ((hlog.sub hs).const_mul (polynomialTransitionExponent q))
  simp only [zero_sub, neg_zero, mul_zero, zero_add] at ht
  apply ht.congr'
  filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
  rw [log_polynomialSparseParameter hn hpn hB]
  simp only [Function.comp_def, id_eq]
  ring

/-- At four moments the sparse parameter condition is literally B_n→∞. -/
theorem polynomialSparseParameter_four (n p : ℕ) (B : ℝ) :
    polynomialSparseParameter n p B 4 = B := by
  norm_num [polynomialSparseParameter]

theorem sparse_parameter_four_tendsto_iff (B : ℕ → ℝ) (p : ℕ → ℕ) :
    Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) (B n) 4) atTop atTop ↔
      Tendsto B atTop atTop := by
  simp only [polynomialSparseParameter_four]


/-- The four-moment logarithmic quotient is uniformly bounded for every
B≥1, as used to absorb the coordinate term in `poly:q4`. -/
theorem exists_four_moment_absorption_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ B : ℝ, 1 ≤ B → ∀ U : ℝ, 0 ≤ U →
      U ≤ C * (Real.sqrt B * U / Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ)) := by
  obtain ⟨C, hC, hc⟩ := exists_log_power_div_rpow_bound (3 / 4) (1 / 2) (by norm_num)
  refine ⟨C, hC, ?_⟩
  intro B hB U hU
  have hBp : 0 < B := zero_lt_one.trans_le hB
  have hLp : 0 < Real.log (Real.exp 1 + B) :=
    Real.log_pos (by linarith [Real.add_one_le_exp 1])
  have hD : 0 < Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ) := Real.rpow_pos_of_pos hLp _
  have h := hc B hB
  rw [← Real.sqrt_eq_rpow] at h
  have he := (div_le_iff₀ (Real.sqrt_pos.mpr hBp)).mp h
  have hm := mul_le_mul_of_nonneg_right he hU
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hD).mpr
  change U * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ) ≤ _
  simpa only [bennettParameterLog, mul_assoc, mul_comm, mul_left_comm] using hm

/-- The printed four-moment rate uniformly absorbs the first Bennett
term, before saturation by one. -/
theorem exists_polynomialBennett_rate_four_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ n p : ℕ, 1 ≤ n → 1 ≤ p → ∀ B : ℝ, 1 ≤ B →
      polynomialBennettObservationRate n p B 4 ≤
        C * (B * dimensionLog p ^ (5 / 4 : ℝ) /
          ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ))) := by
  obtain ⟨C, hC, hc⟩ := exists_four_moment_absorption_constant
  refine ⟨C + 1, by linarith, ?_⟩
  intro n p hn hp B hB
  let U := polynomialCoordinateRate n p B
  let R := B * dimensionLog p ^ (5 / 4 : ℝ) /
    ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ))
  have hB0 : 0 ≤ B := zero_le_one.trans hB
  have hLp : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hU : 0 ≤ U := by dsimp [U, polynomialCoordinateRate]; positivity
  have he : Real.sqrt B * U / Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ) = R := by
    dsimp [U, R, polynomialCoordinateRate]
    rw [← Real.sqrt_eq_rpow]
    calc
      _ = (Real.sqrt B) ^ 2 * dimensionLog p ^ (5 / 4 : ℝ) /
          ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ)) := by ring
      _ = _ := by rw [Real.sq_sqrt hB0]
  have hb := hc B hB U hU
  rw [he] at hb
  rw [polynomialBennettObservationRate_four]
  change U + R ≤ (C + 1) * R
  nlinarith

/-- For q>4, K→0 makes the logarithmic tail term negligible relative
to U; log(e+K)→1. -/
theorem sqrt_div_bennett_log_tendsto_zero (b : ℝ) {K : ℕ → ℝ}
    (hK : Tendsto K atTop (𝓝 0)) :
    Tendsto (fun n => Real.sqrt (K n) / (Real.log (Real.exp 1 + K n)) ^ b)
      atTop (𝓝 0) := by
  have hs := Real.continuous_sqrt.tendsto 0 |>.comp hK
  have he := (tendsto_const_nhds (x := Real.exp 1)).add hK
  have hl := (Real.continuousAt_log (Real.exp_pos 1).ne').tendsto.comp
    (by simpa only [add_zero] using he)
  have hp := hl.rpow_const (p := b) (Or.inl (by simp))
  have hd := hs.div hp (by simp : (Real.log (Real.exp 1)) ^ b ≠ 0)
  simpa only [Real.sqrt_zero, zero_div] using hd

/-- The literal sparse condition at four moments has exactly the three
conditions printed after the sparse theorem. -/
theorem sparse_regime_four_iff (B : ℕ → ℝ) (p : ℕ → ℕ) :
    (Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) (B n) 4) atTop atTop ∧
      Tendsto (fun n : ℕ => Real.log (polynomialSparseParameter n (p n) (B n) 4) /
        dimensionLog (p n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) 4) atTop (𝓝 0)) ↔
    (Tendsto B atTop atTop ∧
      Tendsto (fun n : ℕ => Real.log (B n) / dimensionLog (p n)) atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) 4) atTop (𝓝 0)) := by
  simp only [polynomialSparseParameter_four]

/-- Above four moments, the sparse parameter measures growth of B_n
relative to the precise positive power of n/L stated in the discussion. -/
theorem polynomialTransitionParameter_above_four_eq_ratio {q : ℝ} (hq : 4 < q)
    {B r : ℝ} (hr : 0 ≤ r) :
    polynomialTransitionParameter B q r = B / r ^ (1 / 2 - 2 / q) := by
  unfold polynomialTransitionParameter polynomialTransitionExponent
  rw [show (2 / q - 1 / 2 : ℝ) = -(1 / 2 - 2 / q) by ring, Real.rpow_neg hr]
  rfl


/-- A diverging sparse parameter above four moments forces envelope
growth, since the fixed-envelope factor tends to zero. -/
theorem envelope_tendsto_atTop_of_sparse_parameter_above_four {q : ℝ} (hq : 4 < q)
    {B r : ℕ → ℝ} (hB : ∀ᶠ n : ℕ in atTop, 0 ≤ B n) (hr : Tendsto r atTop atTop)
    (hK : Tendsto (fun n => polynomialTransitionParameter (B n) q (r n)) atTop atTop) :
    Tendsto B atTop atTop := by
  apply tendsto_atTop_mono' atTop _ hK
  filter_upwards [hB, hr.eventually (eventually_ge_atTop (1 : ℝ))] with n hBn hrn
  have hf := Real.rpow_le_one_of_one_le_of_nonpos hrn (polynomialTransitionExponent_neg hq).le
  simpa only [polynomialTransitionParameter, mul_one] using mul_le_mul_of_nonneg_left hf hBn

/-- Exact exponent form used in the polynomial-dimension discussion. -/
theorem polynomialEnvelopeTransferRate_exponent_identity (n p : ℕ) (B q : ℝ) :
    polynomialEnvelopeTransferRate n p B q =
      B * dimensionLog p ^ (1 + (1 / 2 - 1 / q)) /
        (n : ℝ) ^ (1 / 2 - 1 / q) * dimensionLog n ^ (1 / 2 - 1 / q) := by
  unfold polynomialEnvelopeTransferRate polynomialEnvelopeV
  congr 4
  ring

/-- A logarithmic dimension bound gives exactly the printed
n^-alpha (log n)^(1+2alpha) rate, with an explicit constant. -/
theorem polynomialEnvelopeTransferRate_polylog_bound {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B q C : ℝ} (hB : 0 ≤ B) (hq : 2 < q) (hC : 0 < C)
    (hlog : 1 ≤ Real.log (n : ℝ))
    (hLp : dimensionLog p ≤ C * Real.log (n : ℝ)) :
    polynomialEnvelopeTransferRate n p B q ≤
      (B * C ^ (1 + (1 / 2 - 1 / q)) * (2 : ℝ) ^ (1 / 2 - 1 / q)) *
        ((n : ℝ) ^ (-(1 / 2 - 1 / q)) *
          Real.log (n : ℝ) ^ (1 + 2 * (1 / 2 - 1 / q))) := by
  let α := (1 / 2 : ℝ) - 1 / q
  have hqp : 0 < q := by linarith
  have hα : 0 ≤ α := by
    have h := (div_le_iff₀ hqp).mpr (by linarith : (1 : ℝ) ≤ 1 / 2 * q)
    dsimp [α]
    linarith
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hln : 0 < Real.log (n : ℝ) := zero_lt_one.trans_le hlog
  have hL0 : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hD : dimensionLog n ≤ 2 * Real.log (n : ℝ) := by
    unfold dimensionLog
    rw [Real.log_mul (Real.exp_pos 1).ne' hN.ne', Real.log_exp]
    linarith
  have hpwL := Real.rpow_le_rpow hL0 hLp (by linarith : 0 ≤ 1 + α)
  have hpwD := Real.rpow_le_rpow (zero_le_one.trans (log_exp_mul_nat_ge_one hn)) hD hα
  rw [Real.mul_rpow hC.le hln.le] at hpwL
  rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hln.le] at hpwD
  rw [polynomialEnvelopeTransferRate_exponent_identity]
  change B * dimensionLog p ^ (1 + α) / (n : ℝ) ^ α * dimensionLog n ^ α ≤ _
  calc
    _ ≤ B * (C ^ (1 + α) * Real.log (n : ℝ) ^ (1 + α)) / (n : ℝ) ^ α *
        ((2 : ℝ) ^ α * Real.log (n : ℝ) ^ α) := by
      apply mul_le_mul
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpwL hB) (Real.rpow_nonneg hN.le _))
        hpwD (Real.rpow_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hn)) _)
        (by positivity)
    _ = _ := by
      rw [Real.rpow_neg hN.le]
      have he : Real.log (n : ℝ) ^ (1 + 2 * α) =
          Real.log (n : ℝ) ^ (1 + α) * Real.log (n : ℝ) ^ α := by
        rw [← Real.rpow_add hln]
        congr 1
        ring
      change _ = (B * C ^ (1 + α) * (2 : ℝ) ^ α) *
        (((n : ℝ) ^ α)⁻¹ * Real.log (n : ℝ) ^ (1 + 2 * α))
      rw [he]
      ring

/-- In particular p asymp n^a implies the printed polylogarithmic rate.
Only its upper polynomial bound is needed for this conclusion. -/
theorem polynomialEnvelopeTransferRate_isBigO_polylog {p : ℕ → ℕ} {a B q : ℝ}
    (ha : 0 < a) (hB : 0 ≤ B) (hq : 2 < q)
    (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hpoly : (fun n : ℕ => (p n : ℝ)) =O[atTop] (fun n : ℕ => (n : ℝ) ^ a)) :
    (fun n : ℕ => polynomialEnvelopeTransferRate n (p n) B q) =O[atTop]
      (fun n : ℕ => (n : ℝ) ^ (-(1 / 2 - 1 / q)) *
        Real.log (n : ℝ) ^ (1 + 2 * (1 / 2 - 1 / q))) := by
  obtain ⟨D, hD, hbound⟩ := hpoly.exists_pos
  let C := a + 2 + |Real.log D|
  have hC : 0 < C := by dsimp [C]; positivity
  apply IsBigO.of_bound (B * C ^ (1 + (1 / 2 - 1 / q)) * (2 : ℝ) ^ (1 / 2 - 1 / q))
  have hlogTop : Tendsto (fun n : ℕ => Real.log (n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [hp, hbound.bound, hlogTop.eventually (eventually_ge_atTop (1 : ℝ)),
    eventually_ge_atTop 1] with n hpn hbn hln hn
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hpR : (0 : ℝ) < p n := by exact_mod_cast hpn
  have hbn' : (p n : ℝ) ≤ D * (n : ℝ) ^ a := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (show (0 : ℝ) ≤ p n from Nat.cast_nonneg _),
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) a)] using hbn
  have hlogp := Real.log_le_log hpR hbn'
  rw [Real.log_mul hD.ne' (Real.rpow_pos_of_pos hN a).ne', Real.log_rpow hN] at hlogp
  have hLp : dimensionLog (p n) ≤ C * Real.log (n : ℝ) := by
    unfold dimensionLog
    rw [Real.log_mul (Real.exp_pos 1).ne' hpR.ne', Real.log_exp]
    have hm := mul_nonneg (by positivity : 0 ≤ 1 + |Real.log D|) (sub_nonneg.mpr hln)
    dsimp [C]
    nlinarith [le_abs_self (Real.log D)]
  have ht := polynomialEnvelopeTransferRate_polylog_bound hn hpn hB hq hC hln hLp
  have hrate : 0 ≤ polynomialEnvelopeTransferRate n (p n) B q :=
    polynomialEnvelopeTransferRate_nonneg hn hpn hB q
  have htarget : 0 ≤ (n : ℝ) ^ (-(1 / 2 - 1 / q)) *
      Real.log (n : ℝ) ^ (1 + 2 * (1 / 2 - 1 / q)) := by positivity
  simpa only [Real.norm_eq_abs, abs_of_nonneg hrate, abs_of_nonneg htarget] using ht


theorem polynomialSparseParameter_tendsto_atTop_below_four {B q : ℝ} (hB : 0 < B)
    (hq : 2 < q) (hq4 : q < 4) {p : ℕ → ℕ}
    (hr : Tendsto (fun n : ℕ => (n : ℝ) / dimensionLog (p n)) atTop atTop) :
    Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) B q) atTop atTop :=
  polynomialTransitionParameter_tendsto_atTop hB hq hq4 hr

theorem polynomialSparseParameter_tendsto_zero_above_four {B q : ℝ} (hq : 4 < q)
    {p : ℕ → ℕ} (hr : Tendsto (fun n : ℕ => (n : ℝ) / dimensionLog (p n)) atTop atTop) :
    Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) B q) atTop (𝓝 0) :=
  polynomialTransitionParameter_tendsto_zero hq hr

theorem polynomialSparseRate_four (n p : ℕ) (B : ℝ) :
    polynomialSparseRate n p B 4 = B * dimensionLog p ^ (5 / 4 : ℝ) /
      ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ)) := by
  norm_num [polynomialSparseRate, polynomialSparseParameter]

/-- The displayed ratio in `poly:transition`, for the paper's actual
observation-normalized U, V_q and K_q definitions. -/
theorem polynomialSparseRate_div_coordinateRate {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B q : ℝ} (hB : 0 < B) :
    polynomialSparseRate n p B q / polynomialCoordinateRate n p B =
      Real.sqrt (polynomialSparseParameter n p B q) /
        Real.log (Real.exp 1 + polynomialSparseParameter n p B q) ^ (1 - 1 / q) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hd : 0 < rawPolynomialFourthScale n B := div_pos hB (Real.sqrt_pos.mpr hN)
  have hA : 0 ≤ rawPolynomialEnvelopeScale n B q := by unfold rawPolynomialEnvelopeScale; positivity
  have h := bennettEnvelope_div_base_eq_sqrt_parameter (q := q) hd hA hL
  have hK : bennettPolynomialParameter q (rawPolynomialFourthScale n B)
      (rawPolynomialEnvelopeScale n B q) (dimensionLog p) = polynomialSparseParameter n p B q := by
    rw [bennettPolynomialParameter_eq hd hL]
    exact rawPolynomialParameter_eq hn hB hL
  unfold bennettPolynomialLog at h
  rw [hK] at h
  unfold bennettEnvelopeScale bennettBaseScale at h
  rw [rawPolynomialEnvelopeTerm_eq hn B q, rawPolynomialBaseScale_eq hn hB.le hL] at h
  simpa only [polynomialSparseRate, polynomialCoordinateRate, div_div] using h

theorem polynomialSparseRate_dominates_coordinate_below_four {B q : ℝ}
    (hB : 0 < B) (hq : 2 < q) (hq4 : q < 4) {p : ℕ → ℕ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) / dimensionLog (p n)) atTop atTop) :
    Tendsto (fun n : ℕ => polynomialSparseRate n (p n) B q /
      polynomialCoordinateRate n (p n) B) atTop atTop := by
  have h := sqrt_div_bennett_log_tendsto_atTop (1 - 1 / q)
    (polynomialSparseParameter_tendsto_atTop_below_four hB hq hq4 hr)
  apply h.congr'
  filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
  exact (polynomialSparseRate_div_coordinateRate hn hpn hB).symm

theorem polynomialSparseRate_negligible_to_coordinate_above_four {B q : ℝ}
    (hB : 0 < B) (hq : 4 < q) {p : ℕ → ℕ}
    (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hr : Tendsto (fun n : ℕ => (n : ℝ) / dimensionLog (p n)) atTop atTop) :
    Tendsto (fun n : ℕ => polynomialSparseRate n (p n) B q /
      polynomialCoordinateRate n (p n) B) atTop (𝓝 0) := by
  have h := sqrt_div_bennett_log_tendsto_zero (1 - 1 / q)
    (polynomialSparseParameter_tendsto_zero_above_four (B := B) hq hr)
  apply h.congr'
  filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
  exact (polynomialSparseRate_div_coordinateRate hn hpn hB).symm


/-- The displayed `poly:q4` estimate, obtained from Proposition 3 and the
proved uniform absorption constant, on every actual admissible array. -/
theorem polynomialMoment_four_uniform_bound :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω)
      [IsProbabilityMeasure μ] {n p : ℕ}, 1 ≤ n → 1 ≤ p → ∀ B : ℝ, 1 ≤ B →
      ∀ (X : Fin n → Ω → Vector p), PolynomialIndependentHypotheses μ X 4 B →
      ∀ A : Matrix (Fin p) (Fin p) ℝ,
        A * A.transpose = covariance μ (normalizedObservationSum X) →
      rectangleDistance μ (normalizedObservationSum X) A ≤ C * min 1
        (B * dimensionLog p ^ (5 / 4 : ℝ) /
          ((n : ℝ) ^ (1 / 4 : ℝ) * Real.log (Real.exp 1 + B) ^ (3 / 4 : ℝ))) := by
  obtain ⟨C, hC, hrate⟩ := exists_polynomialBennett_rate_four_bound
  refine ⟨bennettPolynomialConstant 4 * C,
    one_le_mul_of_one_le_of_one_le (one_le_bennettPolynomialConstant 4) hC, ?_⟩
  intro Ω mΩ μ hprob n p hn hp B hB X h A hA
  have hb := bennettPolynomialCLT_observations (μ := μ) hp hn X h.measurable h.independent
    h.centered h.fourth_integrable h.average_second A hA hB (by norm_num : (2 : ℝ) < 4)
    h.envelope_integrable h.envelope_moment h.average_fourth
  have hm := min_one_le_mul_min_one hC (hrate n p hn hp B hB)
  have ht := mul_le_mul_of_nonneg_left hm
    (zero_le_one.trans (one_le_bennettPolynomialConstant 4))
  exact hb.trans (ht.trans_eq (by ring))

/-- The relative-growth interpretation of the actual sparse parameter
above four moments, with no change to the paper's definitions. -/
theorem polynomialSparseParameter_above_four_eq_ratio {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p)
    {B q : ℝ} (hq : 4 < q) :
    polynomialSparseParameter n p B q =
      B / ((n : ℝ) / dimensionLog p) ^ (1 / 2 - 2 / q) := by
  apply polynomialTransitionParameter_above_four_eq_ratio hq
  exact div_nonneg (Nat.cast_nonneg n) (zero_le_one.trans (log_exp_mul_nat_ge_one hp))


/-- The coordinate term controls the fourth root of L/n whenever B,L≥1. -/
theorem dimension_ratio_fourth_root_le_coordinateRate {n p : ℕ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) {B : ℝ} (hB : 1 ≤ B) :
    (dimensionLog p / (n : ℝ)) ^ (1 / 4 : ℝ) ≤ polynomialCoordinateRate n p B := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hL1 : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le hL1
  have hBpow : 1 ≤ B ^ (1 / 2 : ℝ) := Real.one_le_rpow hB (by norm_num)
  have hfactor : 1 ≤ B ^ (1 / 2 : ℝ) * dimensionLog p :=
    one_le_mul_of_one_le_of_one_le hBpow hL1
  rw [Real.div_rpow hL.le hN.le]
  unfold polynomialCoordinateRate
  rw [show (5 / 4 : ℝ) = 1 + 1 / 4 by norm_num, Real.rpow_add hL, Real.rpow_one]
  apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg hN.le _)
  have hm := mul_le_mul_of_nonneg_right hfactor (Real.rpow_nonneg hL.le (1 / 4 : ℝ))
  simpa only [one_mul, mul_assoc] using hm

/-- Under the full sparse assumptions, the coordinate term vanishes;
this intermediate also justifies interpreting n/L as a diverging scale. -/
theorem coordinateRate_tendsto_zero_under_sparse_conditions {B : ℕ → ℝ} {p : ℕ → ℕ} (q : ℝ)
    (hB : ∀ᶠ n : ℕ in atTop, 1 ≤ B n) (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hK : Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) (B n) q) atTop atTop)
    (hR : Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) q) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => polynomialCoordinateRate n (p n) (B n)) atTop (𝓝 0) := by
  have hr := sqrt_div_bennett_log_tendsto_atTop (1 - 1 / q) hK
  have hratio : Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) q /
      polynomialCoordinateRate n (p n) (B n)) atTop atTop := by
    apply hr.congr'
    filter_upwards [hB, hp, eventually_ge_atTop 1] with n hBn hpn hn
    exact (polynomialSparseRate_div_coordinateRate hn hpn (zero_lt_one.trans_le hBn)).symm
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hR
  · filter_upwards [hB, hp, eventually_ge_atTop 1] with n hBn hpn hn
    unfold polynomialCoordinateRate
    have hL := zero_le_one.trans (log_exp_mul_nat_ge_one hpn)
    positivity
  · filter_upwards [hB, hp, eventually_ge_atTop 1, hratio.eventually (eventually_ge_atTop (1 : ℝ))]
      with n hBn hpn hn hrn
    have hN : (0 : ℝ) < n := by exact_mod_cast hn
    have hL : 0 < dimensionLog (p n) := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hpn)
    have hU : 0 < polynomialCoordinateRate n (p n) (B n) := by
      unfold polynomialCoordinateRate
      exact div_pos (mul_pos (Real.rpow_pos_of_pos (zero_lt_one.trans_le hBn) _) (Real.rpow_pos_of_pos hL _))
        (Real.rpow_pos_of_pos hN _)
    exact (one_le_div hU).mp hrn

theorem sample_dimension_ratio_tendsto_atTop_under_sparse_conditions {B : ℕ → ℝ} {p : ℕ → ℕ} (q : ℝ)
    (hB : ∀ᶠ n : ℕ in atTop, 1 ≤ B n) (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hK : Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) (B n) q) atTop atTop)
    (hR : Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) q) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (n : ℝ) / dimensionLog (p n)) atTop atTop := by
  have hU := coordinateRate_tendsto_zero_under_sparse_conditions q hB hp hK hR
  have hroot : Tendsto (fun n : ℕ => (dimensionLog (p n) / (n : ℝ)) ^ (1 / 4 : ℝ))
      atTop (𝓝 0) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hU
    · filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
      exact Real.rpow_nonneg (div_nonneg
        (zero_le_one.trans (log_exp_mul_nat_ge_one hpn)) (Nat.cast_nonneg n)) _
    · filter_upwards [hB, hp, eventually_ge_atTop 1] with n hBn hpn hn
      exact dimension_ratio_fourth_root_le_coordinateRate hn hpn hBn
  have hfour := hroot.pow 4
  have hsmall : Tendsto (fun n : ℕ => dimensionLog (p n) / (n : ℝ)) atTop (𝓝 0) := by
    have hh : Tendsto (fun n : ℕ => ((dimensionLog (p n) / (n : ℝ)) ^ (1 / 4 : ℝ)) ^ 4)
        atTop (𝓝 0) := by simpa using hfour
    apply hh.congr'
    filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
    have hnn : 0 ≤ dimensionLog (p n) / (n : ℝ) := div_nonneg
      (zero_le_one.trans (log_exp_mul_nat_ge_one hpn)) (Nat.cast_nonneg n)
    rw [← Real.rpow_natCast, ← Real.rpow_mul hnn]
    norm_num
  have hpos : ∀ᶠ n : ℕ in atTop, 0 < dimensionLog (p n) / (n : ℝ) := by
    filter_upwards [hp, eventually_ge_atTop 1] with n hpn hn
    exact div_pos (zero_lt_one.trans_le (log_exp_mul_nat_ge_one hpn)) (by exact_mod_cast hn)
  have ht : Tendsto (fun n : ℕ => dimensionLog (p n) / (n : ℝ)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨hsmall, hpos⟩
  simpa only [Function.comp_def, inv_div] using tendsto_inv_nhdsGT_zero.comp ht

/-- The sparse theorem's full vanishing-rate assumptions really force
B_n to diverge above four moments; no extra dimension hypothesis is added. -/
theorem envelope_tendsto_atTop_under_sparse_conditions_above_four {B : ℕ → ℝ} {p : ℕ → ℕ}
    {q : ℝ} (hq : 4 < q)
    (hB : ∀ᶠ n : ℕ in atTop, 1 ≤ B n) (hp : ∀ᶠ n : ℕ in atTop, 1 ≤ p n)
    (hK : Tendsto (fun n : ℕ => polynomialSparseParameter n (p n) (B n) q) atTop atTop)
    (hR : Tendsto (fun n : ℕ => polynomialSparseRate n (p n) (B n) q) atTop (𝓝 0)) :
    Tendsto B atTop atTop := by
  apply envelope_tendsto_atTop_of_sparse_parameter_above_four hq
    (hB.mono (fun _ h => zero_le_one.trans h))
    (sample_dimension_ratio_tendsto_atTop_under_sparse_conditions q hB hp hK hR)
  exact hK

end
end RectangleCLT.Companion.SplitV4.Printed
