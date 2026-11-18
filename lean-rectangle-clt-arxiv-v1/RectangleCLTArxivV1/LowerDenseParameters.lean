import RectangleCLTArxivV1.LowerUnmaskedConstruction
import RectangleCLTArxivV1.LowerBoundedCalibration
import RectangleCLTArxivV1.TransfersStatements
import RectangleCLTArxivV1.TransfersEnvelope
import RectangleCLTCompanion.SplitV4.Printed.DenseCalibration

/-! The literal unmasked polynomial amplitude, calibrated from the
width-sensitive rate rather than a worst-dimension comparison scale. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerDenseAmplitude (q B : ℝ) (n m : ℕ) : ℝ :=
  (B / 2) * (Real.log (m : ℝ) / (2 * n)) ^ (-1 / q)

def lowerDenseParameters (q : ℝ) (B : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) : SymmetricFamilyParameters :=
  lowerUnmaskedSequence (fun n => lowerDenseAmplitude q (B n) n (m n)) m n

def lowerDenseWidthRate (q B : ℝ) (n r m : ℕ) : ℝ :=
  B * independentAbsGaussianMean r * dimensionLog (r * m) ^ (1 - 1 / q) /
    (n : ℝ) ^ (1 / 2 - 1 / q)

theorem lowerDenseAmplitude_width_identity {n : ℕ} (hn : 1 ≤ n) {ell : ℝ}
    (hell : 0 < ell) (q B g : ℝ) :
    lowerWidthScale ((B / 2) * (ell / (2 * n)) ^ (-1 / q)) ell g n =
      (2 ^ (1 / q) / 2) * (B * g * ell ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have ht : 0 < ell / (2 * n) := by positivity
  have ha : (ell / (2 * n)) ^ (-1 / q) =
      2 ^ (1 / q) * (n : ℝ) ^ (1 / q) / ell ^ (1 / q) := by
    calc
      _ = ((ell / (2 * n)) ^ (1 / q))⁻¹ := by
        rw [neg_div, Real.rpow_neg ht.le]
      _ = ((ell / (2 * n))⁻¹) ^ (1 / q) := (Real.inv_rpow ht.le _).symm
      _ = (2 * (n : ℝ) / ell) ^ (1 / q) := by congr 1; field_simp
      _ = _ := by rw [Real.div_rpow (mul_nonneg (by norm_num) hn0.le) hell.le,
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hn0.le]
  have hePow : ell ^ (1 - 1 / q) * ell ^ (1 / q) = ell := by
    rw [← Real.rpow_add hell]
    rw [show (1 : ℝ) - 1 / q + 1 / q = 1 by ring, Real.rpow_one]
  have hnPow : (n : ℝ) ^ (1 / 2 - 1 / q) * (n : ℝ) ^ (1 / q) = Real.sqrt n := by
    rw [← Real.rpow_add hn0]
    have hh : (1 / 2 : ℝ) - 1 / q + 1 / q = 1 / 2 := by ring
    rw [hh, ← Real.sqrt_eq_rpow]
  unfold lowerWidthScale
  rw [ha]
  nth_rw 2 [← hePow]
  rw [← hnPow]
  have heNZ := (Real.rpow_pos_of_pos hell (1 / q)).ne'
  have hnNZ := (Real.rpow_pos_of_pos hn0 (1 / q)).ne'
  have hnNZ' := (Real.rpow_pos_of_pos hn0 (1 / 2 - 1 / q)).ne'
  field_simp
  ring

theorem tendsto_lowerDense_raw_width_scale {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q (B n) n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => lowerWidthScale (lowerDenseAmplitude q (B n) n (m n))
      (Real.log (m n : ℝ)) (independentAbsGaussianMean (r n)) n) atTop (𝓝 0) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hbeta : 0 ≤ 1 - 1 / q := by
    have hh : 1 / q < 1 := (div_lt_one hq0).mpr (by linarith)
    linarith
  have hbound : Tendsto (fun n => (2 ^ (1 / q) / 2) * lowerDenseWidthRate q (B n) n (r n) (m n))
      atTop (𝓝 0) := by simpa only [mul_zero] using hsmall.const_mul (2 ^ (1 / q) / 2)
  apply squeeze_zero' _ _ hbound
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
    have hBn : 0 < B n := lt_of_lt_of_le (by norm_num) (hB n)
    have hg0 := independentAbsGaussianMean_nonneg (r n)
    unfold lowerWidthScale lowerDenseAmplitude
    positivity
  · filter_upwards [eventually_ge_atTop 1] with n hn
    have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
    rw [lowerDenseAmplitude, lowerDenseAmplitude_width_identity hn hell]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    unfold lowerDenseWidthRate
    apply div_le_div_of_nonneg_right _ (Real.rpow_nonneg (Nat.cast_nonneg n) _)
    apply mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow hell.le (lower_rareLog_le_dimensionLog (hr n) (by have := hm n; omega)) hbeta)
      (mul_nonneg (by linarith [hB n]) (independentAbsGaussianMean_nonneg _))

theorem lowerDenseAmplitude_moment_identity {theta : ℝ} (htheta : 0 < theta)
    (q B : ℝ) (k : ℕ) :
    theta * ((B / 2) * theta ^ (-1 / q)) ^ k = (B / 2) ^ k * theta ^ (1 - (k : ℝ) / q) := by
  have hh := dense_amplitude_moment_identity htheta q (1 + B / 2) k
  simpa only [add_sub_cancel_left] using hh

theorem tendsto_lowerDense_theta {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q (B n) n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => Real.log (m n : ℝ) / (2 * n)) atTop (𝓝 0) := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hbeta : 0 < 1 - 2 / q := sub_pos.mpr ((div_lt_one hq0).mpr hq)
  have hv := tendsto_lowerUnmasked_raw_variance hr hm hmTop
    (tendsto_lowerDense_raw_width_scale hq hB hr hm hsmall)
  have hpow : Tendsto (fun n : ℕ => (Real.log (m n : ℝ) / (2 * n)) ^ (1 - 2 / q)) atTop (𝓝 0) := by
    apply squeeze_zero' _ _ hv
    · exact Eventually.of_forall (fun n => Real.rpow_nonneg
        (div_nonneg (Real.log_nonneg (by exact_mod_cast (by have := hm n; omega : 1 ≤ m n))) (by positivity)) _)
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
      have ht : 0 < Real.log (m n : ℝ) / (2 * n) := by positivity
      unfold lowerDenseAmplitude
      rw [lowerDenseAmplitude_moment_identity ht q (B n) 2]
      have hB2 : 1 ≤ (B n / 2) ^ 2 := by nlinarith [hB n]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hB2 (Real.rpow_nonneg ht.le (1 - 2 / q))
  have hroot := hpow.rpow_const (Or.inr (one_div_pos.mpr hbeta).le)
  rw [Real.zero_rpow (one_div_pos.mpr hbeta).ne'] at hroot
  apply hroot.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
  have ht : 0 ≤ Real.log (m n : ℝ) / (2 * n) := by positivity
  rw [← Real.rpow_mul ht, mul_one_div_cancel hbeta.ne', Real.rpow_one]

theorem eventually_lowerDenseAmplitude_ge_one {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q (B n) n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, 1 ≤ lowerDenseAmplitude q (B n) n (m n) := by
  have ht := (tendsto_lowerDense_theta hq hB hr hm hmTop hsmall).eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [ht, eventually_ge_atTop 1] with n htheta hn
  have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
  have hθ : 0 < Real.log (m n : ℝ) / (2 * n) := by positivity
  have hp : 1 ≤ (Real.log (m n : ℝ) / (2 * n)) ^ (-1 / q) := by
    rw [neg_div, Real.rpow_neg hθ.le]
    apply (one_le_inv₀ (Real.rpow_pos_of_pos hθ _)).mpr
    exact Real.rpow_le_one hθ.le htheta (by positivity : (0 : ℝ) ≤ 1 / q)
  unfold lowerDenseAmplitude
  nlinarith [hB n]

theorem lowerFamily_polynomialEnvelope_of_factor (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1 ≤ n) {q B : ℝ} (hq : 1 ≤ q)
    (hfactor : P.scale + P.amplitude * P.theta ^ (1 / q) ≤ B) :
    PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) q B := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  have hq0 : 0 < q := zero_lt_one.trans_le hq
  refine ⟨fun _ => measurable_of_finite _, lowerFamilyRawObservations_independent P n r m,
    lowerFamilyRawObservations_centered P, fun _ => integrable_family_finite _ _, ?_, ?_⟩
  · intro j
    simp only [pow_two, lowerFamilyRawObservations_second, lowerFamilyCovariance_unit_diagonal,
      Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    exact one_div_mul_cancel hn0
  · intro i
    have hI : 0 ≤ ∫ z, ‖lowerFamilyRawObservations P i z‖ ^ q ∂lowerFamilyArrayLaw P n r m :=
      integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
    have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI (1 / q))
      ((lowerFamilyRawObservations_Lq_envelope P i hq).trans hfactor) hq0.le
    rwa [← Real.rpow_mul hI, one_div_mul_cancel hq0.ne', Real.rpow_one] at hh

theorem lowerFamily_polynomialFourth_of_moments (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1 ≤ n) {q B : ℝ}
    (henv : PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) q B)
    (hfourth : 1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4 ≤ B ^ 2) :
    PolynomialFourthHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) q B := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (by omega : n ≠ 0)
  refine ⟨henv, fun _ _ => integrable_family_finite _ _, ?_⟩
  intro j
  simp_rw [lowerFamilyRawObservations_fourth]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    ← mul_assoc, one_div_mul_cancel hn0, one_mul]
  exact hfourth

theorem eventually_lowerDense_envelope {q : ℝ} {B : ℕ → ℝ} {r m : ℕ → ℕ}
    (hq : 2 < q) (hB : ∀ n, 2 ≤ B n) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q (B n) n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, PolynomialEnvelopeHypotheses
      (lowerFamilyArrayLaw (lowerDenseParameters q B m n) n (r n) (m n))
      (lowerFamilyRawObservations (lowerDenseParameters q B m n)) q (B n) := by
  have hs := tendsto_lowerDense_raw_width_scale hq hB hr hm hsmall
  have ha := eventually_lowerDenseAmplitude_ge_one hq hB hr hm hmTop hsmall
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hs,eventually_ge_atTop 1]
    with n hfields hn
  apply lowerFamily_polynomialEnvelope_of_factor _ hn (by linarith : 1 ≤ q)
  have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
  have ht : 0 < Real.log (m n : ℝ) / (2 * n) := by positivity
  have hprod : lowerDenseAmplitude q (B n) n (m n) *
      (Real.log (m n : ℝ) / (2 * n)) ^ (1 / q) = B n / 2 := by
    have hh := dense_amplitude_inverse_identity ht q (1 + B n / 2)
    simpa only [lowerDenseAmplitude, add_sub_cancel_left] using hh
  rcases hfields with ⟨htheta, hamp, _⟩
  change (lowerDenseParameters q B m n).theta = _ at htheta
  change (lowerDenseParameters q B m n).amplitude = _ at hamp
  rw [htheta, hamp, hprod]
  have hh := familyScale_le_one (lowerDenseParameters q B m n)
  linarith [hB n]

theorem tendsto_lowerDense_fourth_factor {q B : ℝ} {r m : ℕ → ℕ}
    (hq : 4 < q) (hB : 2 ≤ B) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q B n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => (lowerDenseParameters q (fun _ => B) m n).theta *
      (lowerDenseParameters q (fun _ => B) m n).amplitude ^ 4) atTop (𝓝 0) := by
  have hq2 : 2 < q := by linarith
  have hs := tendsto_lowerDense_raw_width_scale hq2 (fun _ => hB) hr hm hsmall
  have ha := eventually_lowerDenseAmplitude_ge_one hq2 (fun _ => hB) hr hm hmTop hsmall
  have he : 0 < 1 - 4 / q := sub_pos.mpr ((div_lt_one (by linarith : 0 < q)).mpr hq)
  have ht := (tendsto_lowerDense_theta hq2 (fun _ => hB) hr hm hmTop hsmall).rpow_const (Or.inr he.le)
  have hlim := ht.const_mul ((B / 2) ^ 4)
  rw [Real.zero_rpow he.ne', mul_zero] at hlim
  apply hlim.congr'
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hs,eventually_ge_atTop 1]
    with n hfields hn
  have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
  have htheta : 0 < Real.log (m n : ℝ) / (2 * n) := by positivity
  rcases hfields with ⟨hθ, hamp, _⟩
  change (lowerDenseParameters q (fun _ => B) m n).theta = _ at hθ
  change (lowerDenseParameters q (fun _ => B) m n).amplitude = _ at hamp
  rw [hθ, hamp, lowerDenseAmplitude, lowerDenseAmplitude_moment_identity htheta]
  norm_num

theorem eventually_lowerDense_fourth {q B : ℝ} {r m : ℕ → ℕ}
    (hq : 4 < q) (hB : 2 ≤ B) (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n)
    (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerDenseWidthRate q B n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, PolynomialFourthHypotheses
      (lowerFamilyArrayLaw (lowerDenseParameters q (fun _ => B) m n) n (r n) (m n))
      (lowerFamilyRawObservations (lowerDenseParameters q (fun _ => B) m n)) q B := by
  have hq2 : 2 < q := by linarith
  have hs := tendsto_lowerDense_raw_width_scale hq2 (fun _ => hB) hr hm hsmall
  have ha := eventually_lowerDenseAmplitude_ge_one hq2 (fun _ => hB) hr hm hmTop hsmall
  have hv := tendsto_lowerUnmaskedSequence_variance hr hm hmTop ha hs
  have hf := tendsto_lowerDense_fourth_factor hq hB hr hm hmTop hsmall
  have hlim := (((tendsto_const_nhds (x := (1 : ℝ))).add (hv.const_mul 4)).sub
    ((hv.pow 2).const_mul 5)).add hf
  simp only [mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), add_zero, sub_zero] at hlim
  filter_upwards [eventually_lowerDense_envelope hq2 (fun _ => hB) hr hm hmTop hsmall,
    hlim.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)),eventually_ge_atTop 1]
    with n henv hfour hn
  apply lowerFamily_polynomialFourth_of_moments _ hn henv
  have hpi : (lowerDenseParameters q (fun _ => B) m n).pi = 1 := lowerUnmaskedSequence_pi _ _ _
  rw [hpi, mul_one]
  exact hfour.trans (by nlinarith [sq_nonneg (B - 2)] : (2 : ℝ) ≤ B ^ 2)

theorem lowerDense_actual_rate_le_twelve_raw {q B g G ell L : ℝ} {n : ℕ}
    (hq : 2 < q) (hn : 1 ≤ n) (hB : 0 ≤ B) (hg : 0 ≤ g) (hG : G ≤ 2 * g)
    (hell : 0 < ell) (hL0 : 0 ≤ L) (hL : L ≤ 3 * ell) :
    B * G * L ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q) ≤
      12 * lowerWidthScale ((B / 2) * (ell / (2 * n)) ^ (-1 / q)) ell g n := by
  have hq0 : 0 < q := lt_trans (by norm_num) hq
  have hbeta0 : 0 ≤ 1 - 1 / q := by
    have hh : 1 / q < 1 := (div_lt_one hq0).mpr (by linarith)
    linarith
  have hbeta1 : 1 - 1 / q ≤ 1 := by
    have hh : (0 : ℝ) ≤ 1 / q := by positivity
    linarith
  have h3 : (3 : ℝ) ^ (1 - 1 / q) ≤ 3 := by
    simpa only [Real.rpow_one] using
      Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 3) hbeta1
  have hLPow : L ^ (1 - 1 / q) ≤ 3 * ell ^ (1 - 1 / q) := by
    have hh := Real.rpow_le_rpow hL0 hL hbeta0
    rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 3) hell.le] at hh
    exact hh.trans (mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hell.le _))
  have hprod := mul_le_mul (mul_le_mul_of_nonneg_left hG hB) hLPow
    (Real.rpow_nonneg hL0 _) (mul_nonneg hB (mul_nonneg (by norm_num) hg))
  have hquot := div_le_div_of_nonneg_right hprod (Real.rpow_nonneg (Nat.cast_nonneg n) (1 / 2 - 1 / q))
  let X := B * g * ell ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)
  have hX : 0 ≤ X := by dsimp [X]; positivity
  have hcoef : (1 / 2 : ℝ) ≤ 2 ^ (1 / q) / 2 := by
    have hh := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity : (0 : ℝ) ≤ 1 / q)
    linarith
  have hscaled := mul_le_mul_of_nonneg_right hcoef hX
  have hquot' : B * G * L ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q) ≤ 6 * X := by
    convert hquot using 1
    dsimp [X]
    ring
  rw [lowerDenseAmplitude_width_identity hn hell]
  change _ ≤ 12 * ((2 ^ (1 / q) / 2) * X)
  linarith only [hquot', hscaled]

/-- Theorem7(i), with the explicitly constructed finite iid symmetric
law, genuine envelope membership, actual Gaussian width and discrepancy.
The positive constant precedes the dimensions and varying envelope. -/
theorem theorem_7_polynomial_envelope_lower (q : ℝ) (hq : 2 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℕ → ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) →
      (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      Tendsto (fun n => lowerDenseWidthRate q (B n) n (r n) (m n)) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q B m n)
        (r n) (m n)) / independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerDenseParameters q B m n) n (r n) (m n) ∧
        PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw (lowerDenseParameters q B m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerDenseParameters q B m n)) q (B n) ∧
        c * (B n * gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q B m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) ≤
          lowerFamilyShiftedCDFDifference (lowerDenseParameters q B m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c * (B n * gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q B m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) ≤
          lowerFamilyComparisonDistance (lowerDenseParameters q B m n) n (r n) (m n) := by
  obtain ⟨c, hc, hdetect⟩ := exists_lowerUnmaskedSequence_detection_constant
  refine ⟨c / 12, by positivity, ?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hsmall
  have hs := tendsto_lowerDense_raw_width_scale hq hB hr hm hsmall
  have ha := eventually_lowerDenseAmplitude_ge_one hq hB hr hm hmTop hsmall
  have hwidth := lowerUnmaskedSequence_width_profile hr hm hmTop ha hs
  refine ⟨hwidth, ?_⟩
  have hlog := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hmTop)
  have hdet := hdetect (fun n => lowerDenseAmplitude q (B n) n (m n)) r m hr hm hrm hmTop ha hs
  filter_upwards [hdet, eventually_lowerDense_envelope hq hB hr hm hmTop hsmall,
    eventually_lowerUnmaskedSequence_properties (fun n => lowerDenseAmplitude q (B n) n (m n)) hr hm,
    hwidth.eventually (eventually_le_nhds (by norm_num : (1 : ℝ) < 2)),
    hlog.eventually (eventually_ge_atTop 1), eventually_ge_atTop 1]
    with n hdn henv hprop hG hnL hn
  have hgpos : 0 < independentAbsGaussianMean (r n) :=
    (show 0 < Real.sqrt (2 / Real.pi) by positivity).trans_le (independentAbsGaussianMean_lower (hr n))
  have hG' := (div_le_iff₀ hgpos).mp hG
  have htarget := lowerDense_actual_rate_le_twelve_raw (B := B n) hq hn (by linarith [hB n]) hgpos.le hG'
    (zero_lt_one.trans_le hnL) (zero_le_one.trans (log_exp_mul_nat_ge_one (by nlinarith [hr n,hm n] : 1 ≤ r n*m n)))
    (lower_dimensionLog_le_three_rareLog (hr n) (hrm n) hnL)
  have hscaled := mul_le_mul_of_nonneg_left htarget (div_nonneg hc.le (by norm_num : (0 : ℝ) ≤ 12))
  refine ⟨hprop, henv, ?_, ?_⟩
  · apply hscaled.trans
    convert hdn.1 using 1
    dsimp only [lowerDenseAmplitude, Function.comp_apply]
    ring
  · apply hscaled.trans
    convert hdn.2 using 1
    dsimp only [lowerDenseAmplitude, Function.comp_apply]
    ring

/-- Theorem7(ii): at a fixed envelope andq>4 the same actual
construction also has the separate coordinate fourth-moment budget. -/
theorem theorem_7_fixed_envelope_fourth_lower (q : ℝ) (hq : 4 < q) :
    ∃ c : ℝ, 0 < c ∧ ∀ (B : ℝ) (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      2 ≤ B → (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) →
      (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      Tendsto (fun n => lowerDenseWidthRate q B n (r n) (m n)) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q (fun _ => B) m n)
        (r n) (m n)) / independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerDenseParameters q (fun _ => B) m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerDenseParameters q (fun _ => B) m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerDenseParameters q (fun _ => B) m n)) q B ∧
        c * (B * gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q (fun _ => B) m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) ≤
          lowerFamilyShiftedCDFDifference (lowerDenseParameters q (fun _ => B) m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c * (B * gaussianMaximumMean (lowerFamilyGaussianFactor (lowerDenseParameters q (fun _ => B) m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) ≤
          lowerFamilyComparisonDistance (lowerDenseParameters q (fun _ => B) m n) n (r n) (m n) := by
  obtain ⟨c, hc, hlower⟩ := theorem_7_polynomial_envelope_lower q (by linarith : 2 < q)
  refine ⟨c, hc, ?_⟩
  intro B r m _ _ hB hr hm hrm hmTop hsmall
  obtain ⟨hw, hevent⟩ := hlower (fun _ => B) r m (fun _ => hB) hr hm hrm hmTop hsmall
  refine ⟨hw, ?_⟩
  filter_upwards [hevent, eventually_lowerDense_fourth hq hB hr hm hmTop hsmall] with n hn hfour
  exact ⟨hn.1, hfour, hn.2.2⟩

/-- The logarithmic upper comparison stated after Theorem7 is the
actual new Theorem2(i) applied to these same observations. -/
theorem exists_lowerDense_upper_constant (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : SymmetricFamilyParameters) (n r m : ℕ) (B : ℝ),
      1 ≤ n → 1 ≤ r → 1 ≤ m → 1 ≤ B →
      PolynomialEnvelopeHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) q B →
      lowerFamilyComparisonDistance P n r m ≤
        C * dimensionLog n ^ (1 / 2 - 1 / q) *
          (B * gaussianMaximumMean (lowerFamilyGaussianFactor P r m) *
            dimensionLog (r * m) ^ (1 - 1 / q) / (n : ℝ) ^ (1 / 2 - 1 / q)) := by
  obtain ⟨C, hC, hbound⟩ := theorem_2_i_intrinsic q hq
  refine ⟨C, hC, ?_⟩
  intro P n r m B hn hr hm hB hX
  have hW : normalizedObservationSum (lowerFamilyRawObservations P : Fin n →
      (Fin n → LowerFamilySeed r m) → Vector (r * m)) = sumVector (lowerFamilyNormalizedObservations P) := by
    funext z
    simp only [normalizedObservationSum, sumVector, lowerFamilyNormalizedObservations, Finset.smul_sum, one_div]
  have hA : lowerFamilyGaussianFactor P r m * (lowerFamilyGaussianFactor P r m).transpose =
      covariance (lowerFamilyArrayLaw P n r m) (normalizedObservationSum (lowerFamilyRawObservations P)) := by
    rw [hW, lowerFamilyNormalizedObservations_covariance P hn]
    exact lowerFamilyGaussianFactor_gram P r m
  have hh := hbound (r * m) n (by nlinarith : 1 ≤ r * m) hn B hB
    (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) hX (lowerFamilyGaussianFactor P r m) hA
  rw [hW] at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le).trans_eq
  unfold polynomialEnvelopeWidthRate
  ring

end
end RectangleCLTArxivV1
