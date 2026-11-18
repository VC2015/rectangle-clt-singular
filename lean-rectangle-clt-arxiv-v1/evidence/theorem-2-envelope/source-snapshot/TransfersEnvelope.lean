import RectangleCLTArxivV1.TransfersEnvelopeThreshold
import RectangleCLTArxivV1.TransfersMoments

/-! The envelope-only part of the new width-dependent Theorem 2. The
probabilistic cutoff proof is new; only the checked scalar cutoff algebra
from the archive is reused. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
  RectangleCLT.Companion.SplitV4
open scoped BigOperators
universe u

/-- Exact relation between the new width-dependent rate and the archived
scalar cutoff algebra. -/
theorem polynomialEnvelopeWidthRate_eq_scaled_old {n p : ℕ} (hp : 1 ≤ p)
    (B q g : ℝ) :
    polynomialEnvelopeWidthRate n p B q g =
      (g / Real.sqrt (dimensionLog p)) * polynomialEnvelopeTransferRate n p B q := by
  have hL : 0 < dimensionLog p := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hs : Real.sqrt (dimensionLog p) ≠ 0 := (Real.sqrt_pos.mpr hL).ne'
  unfold polynomialEnvelopeWidthRate polynomialEnvelopeTransferRate polynomialEnvelopeV
  rw [show (3 / 2 : ℝ) - 1 / q = (1 - 1 / q) + 1 / 2 by ring,
    Real.rpow_add hL, ← Real.sqrt_eq_rpow]
  field_simp [hs]
  ring_nf
  simp only [mul_assoc, mul_inv_cancel₀ hs, mul_one]

noncomputable def polynomialEnvelopeIntrinsicConstant : ℝ :=
  4 * conditionalIntrinsicTransferConstant * max 1 (1 / Real.sqrt (2 / Real.pi))

theorem polynomialEnvelopeIntrinsicConstant_pos : 0 < polynomialEnvelopeIntrinsicConstant := by
  have hc := zero_lt_one.trans_le one_le_conditionalIntrinsicTransferConstant
  have hm : (0 : ℝ) < max 1 (1 / Real.sqrt (2 / Real.pi)) := zero_lt_one.trans_le (le_max_left _ _)
  unfold polynomialEnvelopeIntrinsicConstant
  positivity

/-- The actual envelope-only CLT, with no coordinate fourth-moment
assumption, at the precise Gaussian width of the original covariance. -/
theorem polynomialEnvelope_intrinsic_CLT
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} (hp : 1 ≤ p) (hn : 1 ≤ n) {B q : ℝ} (hB : 1 ≤ B) (hq : 2 < q)
    (X : Fin n → Ω → Vector p) (h : PolynomialEnvelopeHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X)) :
    rectangleDistance μ (normalizedObservationSum X) A ≤
      polynomialEnvelopeIntrinsicConstant * min 1
        (polynomialEnvelopeWidthRate n p B q (gaussianMaximumMean A)) := by
  let k := Real.sqrt (2 / Real.pi)
  let g := gaussianMaximumMean A
  let L := dimensionLog p
  let R := polynomialEnvelopeWidthRate n p B q g
  let K := max 1 (1 / k)
  have hk : 0 < k := by dsimp [k]; positivity
  have hg : 0 ≤ g := gaussianMaximumMean_nonneg A
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have hs : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL
  have hR : 0 ≤ R := polynomialEnvelopeWidthRate_nonneg hn hp (zero_le_one.trans hB) hg q
  have hK : 1 ≤ K := le_max_left _ _
  have hC : 1 ≤ conditionalIntrinsicTransferConstant := one_le_conditionalIntrinsicTransferConstant
  have hunit (j : Fin p) : (A * A.transpose) j j = 1 := by rw [hA]; exact h.unit_covariance hq j
  have hglow : k ≤ g := sqrt_two_div_pi_le_gaussianMaximumMean hp A hunit
  by_cases hlarge : dimensionLog p * dimensionLog n ≤ (n : ℝ)
  · let T := polynomialTruncationThreshold n p B q
    have hT : 2 * B ≤ T := polynomialTruncationThreshold_ge hp hn (zero_le_one.trans hB)
      (by linarith : 0 < q) hlarge
    let ν : Fin n → Measure (Vector p) := fun i => μ.map (X i)
    haveI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (h.measurable i).aemeasurable
    have hm := h.conditional_marginal_inputs hq hB hT
    have hAf : A * A.transpose = originalAverageCovariance ν :=
      hA.trans (h.covariance_eq_originalAverageCovariance hq hB hn)
    have hb := conditionalPolynomial_intrinsic_threshold ν hm hp hn hB A hAf hunit
    rw [normalized_product_rectangleDistance_eq μ X h.measurable h.independent] at hb
    have hr := mul_le_mul_of_nonneg_left (polynomialTruncation_threshold_rate_le hp hn
      (zero_lt_one.trans_le hB) hq) (div_nonneg hg hs.le)
    have hr' : (g / Real.sqrt L) * conditionalPolynomialThresholdRate n p B T q ≤ 4 * R := by
      rw [show R = (g / Real.sqrt L) * polynomialEnvelopeTransferRate n p B q from
        polynomialEnvelopeWidthRate_eq_scaled_old hp B q g]
      convert hr using 1; ring
    have hcap := min_one_le_mul_min_one (by norm_num : (1 : ℝ) ≤ 4) hr'
    have hfinal := hb.trans (mul_le_mul_of_nonneg_left hcap (zero_le_one.trans hC))
    have hscale : 4 * conditionalIntrinsicTransferConstant ≤ polynomialEnvelopeIntrinsicConstant := by
      unfold polynomialEnvelopeIntrinsicConstant
      exact le_mul_of_one_le_right (by linarith : 0 ≤ 4 * conditionalIntrinsicTransferConstant) hK
    exact hfinal.trans (by
      convert mul_le_mul_of_nonneg_right hscale (le_min zero_le_one hR) using 1; ring)
  · have hsmall : (n : ℝ) ≤ dimensionLog p * dimensionLog n := le_of_not_ge hlarge
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hratio : 1 ≤ (dimensionLog p * dimensionLog n) / (n : ℝ) := (one_le_div hnR).mpr hsmall
    have ha : 0 ≤ (1 / 2 : ℝ) - 1 / q := by
      have hqp : 0 < q := by linarith
      have hrec : 1 / q ≤ (1 / 2 : ℝ) := (div_le_iff₀ hqp).mpr (by linarith)
      linarith
    have hpw := Real.one_le_rpow hratio ha
    have hOld : L ≤ polynomialEnvelopeTransferRate n p B q := by
      rw [polynomialEnvelopeTransferRate_eq_ratio hp hn]
      have hbL : L ≤ B * L := le_mul_of_one_le_left hL.le hB
      exact hbL.trans (le_mul_of_one_le_right (mul_nonneg (zero_le_one.trans hB) hL.le) hpw)
    have hlow : k ≤ R := by
      rw [show R = (g / Real.sqrt L) * polynomialEnvelopeTransferRate n p B q from
        polynomialEnvelopeWidthRate_eq_scaled_old hp B q g]
      have hh := mul_le_mul_of_nonneg_left hOld (div_nonneg hg hs.le)
      have hs1 : 1 ≤ Real.sqrt L := Real.one_le_sqrt.mpr hL1
      have hs2 : (Real.sqrt L) ^ 2 = L := Real.sq_sqrt hL.le
      have heq : (g / Real.sqrt L) * L = g * Real.sqrt L := by
        calc
          _ = (g * L) / Real.sqrt L := by ring
          _ = _ := by
            apply (div_eq_iff hs.ne').mpr
            nlinarith only [congrArg (fun x => g * x) hs2]
      rw [heq] at hh
      exact hglow.trans ((le_mul_of_one_le_right hg hs1).trans hh)
    have hone : 1 ≤ K * min 1 R := by
      by_cases hRone : R ≤ 1
      · rw [min_eq_right hRone]
        have hh := mul_le_mul_of_nonneg_left hlow (inv_nonneg.mpr hk.le)
        have hh' : 1 ≤ (1 / k) * R := by simpa only [one_div, inv_mul_cancel₀ hk.ne'] using hh
        exact hh'.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hR)
      · rw [min_eq_left (le_of_not_ge hRone), mul_one]
        exact hK
    have hsC : K ≤ polynomialEnvelopeIntrinsicConstant := by
      unfold polynomialEnvelopeIntrinsicConstant
      exact le_mul_of_one_le_left (zero_le_one.trans hK) (by linarith : 1 ≤ 4 * conditionalIntrinsicTransferConstant)
    exact (rectangleDistance_le_one _ _ _).trans (hone.trans
      (mul_le_mul_of_nonneg_right hsC (le_min zero_le_one hR)))

/-- Theorem 2(i), with its constant fixed before all dimensions, arrays
and probability models. -/
theorem theorem_2_i_intrinsic (q : ℝ) (hq : 2 < q) :
    ∃ C : ℝ, 0 < C ∧ PolynomialEnvelopeBound.{u} q C := by
  refine ⟨polynomialEnvelopeIntrinsicConstant, polynomialEnvelopeIntrinsicConstant_pos, ?_⟩
  intro p n hp hn B hB Ω mΩ μ hprob X hX A hA
  exact polynomialEnvelope_intrinsic_CLT μ hp hn hB hq X hX A hA

end RectangleCLTArxivV1
