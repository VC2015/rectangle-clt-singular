import RectangleCLTCompanion.SplitV4.PairedNormalization

/-! Actual normalized moment budgets and the raw-observation polynomial
parameters. These identities do not assert a CLT by themselves. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def rawPolynomialEnvelopeScale (n : ℕ) (B q : ℝ) : ℝ :=
  B * (n : ℝ) ^ (-1 / 2 + 1 / q)

def rawPolynomialFourthScale (n : ℕ) (B : ℝ) : ℝ := B / Real.sqrt (n : ℝ)

theorem rawPolynomialEnvelopeScale_rpow {n : ℕ} (hn : 1 ≤ n)
    {B q : ℝ} (hB : 0 ≤ B) (hq : 0 < q) :
    rawPolynomialEnvelopeScale n B q ^ q =
      (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹)^q * B^q := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hinv : (Real.sqrt (n : ℝ))⁻¹ = (n : ℝ)^(-1 / 2 : ℝ) := by
    rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring, Real.rpow_neg hN.le,
      ← Real.sqrt_eq_rpow]
  have hpow : ((Real.sqrt (n : ℝ))⁻¹)^q = (n : ℝ)^((-1/2 : ℝ)*q) := by
    rw [hinv, ← Real.rpow_mul hN.le]
  rw [hpow]
  unfold rawPolynomialEnvelopeScale
  rw [Real.mul_rpow hB (Real.rpow_nonneg hN.le _), ← Real.rpow_mul hN.le]
  have hexp : (-1 / 2 + 1 / q) * q = 1 + (-1 / 2 : ℝ) * q := by
    field_simp
    ring
  rw [hexp, Real.rpow_add hN, Real.rpow_one]
  ring

theorem normalizedSummands_norm_rpow {Ω : Type*} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (q : ℝ) (i : Fin n) (ω : Ω) :
    ‖normalizedSummands X i ω‖^q =
      ((Real.sqrt (n : ℝ))⁻¹)^q * ‖X i ω‖^q := by
  rw [normalizedSummands, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    Real.mul_rpow (inv_nonneg.mpr (Real.sqrt_nonneg _)) (norm_nonneg _)]

theorem normalized_q_envelope_integrable
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (q : ℝ)
    (hI : ∀ i, Integrable (fun ω => ‖X i ω‖^q) μ) (i : Fin n) :
    Integrable (fun ω => ‖normalizedSummands X i ω‖^q) μ := by
  simpa only [normalizedSummands_norm_rpow] using
    (hI i).const_mul (((Real.sqrt (n : ℝ))⁻¹)^q)

theorem normalized_q_envelope_budget
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}
    (X : Fin n → Ω → Vector p) (hn : 1 ≤ n) {B q : ℝ}
    (hB : 0 ≤ B) (hq : 0 < q)
    (hbudget : ∀ i, (∫ ω, ‖X i ω‖^q ∂μ) ≤ B^q) :
    (∑ i, ∫ ω, ‖normalizedSummands X i ω‖^q ∂μ) ≤
      rawPolynomialEnvelopeScale n B q ^ q := by
  calc
    _ = ∑ i, ((Real.sqrt (n : ℝ))⁻¹)^q * (∫ ω, ‖X i ω‖^q ∂μ) := by
      simp_rw [normalizedSummands_norm_rpow, integral_const_mul]
    _ ≤ ∑ _i : Fin n, ((Real.sqrt (n : ℝ))⁻¹)^q * B^q :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hbudget i)
        (Real.rpow_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)) _)
    _ = (n : ℝ) * ((Real.sqrt (n : ℝ))⁻¹)^q * B^q := by simp; ring
    _ = _ := (rawPolynomialEnvelopeScale_rpow hn hB hq).symm

theorem normalized_coordinate_fourth_budget
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} (X : Fin n → Ω → Vector p) (hn : 1 ≤ n) {B : ℝ}
    (hbudget : ∀ j, (1/(n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 4 ∂μ) ≤ B^2)
    (j : Fin p) :
    (∑ i, ∫ ω, normalizedSummands X i ω j ^ 4 ∂μ) ≤
      rawPolynomialFourthScale n B ^ 2 := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  simp_rw [normalizedSummands_fourth_moment]
  rw [← Finset.mul_sum]
  calc
    _ = (1/(n : ℝ)) * ((1/(n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 4 ∂μ) := by
      simp only [div_eq_mul_inv, one_mul, inv_pow]
      ring
    _ ≤ (1/(n : ℝ)) * B^2 := mul_le_mul_of_nonneg_left (hbudget j) (by positivity)
    _ = rawPolynomialFourthScale n B ^ 2 := by
      rw [rawPolynomialFourthScale, div_pow, Real.sq_sqrt hN.le]
      ring

theorem rawPolynomialParameter_eq {n : ℕ} (hn : 1 ≤ n) {B L q : ℝ}
    (hB : 0 < B) (hL : 0 < L) :
    (rawPolynomialEnvelopeScale n B q ^ 2 / rawPolynomialFourthScale n B) *
      L ^ (1 / 2 - 2 / q) = B * ((n : ℝ)/L) ^ (2 / q - 1 / 2) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  let a : ℝ := -1/2 + 1/q
  let e : ℝ := 2/q - 1/2
  have hexp : e = a*2 + 1/2 := by dsimp [a,e]; ring
  have hNe : (n : ℝ)^e = (n : ℝ)^(a*2) * Real.sqrt (n : ℝ) := by
    rw [hexp, Real.rpow_add hN, ← Real.sqrt_eq_rpow]
  have hcoeff : rawPolynomialEnvelopeScale n B q ^ 2 / rawPolynomialFourthScale n B =
      B * (n : ℝ)^e := by
    change (B * (n : ℝ)^a)^2 / (B / Real.sqrt (n : ℝ)) = _
    rw [mul_pow, ← Real.rpow_mul_natCast hN.le, hNe]
    field_simp
    ring
  rw [hcoeff, Real.div_rpow hN.le hL.le]
  have hLe : L ^ (1/2-2/q) = (L^e)⁻¹ := by
    rw [show (1/2-2/q) = -e by dsimp [e]; ring, Real.rpow_neg hL.le]
  rw [hLe]
  ring

theorem rawPolynomialBaseScale_eq {n : ℕ} (hn : 1 ≤ n) {B L : ℝ}
    (hB : 0 ≤ B) (hL : 0 < L) :
    Real.sqrt (rawPolynomialFourthScale n B * L^(5/2 : ℝ)) =
      B^(1/2 : ℝ) * L^(5/4 : ℝ) / (n : ℝ)^(1/4 : ℝ) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hn4 : (Real.sqrt (n : ℝ))^(1/2 : ℝ) = (n : ℝ)^(1/4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hN.le]
    norm_num
  have hL54 : (L^(5/2 : ℝ))^(1/2 : ℝ) = L^(5/4 : ℝ) := by
    rw [← Real.rpow_mul hL.le]
    norm_num
  rw [Real.sqrt_eq_rpow, rawPolynomialFourthScale,
    Real.mul_rpow (div_nonneg hB (Real.sqrt_nonneg _)) (Real.rpow_nonneg hL.le _),
    Real.div_rpow hB (Real.sqrt_nonneg _), hn4, hL54]
  ring

theorem rawPolynomialEnvelopeTerm_eq {n : ℕ} (hn : 1 ≤ n) (B q L : ℝ) :
    rawPolynomialEnvelopeScale n B q * L^(3/2-1/q) =
      B * L^(3/2-1/q) / (n : ℝ)^(1/2-1/q) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  unfold rawPolynomialEnvelopeScale
  rw [show (-1/2+1/q) = -(1/2-1/q) by ring, Real.rpow_neg hN.le]
  ring

end
end RectangleCLT.Companion.SplitV4
