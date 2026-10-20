import RectangleCLT.TruncationCoupling
import RectangleCLT.TruncationThirdMoment

/-! The actual normalized truncated observations have fourth-moment sum
at most `64 B4²/n` and aggregate third moment at most `8 B4/sqrt(n)`.
The tail scale does not enter either moment bound. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem boundedIndependentHypotheses_normalizedCenteredTruncation
    {p n : ℕ} {Y : Fin n → Ω → Vector p}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    {u : ℝ} (hu : 0 ≤ u) (hn : 0 < n) (d : Vector p)
    (hd : ∀ j, 0 < d j) (hdlo : ∀ j, 1 / 2 ≤ d j ^ 2) :
    BoundedIndependentHypotheses μ (normalizedCenteredTruncation μ Y u d)
      (4 * u / Real.sqrt (n : ℝ)) := by
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  have hdhalf (j : Fin p) : 1 / 2 ≤ d j := by
    nlinarith [hd j, hdlo j]
  have hmap (i : Fin n) : Measurable
      (fun x : Vector p => fun j => (x j - truncationMean μ (Y i) u j) /
        (d j * Real.sqrt (n : ℝ))) := by
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).sub measurable_const).div_const _
  refine ⟨?_, ?_, ?_, ?_, div_nonneg (mul_nonneg (by norm_num) hu) hsqrt.le⟩
  · intro i
    apply measurable_pi_lambda
    intro j
    exact ((measurable_pi_apply j).comp
      (measurable_centeredTruncateVector (hY i) u)).div_const _
  · have htr := hind.comp (fun _ => truncateVector (p := p) u)
      (fun _ => measurable_truncateVector u)
    exact htr.comp _ hmap
  · intro i j
    change (∫ ω, centeredTruncateVector μ (Y i) u ω j /
      (d j * Real.sqrt (n : ℝ)) ∂μ) = 0
    rw [integral_div, centeredTruncateVector_integral_zero (hY i) hu j, zero_div]
  · intro i
    apply ae_of_all
    intro ω
    apply (pi_norm_le_iff_of_nonneg
      (div_nonneg (mul_nonneg (by norm_num) hu) hsqrt.le)).mpr
    intro j
    change |centeredTruncateVector μ (Y i) u ω j /
      (d j * Real.sqrt (n : ℝ))| ≤ _
    rw [abs_div, abs_of_pos (mul_pos (hd j) hsqrt)]
    apply (div_le_iff₀ (mul_pos (hd j) hsqrt)).mpr
    have heq : (4 * u / Real.sqrt (n : ℝ)) * (d j * Real.sqrt (n : ℝ)) =
        4 * u * d j := by field_simp [ne_of_gt hsqrt]; ring
    rw [heq]
    have hcoord : |centeredTruncateVector μ (Y i) u ω j| ≤ 2 * u := by
      simpa only [Real.norm_eq_abs] using
        (norm_le_pi_norm (centeredTruncateVector μ (Y i) u ω) j).trans
          (norm_centeredTruncateVector_le (Y i) hu ω)
    exact hcoord.trans (by nlinarith [mul_nonneg hu (by linarith [hdhalf j] : 0 ≤ 2 * d j - 1)])

/-- The fourth-moment bound after centering and coordinate normalization. -/
theorem gamma4_normalizedCenteredTruncation_le
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 u : ℝ}
    (hY : ∀ i, Measurable (Y i))
    (hY1 : ∀ i j, Integrable (fun ω => Y i ω j) μ)
    (hY4 : ∀ i j, Integrable (fun ω => Y i ω j ^ 4) μ)
    (hfour : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ n * B4 ^ 2)
    (hn : 0 < n) (d : Vector p) (hd : ∀ j, 0 < d j)
    (hdlo : ∀ j, 1 / 2 ≤ d j ^ 2) :
    gamma4 μ (normalizedCenteredTruncation μ Y u d) ≤ 64 * B4 ^ 2 / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hcenter (j : Fin p) :
      (∑ i, ∫ ω, centeredTruncateVector μ (Y i) u ω j ^ 4 ∂μ) ≤
        16 * n * B4 ^ 2 := by
    calc
      _ ≤ ∑ i, 16 * ∫ ω, Y i ω j ^ 4 ∂μ :=
        Finset.sum_le_sum fun i _ =>
          centeredTruncateVector_fourth_integral_le (hY i) (hY1 i) (hY4 i) u j
      _ = 16 * ∑ i, ∫ ω, Y i ω j ^ 4 ∂μ := by rw [Finset.mul_sum]
      _ ≤ 16 * (n * B4 ^ 2) := mul_le_mul_of_nonneg_left (hfour j) (by norm_num)
      _ = _ := by ring
  unfold gamma4
  apply (Finset.fold_max_le _).mpr
  refine ⟨div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) hnR.le, ?_⟩
  intro j _
  have hd4 : (1 : ℝ) / 4 ≤ d j ^ 4 := by
    nlinarith [hdlo j, sq_nonneg (d j ^ 2 - 1 / 2)]
  have hsqrt4 : Real.sqrt (n : ℝ) ^ 4 = (n : ℝ) ^ 2 := by
    calc
      _ = (Real.sqrt (n : ℝ) ^ 2) ^ 2 := by ring
      _ = _ := by rw [Real.sq_sqrt hnR.le]
  have hden : (n : ℝ) ^ 2 / 4 ≤ (d j * Real.sqrt (n : ℝ)) ^ 4 := by
    rw [mul_pow, hsqrt4]
    nlinarith [mul_le_mul_of_nonneg_right hd4 (sq_nonneg (n : ℝ))]
  have hdenpos : 0 < (d j * Real.sqrt (n : ℝ)) ^ 4 := pow_pos (mul_pos (hd j) hsqrt) _
  have heq (i : Fin n) : (∫ ω, normalizedCenteredTruncation μ Y u d i ω j ^ 4 ∂μ) =
      (∫ ω, centeredTruncateVector μ (Y i) u ω j ^ 4 ∂μ) /
        (d j * Real.sqrt (n : ℝ)) ^ 4 := by
    simp only [normalizedCenteredTruncation, div_pow, integral_div]
  simp_rw [heq]
  rw [← Finset.sum_div]
  apply (div_le_iff₀ hdenpos).mpr
  calc
    _ ≤ 16 * n * B4 ^ 2 := hcenter j
    _ = (64 * B4 ^ 2 / n) * ((n : ℝ) ^ 2 / 4) := by
      field_simp [ne_of_gt hnR]
      <;> ring
    _ ≤ (64 * B4 ^ 2 / n) * (d j * Real.sqrt (n : ℝ)) ^ 4 :=
      mul_le_mul_of_nonneg_left hden (div_nonneg (by positivity) hnR.le)

/-- The normalized third-moment bound uses the actual unit variances. -/
theorem gamma3_normalizedCenteredTruncation_le
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {B4 u : ℝ}
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hY1 : ∀ i j, Integrable (fun ω => Y i ω j) μ)
    (hY4 : ∀ i j, Integrable (fun ω => Y i ω j ^ 4) μ)
    (hfour : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ n * B4 ^ 2)
    (hB : 0 ≤ B4) (hu : 0 ≤ u) (hn : 0 < n) (d : Vector p)
    (hd : ∀ j, 0 < d j) (hdlo : ∀ j, 1 / 2 ≤ d j ^ 2)
    (hunit : ∀ j, covariance μ (sumVector (normalizedCenteredTruncation μ Y u d)) j j = 1) :
    gamma3 μ (normalizedCenteredTruncation μ Y u d) ≤ 8 * B4 / Real.sqrt (n : ℝ) := by
  have hdata := boundedIndependentHypotheses_normalizedCenteredTruncation hY hind hu hn d hd hdlo
  refine (hdata.gamma3_le_sqrt_gamma4 hunit).trans ?_
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  apply (sq_le_sq₀ (Real.sqrt_nonneg _)
    (div_nonneg (mul_nonneg (by norm_num) hB) (Real.sqrt_nonneg _))).mp
  rw [Real.sq_sqrt (gamma4_nonneg μ _)]
  calc
    _ ≤ 64 * B4 ^ 2 / n := gamma4_normalizedCenteredTruncation_le hY hY1 hY4 hfour hn d hd hdlo
    _ = (8 * B4 / Real.sqrt (n : ℝ)) ^ 2 := by
      rw [div_pow, Real.sq_sqrt hnR.le]
      ring

end

end RectangleCLT
