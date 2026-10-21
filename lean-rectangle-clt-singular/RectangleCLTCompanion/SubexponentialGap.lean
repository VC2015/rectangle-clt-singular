import RectangleCLTCompanion.SubexponentialL2
import RectangleCLTCompanion.SubexponentialScaling
import RectangleCLTCompanion.SubexponentialPairGap

/-! The optional pairwise correlation gap survives clipping.  All
perturbations are measured on the original probability space, so no
independence between a clipped sum and its residual is needed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT.Companion

noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {p n : ℕ}

theorem covariance_eq_inner_toLp
    {W : Ω → Vector p}
    (hLp : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hmean : ∀ j, (∫ ω, W ω j ∂μ) = 0) (j k : Fin p) :
    covariance μ W j k =
      @inner ℝ (Lp ℝ 2 μ) _ ((hLp j).toLp (fun ω => W ω j))
        ((hLp k).toLp (fun ω => W ω k)) := by
  simp only [covariance, hmean, zero_mul, sub_zero]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [(hLp j).coeFn_toLp, (hLp k).coeFn_toLp] with ω hj hk
  simp only [hj, hk, RCLike.inner_apply', conj_trivial]

theorem norm_toLp_coordinate_eq_one
    {W : Ω → Vector p}
    (hLp : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hmean : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hunit : ∀ j, covariance μ W j j = 1) (j : Fin p) :
    ‖(hLp j).toLp (fun ω => W ω j)‖ = 1 := by
  have hh := hunit j
  rw [covariance_eq_inner_toLp hLp hmean, real_inner_self_eq_norm_sq] at hh
  nlinarith [norm_nonneg ((hLp j).toLp (fun ω => W ω j))]

/-- Normalization costs at most one additional standard-deviation error. -/
theorem norm_normalized_sub_le {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {c w : E} {d τ : ℝ}
    (hd : 0 < d) (hnorm : ‖c‖ = d)
    (hcw : ‖c - w‖ ≤ τ) (hdiff : |d - 1| ≤ τ) :
    ‖d⁻¹ • c - w‖ ≤ 2 * τ := by
  have hc : ‖d⁻¹ • c - c‖ ≤ τ := by
    have he : d⁻¹ • c - c = (d⁻¹ - 1) • c := by
      rw [sub_smul, one_smul]
    rw [he, norm_smul, Real.norm_eq_abs, hnorm]
    have heq : |d⁻¹ - 1| * d = |d - 1| := by
      calc
        _ = |(d⁻¹ - 1) * d| := by rw [abs_mul, abs_of_pos hd]
        _ = |1 - d| := by congr 1; rw [sub_mul, inv_mul_cancel₀ hd.ne', one_mul]
        _ = _ := abs_sub_comm _ _
    rwa [heq]
  calc
    _ = ‖(d⁻¹ • c - c) + (c - w)‖ := by congr 1; abel
    _ ≤ ‖d⁻¹ • c - c‖ + ‖c - w‖ := norm_add_le _ _
    _ ≤ _ := by linarith

/-- Two centered unit-variance vectors on the same space have covariance
entries stable under coordinatewise `L²` perturbations. -/
theorem covariance_difference_le_two_error
    {W S : Ω → Vector p} {η : ℝ}
    (hW : ∀ j, MemLp (fun ω => W ω j) 2 μ)
    (hS : ∀ j, MemLp (fun ω => S ω j) 2 μ)
    (hmW : ∀ j, (∫ ω, W ω j ∂μ) = 0)
    (hmS : ∀ j, (∫ ω, S ω j ∂μ) = 0)
    (huW : ∀ j, covariance μ W j j = 1)
    (huS : ∀ j, covariance μ S j j = 1)
    (hdist : ∀ j, Real.sqrt (∫ ω, (S ω j - W ω j) ^ 2 ∂μ) ≤ η)
    (j k : Fin p) :
    |covariance μ S j k - covariance μ W j k| ≤ 2 * η := by
  let w := fun j => (hW j).toLp (fun ω => W ω j)
  let s := fun j => (hS j).toLp (fun ω => S ω j)
  have hnormw (j : Fin p) : ‖w j‖ = 1 := norm_toLp_coordinate_eq_one hW hmW huW j
  have hnorms (j : Fin p) : ‖s j‖ = 1 := norm_toLp_coordinate_eq_one hS hmS huS j
  have hdist' (j : Fin p) : ‖s j - w j‖ ≤ η := by
    have hh := hdist j
    rwa [sqrt_integral_sub_sq_eq_norm_toLp (hS j) (hW j)] at hh
  rw [covariance_eq_inner_toLp hS hmS, covariance_eq_inner_toLp hW hmW]
  change |@inner ℝ (Lp ℝ 2 μ) _ (s j) (s k) -
    @inner ℝ (Lp ℝ 2 μ) _ (w j) (w k)| ≤ _
  have he : @inner ℝ (Lp ℝ 2 μ) _ (s j) (s k) -
      @inner ℝ (Lp ℝ 2 μ) _ (w j) (w k) =
      @inner ℝ (Lp ℝ 2 μ) _ (s j - w j) (s k) +
      @inner ℝ (Lp ℝ 2 μ) _ (w j) (s k - w k) := by
    simp only [inner_sub_left, inner_sub_right]
    ring
  rw [he]
  calc
    _ ≤ |@inner ℝ (Lp ℝ 2 μ) _ (s j - w j) (s k)| +
        |@inner ℝ (Lp ℝ 2 μ) _ (w j) (s k - w k)| := abs_add _ _
    _ ≤ ‖s j - w j‖ * ‖s k‖ + ‖w j‖ * ‖s k - w k‖ :=
      add_le_add (abs_real_inner_le_norm _ _) (abs_real_inner_le_norm _ _)
    _ = ‖s j - w j‖ + ‖s k - w k‖ := by rw [hnorms, hnormw, mul_one, one_mul]
    _ ≤ _ := by linarith [hdist' j, hdist' k]

theorem standardizedClipped_coordinate_L2_distance_le [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (hsmall : 2 * K * Real.exp (-u / 2) ≤ 1 / 2) (j : Fin p) :
    let C := sumVector (normalizedClippedRows μ X (K * u))
    let d := fun j => Real.sqrt (covariance μ C j j)
    Real.sqrt (∫ ω, ((d j)⁻¹ * C ω j - normalizedObservationSum X ω j) ^ 2 ∂μ) ≤
      4 * K * Real.exp (-u / 2) := by
  let C := sumVector (normalizedClippedRows μ X (K * u))
  let d := Real.sqrt (covariance μ C j j)
  let W := normalizedObservationSum X
  have hc := normalizedClippedSum_coordinate_memLp_two h hu j
  have hw := normalizedObservationSum_coordinate_memLp_two h j
  have hm : (∫ ω, C ω j ∂μ) = 0 := normalizedClippedSum_coordinate_centered h hu j
  have hnc : ‖hc.toLp (fun ω => C ω j)‖ = d := by
    have he : covariance μ C j j = ∫ ω, C ω j ^ 2 ∂μ := by
      simp only [covariance, hm, zero_mul, sub_zero, pow_two]
    rw [← sqrt_integral_sq_eq_norm_toLp hc, ← he]
  have hdc : 1 / 2 ≤ d := clipped_standardDeviation_ge_half h hu hn hunit hsmall j
  have hdp : 0 < d := lt_of_lt_of_le (by norm_num) hdc
  have hdist : ‖hc.toLp (fun ω => C ω j) - hw.toLp (fun ω => W ω j)‖ ≤
      2 * K * Real.exp (-u / 2) := by
    have hh := clipped_coordinate_L2_distance_le h hu hn j
    rwa [sqrt_integral_sub_sq_eq_norm_toLp hc hw] at hh
  have hd1 : |d - 1| ≤ 2 * K * Real.exp (-u / 2) :=
    clipped_standardDeviation_sub_one_le h hu hn hunit j
  have hh := norm_normalized_sub_le hdp hnc hdist hd1
  change Real.sqrt (∫ ω, (d⁻¹ * C ω j - W ω j) ^ 2 ∂μ) ≤ _
  rw [sqrt_integral_const_mul_sub_sq_eq_norm_toLp hc hw d⁻¹]
  convert hh using 1
  ring

/-- The standardized clipped covariance loses at most four times the
residual standard-deviation bound in its pairwise correlation gap. -/
theorem standardizedClipped_pairGap_lower [IsProbabilityMeasure μ]
    {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (hsmall : 2 * K * Real.exp (-u / 2) ≤ 1 / 2) :
    let C := sumVector (normalizedClippedRows μ X (K * u))
    let d := fun j => Real.sqrt (covariance μ C j j)
    let S := fun ω => diagonalScale (fun j => (d j)⁻¹) (C ω)
    pairGap (covariance μ (normalizedObservationSum X)) -
      8 * K * Real.exp (-u / 2) ≤ pairGap (covariance μ S) := by
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  let C := sumVector (normalizedClippedRows μ X (K * u))
  let d := fun j => Real.sqrt (covariance μ C j j)
  let S := fun ω => diagonalScale (fun j => (d j)⁻¹) (C ω)
  let W := normalizedObservationSum X
  have hC (j : Fin p) : MemLp (fun ω => C ω j) 2 μ :=
    normalizedClippedSum_coordinate_memLp_two h hu j
  have hW (j : Fin p) : MemLp (fun ω => W ω j) 2 μ :=
    normalizedObservationSum_coordinate_memLp_two h j
  have hS (j : Fin p) : MemLp (fun ω => S ω j) 2 μ := (hC j).const_mul _
  have hmC (j : Fin p) : (∫ ω, C ω j ∂μ) = 0 :=
    normalizedClippedSum_coordinate_centered h hu j
  have hmW (j : Fin p) : (∫ ω, W ω j ∂μ) = 0 :=
    normalizedObservationSum_coordinate_centered h j
  have hmS (j : Fin p) : (∫ ω, S ω j ∂μ) = 0 := by
    simp only [S, diagonalScale, integral_const_mul, hmC, mul_zero]
  have hd (j : Fin p) : d j ≠ 0 :=
    (lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 2)
      (clipped_standardDeviation_ge_half h hu hn hunit hsmall j)).ne'
  have hvar (j : Fin p) : covariance μ C j j = (d j) ^ 2 := by
    apply (Real.sq_sqrt _).symm
    rw [covariance_diagonal_eq_variance j (hC j)]
    exact variance_nonneg _ _
  have huS (j : Fin p) : covariance μ S j j = 1 :=
    covariance_standardize_diagonal μ C d hd hvar j
  have hdist (j : Fin p) :
      Real.sqrt (∫ ω, (S ω j - W ω j) ^ 2 ∂μ) ≤
        4 * K * Real.exp (-u / 2) :=
    standardizedClipped_coordinate_L2_distance_le h hu hn hunit hsmall j
  change pairGap (covariance μ W) - 8 * K * Real.exp (-u / 2) ≤ pairGap (covariance μ S)
  apply pairGap_sub_le_of_entrywise_sub_le (covariance μ S) (covariance μ W)
    (by positivity)
  intro j k _
  have hh := covariance_difference_le_two_error hW hS hmW hmS hunit huS hdist j k
  convert hh using 1
  ring

end
end RectangleCLT.Companion
