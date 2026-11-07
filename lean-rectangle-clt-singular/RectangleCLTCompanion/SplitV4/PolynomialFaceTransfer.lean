import RectangleCLTCompanion.SplitV4.PolynomialMain
import RectangleCLTCompanion.SplitV4.OrliczFaceTransfer

/-!
# Polynomial polyhedral transfer

The standardized face map preserves the actual array class.  The fourth
moment estimate averages over observations before using the coordinate
budget; it never replaces that budget by a sum of coordinate maxima.
The final bound concerns the original polyhedral probabilities, including
singular covariance matrices and dependent coordinates within each row.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

variable {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ]
  {X : Fin n → Ω → Vector p} {q B : ℝ}

theorem PolynomialIndependentHypotheses.coordinate_memLp_two
    (h : PolynomialIndependentHypotheses μ X q B) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => X i ω j) 2 μ :=
  coordinate_memLp_two_of_fourth_moment μ _
    ((measurable_pi_apply j).comp (h.measurable i)) (h.fourth_integrable i j)

theorem PolynomialIndependentHypotheses.projected_centered
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) (i : Fin n) (α : Fin m) :
    (∫ ω, M.mulVec (X i ω) α ∂μ) = 0 := by
  unfold Matrix.mulVec dotProduct
  rw [integral_finset_sum Finset.univ (fun j _ =>
    ((h.coordinate_memLp_two i j).integrable (by norm_num)).const_mul _)]
  simp only [integral_const_mul, h.centered, mul_zero, Finset.sum_const_zero]

theorem PolynomialIndependentHypotheses.projected_coordinate_memLp_two
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) (i : Fin n) (α : Fin m) :
    MemLp (fun ω => M.mulVec (X i ω) α) 2 μ := by
  have he : (fun ω => M.mulVec (X i ω) α) =
      ∑ j, (fun ω => M α j * X i ω j) := by
    funext ω
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply]
  rw [he]
  exact memLp_finset_sum' Finset.univ
    (fun j _ => (h.coordinate_memLp_two i j).const_mul (M α j))

theorem polynomial_projected_covariance
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) :
    covariance μ (normalizedObservationSum (fun i ω => M.mulVec (X i ω))) =
      M * covariance μ (normalizedObservationSum X) * M.transpose := by
  rw [normalizedObservationSum_mulVec]
  apply covariance_mulVec_of_centered_memLp
  · simpa only [sumVector_normalizedSummands] using
      memLp_sumVector_coordinate (normalizedSummands_coordinate_memLp_two h.coordinate_memLp_two)
  · simpa only [sumVector_normalizedSummands] using
      integral_sumVector_coordinate_zero
        (fun i j => ((normalizedSummands_coordinate_memLp_two h.coordinate_memLp_two i j).integrable
          (by norm_num))) (normalizedSummands_centered h.centered)

theorem polynomial_projected_average_second
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ)
    (hunit : ∀ α, (M * covariance μ (normalizedObservationSum X) * M.transpose) α α = 1)
    (α : Fin m) :
    (1 / (n : ℝ)) * (∑ i, ∫ ω, M.mulVec (X i ω) α ^ 2 ∂μ) = 1 := by
  have hc := normalizedSummands_covariance_diagonal
    (h.independent.comp (fun _ => M.mulVec) (fun _ => measurable_rectangular_mulVec M))
    (h.projected_coordinate_memLp_two M) (h.projected_centered M) α
  change covariance μ (sumVector (normalizedSummands (fun i ω => M.mulVec (X i ω)))) α α = _ at hc
  rw [sumVector_normalizedSummands, polynomial_projected_covariance h M, hunit α] at hc
  exact hc.symm

theorem polynomial_projected_average_second_le
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ} (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (α : Fin m) :
    (1 / (n : ℝ)) * (∑ i, ∫ ω, M.mulVec (X i ω) α ^ 2 ∂μ) ≤ J^2 := by
  have hb (i : Fin n) : (∫ ω, M.mulVec (X i ω) α ^ 2 ∂μ) ≤
      J * ∑ j, |M α j| * (∫ ω, X i ω j ^ 2 ∂μ) := by
    calc
      _ ≤ ∫ ω, J * ∑ j, |M α j| * X i ω j ^ 2 ∂μ :=
        integral_mono (h.projected_coordinate_memLp_two M i α).integrable_sq
          ((integrable_finset_sum Finset.univ (fun j _ =>
            (h.coordinate_memLp_two i j).integrable_sq.const_mul _)).const_mul _)
          (fun ω => mulVec_sq_le_weighted_coordinate_squares M J hM (X i ω) α)
      _ = _ := by
        rw [integral_const_mul, integral_finset_sum Finset.univ
          (fun j _ => (h.coordinate_memLp_two i j).integrable_sq.const_mul _)]
        simp only [integral_const_mul]
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ i, J * ∑ j, |M α j| * (∫ ω, X i ω j ^ 2 ∂μ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (by positivity)
    _ = J * ∑ j, |M α j| * ((1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 2 ∂μ) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ = J * ∑ j, |M α j| := by simp only [h.average_second, mul_one]
    _ ≤ J * J := mul_le_mul_of_nonneg_left (hM α) hJ
    _ = J^2 := by ring

/-- Unit projected variance forces every common row-l1 bound to be at least
one. Thus Corollary 3 does not acquire an additional scale assumption. -/
theorem one_le_polynomial_projection_bound
    (h : PolynomialIndependentHypotheses μ X q B) (hm : 1 ≤ m)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ}
    (hM : ∀ α, (∑ j, |M α j|) ≤ J)
    (hunit : ∀ α, (M * covariance μ (normalizedObservationSum X) * M.transpose) α α = 1) :
    1 ≤ J := by
  let α : Fin m := ⟨0, by omega⟩
  have hJ : 0 ≤ J := (Finset.sum_nonneg (fun j _ => abs_nonneg (M α j))).trans (hM α)
  have hb := polynomial_projected_average_second_le h M hJ hM α
  rw [polynomial_projected_average_second h M hunit α] at hb
  nlinarith

theorem polynomial_projected_fourth_integrable
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ} (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (i : Fin n) (α : Fin m) :
    Integrable (fun ω => M.mulVec (X i ω) α ^ 4) μ := by
  have hi : Integrable (fun ω => J^3 * ∑ j, |M α j| * X i ω j ^ 4) μ :=
    (integrable_finset_sum Finset.univ (fun j _ =>
      (h.fourth_integrable i j).const_mul _)).const_mul _
  apply hi.mono' (((measurable_pi_apply α).comp
    ((measurable_rectangular_mulVec M).comp (h.measurable i))).pow_const 4).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    change ‖M.mulVec (X i ω) α ^ 4‖ ≤ _
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity :
      0 ≤ M.mulVec (X i ω) α ^ 4)] using
        mulVec_fourth_le_weighted_coordinate_fourths M J hJ hM (X i ω) α

theorem polynomial_projected_average_fourth
    (h : PolynomialIndependentHypotheses μ X q B)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ} (hJ : 0 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (α : Fin m) :
    (1 / (n : ℝ)) * (∑ i, ∫ ω, M.mulVec (X i ω) α ^ 4 ∂μ) ≤ (J^2 * B)^2 := by
  have hb (i : Fin n) : (∫ ω, M.mulVec (X i ω) α ^ 4 ∂μ) ≤
      J^3 * ∑ j, |M α j| * (∫ ω, X i ω j ^ 4 ∂μ) := by
    calc
      _ ≤ ∫ ω, J^3 * ∑ j, |M α j| * X i ω j ^ 4 ∂μ :=
        integral_mono (polynomial_projected_fourth_integrable h M hJ hM i α)
          ((integrable_finset_sum Finset.univ (fun j _ =>
            (h.fourth_integrable i j).const_mul _)).const_mul _)
          (fun ω => mulVec_fourth_le_weighted_coordinate_fourths M J hJ hM (X i ω) α)
      _ = _ := by
        rw [integral_const_mul, integral_finset_sum Finset.univ
          (fun j _ => (h.fourth_integrable i j).const_mul _)]
        simp only [integral_const_mul]
  calc
    _ ≤ (1 / (n : ℝ)) * ∑ i, J^3 * ∑ j, |M α j| * (∫ ω, X i ω j ^ 4 ∂μ) :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun i _ => hb i)) (by positivity)
    _ = J^3 * ∑ j, |M α j| * ((1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 4 ∂μ) := by
      simp only [Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro i _
      ring
    _ ≤ J^3 * ∑ j, |M α j| * B^2 :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun j _ =>
        mul_le_mul_of_nonneg_left (h.average_fourth j) (abs_nonneg _))) (by positivity)
    _ ≤ J^3 * (J * B^2) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right (hM α) (sq_nonneg _)) (by positivity)
    _ = (J^2 * B)^2 := by ring

theorem polynomial_projected_envelope_moment
    (h : PolynomialIndependentHypotheses μ X q B) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ} (hJ : 1 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J) (i : Fin n) :
    Integrable (fun ω => ‖M.mulVec (X i ω)‖^q) μ ∧
      (∫ ω, ‖M.mulVec (X i ω)‖^q ∂μ) ≤ (J^2 * B)^q := by
  have hJ0 : 0 ≤ J := zero_le_one.trans hJ
  have hp (ω : Ω) : ‖M.mulVec (X i ω)‖^q ≤ J^q * ‖X i ω‖^q := by
    rw [← Real.mul_rpow hJ0 (norm_nonneg _)]
    exact Real.rpow_le_rpow (norm_nonneg _) (norm_mulVec_le_of_row_l1 M J hJ0 hM _) hq
  have hi : Integrable (fun ω => ‖M.mulVec (X i ω)‖^q) μ :=
    ((h.envelope_integrable i).const_mul (J^q)).mono'
      ((((measurable_rectangular_mulVec M).comp (h.measurable i)).norm).pow_const q).aestronglyMeasurable
      (ae_of_all _ fun ω => by
        change ‖‖M.mulVec (X i ω)‖^q‖ ≤ _
        rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _)]
        exact hp ω)
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ ω, J^q * ‖X i ω‖^q ∂μ :=
      integral_mono hi ((h.envelope_integrable i).const_mul _) hp
    _ = J^q * (∫ ω, ‖X i ω‖^q ∂μ) := integral_const_mul _ _
    _ ≤ J^q * B^q := mul_le_mul_of_nonneg_left (h.envelope_moment i) (by positivity)
    _ = (J*B)^q := (Real.mul_rpow hJ0 hB).symm
    _ ≤ (J^2*B)^q := Real.rpow_le_rpow (mul_nonneg hJ0 hB)
      (mul_le_mul_of_nonneg_right (by nlinarith) hB) hq

theorem polynomialIndependent_projected
    (h : PolynomialIndependentHypotheses μ X q B) (hq : 0 ≤ q) (hB : 0 ≤ B)
    (M : Matrix (Fin m) (Fin p) ℝ) {J : ℝ} (hJ : 1 ≤ J)
    (hM : ∀ α, (∑ j, |M α j|) ≤ J)
    (hunit : ∀ α, (M * covariance μ (normalizedObservationSum X) * M.transpose) α α = 1) :
    PolynomialIndependentHypotheses μ (fun i ω => M.mulVec (X i ω)) q (J^2*B) :=
  ⟨fun i => (measurable_rectangular_mulVec M).comp (h.measurable i),
    h.independent.comp (fun _ => M.mulVec) (fun _ => measurable_rectangular_mulVec M),
    h.projected_centered M,
    fun i => (polynomial_projected_envelope_moment h hq hB M hJ hM i).1,
    polynomial_projected_fourth_integrable h M (zero_le_one.trans hJ) hM,
    polynomial_projected_average_second h M hunit,
    fun i => (polynomial_projected_envelope_moment h hq hB M hJ hM i).2,
    polynomial_projected_average_fourth h M (zero_le_one.trans hJ) hM⟩

/-- Polynomial branch of Corollary 3: the full Theorem 2 rate is recomputed
at the exact safe class scale `J² B` and at the number of faces. -/
theorem polynomialPolyhedralCLT
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (X : Fin n → Ω → Vector p) {q B : ℝ} (hq : 2 < q) (hB : 1 ≤ B)
    (h : PolynomialIndependentHypotheses μ X q B)
    (A : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α)
    (hvariance : ∀ α, dotProduct (ν α)
      ((covariance μ (normalizedObservationSum X)).mulVec (ν α)) = (σ α)^2) :
    polyhedralDistance μ (normalizedObservationSum X) A ν ≤
      polynomialUniversalConstant q * min 1 (polynomialCombinedRate n m (J^2*B) q) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  have hunit : ∀ α, (M * covariance μ (normalizedObservationSum X) * M.transpose) α α = 1 :=
    standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance
  have hJ : 1 ≤ J := one_le_polynomial_projection_bound h hm M hM hunit
  let Y : Fin n → Ω → Vector m := fun i ω => M.mulVec (X i ω)
  have hY : PolynomialIndependentHypotheses μ Y q (J^2*B) :=
    polynomialIndependent_projected h (by linarith) (zero_le_one.trans hB) M hJ hM
      hunit
  obtain ⟨C, hC⟩ := hY.gaussian_factor_exists μ
  have hgram : C*C.transpose = M*(A*A.transpose)*M.transpose := by
    rw [hC, hA]
    exact polynomial_projected_covariance h M
  have hd := polyhedralDistance_le_projected_rectangleDistance
    μ (normalizedObservationSum X) A C ν σ hσ hgram
  have hsum : normalizedObservationSum Y =
      fun ω => M.mulVec (normalizedObservationSum X ω) := normalizedObservationSum_mulVec M X
  change polyhedralDistance μ (normalizedObservationSum X) A ν ≤
    rectangleDistance μ (fun ω => M.mulVec (normalizedObservationSum X ω)) C at hd
  rw [← hsum] at hd
  exact hd.trans (polynomialMomentCLT μ hm hn hq
    (one_le_mul_of_one_le_of_one_le (by nlinarith) hB) Y hY C hC)

end
end RectangleCLT.Companion.SplitV4
