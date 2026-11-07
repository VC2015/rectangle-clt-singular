import RectangleCLTCompanion.SubexponentialGaussian
import RectangleCLTCompanion.SubexponentialL2
import RectangleCLTCompanion.SubexponentialScaling
import RectangleCLTCompanion.SplitV4.PairedMoments
import RectangleCLT.BoundedIndependentScaling
import RectangleCLT.ThinningMoments

/-!
Actual normalization and covariance-factor existence for the finite-moment
observations in Appendix G. No boundedness, identical-law, covariance gap,
symmetry or positive eigenvalue premise is imposed.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- The actual normalized summands `xi_i=X_i/sqrt n`. -/
def normalizedSummands {Ω : Type*} {p n : ℕ} (X : Fin n → Ω → Vector p) :
    Fin n → Ω → Vector p := fun i ω => (Real.sqrt (n : ℝ))⁻¹ • X i ω

/-- The coordinate fourth-moment sums, before taking the maximum norm. -/
def coordinateFourthMomentSums {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) : Vector p :=
  fun j => ∑ i, ∫ ω, X i ω j ^ 4 ∂μ

/-- The genuine maximum of the nonnegative coordinate fourth-moment sums.
Its native finite-product norm is the maximum norm, including dimension zero. -/
def arrayFourthMomentBudget {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) : ℝ := ‖coordinateFourthMomentSums μ X‖

/-- The paper's raw-observation parameter `Delta_1`. Genuine integrability
is discharged in the theorems using this definition. -/
def deltaOne {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) : ℝ :=
  (1 / (n : ℝ) ^ 2) * arrayFourthMomentBudget μ X

variable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
  {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector p}

/-- A centered vector with genuine coordinate L2 moments has an actual
square Gaussian covariance factor. No covariance inverse is used. -/
theorem gaussian_factor_exists_of_coordinate_memLp_two
    (U : Ω → Vector p) (hL2 : ∀ j, MemLp (fun ω => U ω j) (2 : ℝ≥0∞) μ)
    (hc : ∀ j, (∫ ω, U ω j ∂μ) = 0) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = covariance μ U := by
  let V : Ω → Vector p := 0
  have hjoint (a : JointIndex p) : MemLp (fun ω => jointValue U V ω a) 2 μ := by
    cases a with
    | inl j => exact hL2 j
    | inr j => exact MemLp.zero'
  have hmean (a : JointIndex p) : (∫ ω, jointValue U V ω a ∂μ) = 0 := by
    cases a with
    | inl j => exact hc j
    | inr j => simp [jointValue, V]
  have hrest : restoredCovariance (jointSecondMoment μ U V) = covariance μ U := by
    simpa only [V, add_zero] using jointSecondMoment_restoredCovariance U V hjoint hmean
  have hcov : (covariance μ U).PosSemidef := by
    rw [← hrest]
    exact restoredCovariance_posSemidef _ (jointSecondMoment_posSemidef hjoint)
  refine ⟨hcov.sqrt, ?_⟩
  have hsym : hcov.sqrt.transpose = hcov.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial] using
      hcov.posSemidef_sqrt.isHermitian
  rw [hsym]
  exact hcov.sqrt_mul_self

theorem gaussian_factor_exists_of_centered_array
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ)
    (hc : ∀ i j, (∫ ω, X i ω j ∂μ) = 0) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ, A * A.transpose = covariance μ (sumVector X) := by
  apply gaussian_factor_exists_of_coordinate_memLp_two (sumVector X)
    (memLp_sumVector_coordinate hL2)
  exact integral_sumVector_coordinate_zero (fun i j => (hL2 i j).integrable (by norm_num)) hc

theorem normalizedSummands_measurable (hX : ∀ i, Measurable (X i)) (i : Fin n) :
    Measurable (normalizedSummands X i) := measurable_const.smul (hX i)

theorem normalizedSummands_independent (hi : iIndepFun X μ) :
    iIndepFun (normalizedSummands X) μ :=
  hi.comp (fun _ x => (Real.sqrt (n : ℝ))⁻¹ • x)
    (fun _ => measurable_const.smul measurable_id)

theorem normalizedSummands_centered
    (hc : ∀ i j, (∫ ω, X i ω j ∂μ) = 0) (i : Fin n) (j : Fin p) :
    (∫ ω, normalizedSummands X i ω j ∂μ) = 0 := by
  simp only [normalizedSummands, Pi.smul_apply, smul_eq_mul, integral_const_mul, hc, mul_zero]

theorem normalizedSummands_coordinate_memLp_two
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ) (i : Fin n) (j : Fin p) :
    MemLp (fun ω => normalizedSummands X i ω j) (2 : ℝ≥0∞) μ :=
  (hL2 i j).const_mul _

theorem sumVector_normalizedSummands : sumVector (normalizedSummands X) = normalizedObservationSum X := by
  funext ω
  exact sumVector_smul X (Real.sqrt (n : ℝ))⁻¹ ω

/-- Full covariance scaling, including all cross-coordinate blocks. -/
theorem covariance_normalizedSummands :
    covariance μ (sumVector (normalizedSummands X)) =
      (1 / (n : ℝ)) • covariance μ (sumVector X) := by
  ext j k
  rw [sumVector_normalizedSummands]
  change covariance μ (fun ω => diagonalScale (fun _ => (Real.sqrt (n : ℝ))⁻¹) (sumVector X ω)) j k = _
  rw [covariance_diagonalScale]
  have hs : (Real.sqrt (n : ℝ))⁻¹ * (Real.sqrt (n : ℝ))⁻¹ = 1 / (n : ℝ) := by
    rw [← pow_two, inv_pow, Real.sq_sqrt (Nat.cast_nonneg n), one_div]
  simp only [Matrix.smul_apply, smul_eq_mul, ← mul_assoc, hs]

private theorem coordinate_product_integrable
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ)
    (i l : Fin n) (j k : Fin p) : Integrable (fun ω => X i ω j * X l ω k) μ := by
  haveI : ENNReal.HolderTriple (2 : ℝ≥0∞) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  exact (hL2 i j).integrable_mul (hL2 l k)

/-- Average marginal second moments are exactly the diagonal covariance
of the actual normalized sum. Independence is only over summands. -/
theorem normalizedSummands_covariance_diagonal
    (hi : iIndepFun X μ)
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ)
    (hc : ∀ i j, (∫ ω, X i ω j ∂μ) = 0) (j : Fin p) :
    covariance μ (sumVector (normalizedSummands X)) j j =
      (1 / (n : ℝ)) * ∑ i, ∫ ω, X i ω j ^ 2 ∂μ := by
  rw [covariance_normalizedSummands]
  simp only [Matrix.smul_apply, smul_eq_mul]
  have hint (i : Fin n) (k : Fin p) : Integrable (fun ω => X i ω k) μ :=
    (hL2 i k).integrable (by norm_num)
  rw [covariance_sum_of_centered_cross hint (coordinate_product_integrable hL2) hc
    (independent_centered_cross_zero hi hint hc)]
  simp only [pow_two]

theorem normalizedSummands_unit_covariance
    (hi : iIndepFun X μ)
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ)
    (hc : ∀ i j, (∫ ω, X i ω j ∂μ) = 0)
    (havg : ∀ j, (1 / (n : ℝ)) * (∑ i, ∫ ω, X i ω j ^ 2 ∂μ) = 1) (j : Fin p) :
    covariance μ (sumVector (normalizedSummands X)) j j = 1 := by
  rw [normalizedSummands_covariance_diagonal hi hL2 hc, havg]

theorem normalizedSummands_gaussian_factor_exists
    (hL2 : ∀ i j, MemLp (fun ω => X i ω j) (2 : ℝ≥0∞) μ)
    (hc : ∀ i j, (∫ ω, X i ω j ∂μ) = 0) :
    ∃ A : Matrix (Fin p) (Fin p) ℝ,
      A * A.transpose = covariance μ (sumVector (normalizedSummands X)) :=
  gaussian_factor_exists_of_centered_array (normalizedSummands_coordinate_memLp_two hL2)
    (normalizedSummands_centered hc)

private theorem normalized_fourth_coefficient (n : ℕ) :
    ((Real.sqrt (n : ℝ))⁻¹) ^ 4 = 1 / (n : ℝ) ^ 2 := by
  rw [inv_pow, show Real.sqrt (n : ℝ) ^ 4 = (Real.sqrt (n : ℝ) ^ 2) ^ 2 by ring,
    Real.sq_sqrt (Nat.cast_nonneg n), one_div]

theorem normalizedSummands_fourth_moment (i : Fin n) (j : Fin p) :
    (∫ ω, normalizedSummands X i ω j ^ 4 ∂μ) =
      (1 / (n : ℝ) ^ 2) * ∫ ω, X i ω j ^ 4 ∂μ := by
  simp only [normalizedSummands, Pi.smul_apply, smul_eq_mul, mul_pow,
    integral_const_mul, normalized_fourth_coefficient]

theorem normalizedSummands_fourth_integrable
    (hfourth : ∀ i j, Integrable (fun ω => X i ω j ^ 4) μ) (i : Fin n) (j : Fin p) :
    Integrable (fun ω => normalizedSummands X i ω j ^ 4) μ := by
  simpa only [normalizedSummands, Pi.smul_apply, smul_eq_mul, mul_pow] using
    (hfourth i j).const_mul (((Real.sqrt (n : ℝ))⁻¹) ^ 4)

theorem coordinateFourthMomentSums_nonneg (j : Fin p) :
    0 ≤ coordinateFourthMomentSums μ X j :=
  Finset.sum_nonneg (fun _ _ => integral_nonneg (fun _ => by positivity))

theorem coordinateFourthMomentSums_le_budget (j : Fin p) :
    coordinateFourthMomentSums μ X j ≤ arrayFourthMomentBudget μ X := by
  simpa only [Real.norm_eq_abs, abs_of_nonneg (coordinateFourthMomentSums_nonneg j)] using
    norm_le_pi_norm (coordinateFourthMomentSums μ X) j

/-- In positive dimension the supremum norm is attained by an actual
coordinate, so the budget is exactly the manuscript's finite maximum. -/
theorem arrayFourthMomentBudget_attained (hp : 1 ≤ p) :
    ∃ j : Fin p, coordinateFourthMomentSums μ X j = arrayFourthMomentBudget μ X := by
  haveI : Nonempty (Fin p) := ⟨⟨0, lt_of_lt_of_le Nat.zero_lt_one hp⟩⟩
  obtain ⟨j, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset (Fin p))
    (coordinateFourthMomentSums μ X) Finset.univ_nonempty
  refine ⟨j, le_antisymm (coordinateFourthMomentSums_le_budget j) ?_⟩
  apply (pi_norm_le_iff_of_nonneg (coordinateFourthMomentSums_nonneg j)).mpr
  intro k
  rw [Real.norm_eq_abs, abs_of_nonneg (coordinateFourthMomentSums_nonneg k)]
  exact hmax k (Finset.mem_univ k)

/-- The normalized fourth budget is exactly the manuscript `Delta_1`,
not a bound obtained by discarding dimensions or individual moments. -/
theorem normalizedSummands_fourth_budget :
    arrayFourthMomentBudget μ (normalizedSummands X) = deltaOne μ X := by
  have hv : coordinateFourthMomentSums μ (normalizedSummands X) =
      (1 / (n : ℝ) ^ 2) • coordinateFourthMomentSums μ X := by
    ext j
    simp only [coordinateFourthMomentSums, normalizedSummands_fourth_moment,
      Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  unfold deltaOne arrayFourthMomentBudget
  rw [hv, norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ 1 / (n : ℝ) ^ 2)]

theorem arrayFourthMomentBudget_nonneg : 0 ≤ arrayFourthMomentBudget μ X := norm_nonneg _

theorem deltaOne_nonneg : 0 ≤ deltaOne μ X :=
  mul_nonneg (by positivity) arrayFourthMomentBudget_nonneg

theorem normalizedSummands_fourth_sums_le_deltaOne (j : Fin p) :
    (∑ i, ∫ ω, normalizedSummands X i ω j ^ 4 ∂μ) ≤ deltaOne μ X := by
  have hb := coordinateFourthMomentSums_le_budget (μ := μ) (X := normalizedSummands X) j
  rw [normalizedSummands_fourth_budget] at hb
  exact hb

/-- The actual paired increment scales with the same `1/sqrt n`. -/
theorem pairedIncrement_normalizedSummands (i : Fin n) (z : Ω × Ω) :
    pairedIncrement (normalizedSummands X) i z =
      (Real.sqrt (n : ℝ))⁻¹ • pairedIncrement X i z := by
  simp only [pairedIncrement, normalizedSummands, smul_sub]

/-- The normalization scales both the paired increment and its actual
norm-truncation event; the cutoff is multiplied by `sqrt n`. -/
theorem pairedTruncatedArray_normalizedSummands
    (hn : 1 ≤ n) (h : ℝ) (i : Fin n) (z : Ω × Ω) :
    pairedTruncatedArray (normalizedSummands X) h i z =
      (Real.sqrt (n : ℝ))⁻¹ • pairedTruncatedArray X (Real.sqrt (n : ℝ) * h) i z := by
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnpos
  have hdiff : (Real.sqrt (n : ℝ))⁻¹ • X i z.2 - (Real.sqrt (n : ℝ))⁻¹ • X i z.1 =
      (Real.sqrt (n : ℝ))⁻¹ • (X i z.2 - X i z.1) := (smul_sub _ _ _).symm
  have hevent : ‖(Real.sqrt (n : ℝ))⁻¹ • (X i z.2 - X i z.1)‖ ≤ h ↔
      ‖X i z.2 - X i z.1‖ ≤ Real.sqrt (n : ℝ) * h := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hspos)]
    simpa only [div_eq_mul_inv, mul_comm] using
      (div_le_iff₀ hspos : ‖X i z.2 - X i z.1‖ / Real.sqrt (n : ℝ) ≤ h ↔
        ‖X i z.2 - X i z.1‖ ≤ h * Real.sqrt (n : ℝ))
  simp only [pairedTruncatedArray, normalizedSummands, pairedTruncatedIncrement, hdiff]
  simp only [hevent]
  split_ifs <;> simp

end

end RectangleCLT.Companion.SplitV4
