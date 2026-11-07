import RectangleCLTCompanion.SplitV4.SymmetricFamilyCount

/-! Actual count-tail and mean-deficit bounds for the common-family maximum. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyActivationCount_upper_tail (P : SymmetricFamilyParameters) (n m : ℕ)
    {b : ℝ} (hb : (n : ℝ) * P.theta < b) :
    (familyRestArrayLaw P n m).real {z | b < familyActivationCount z} ≤
      ((n : ℝ) * P.theta) / (b - (n : ℝ) * P.theta) ^ 2 := by
  let μ := familyRestArrayLaw P n m
  have hc : 0 < b - (n : ℝ) * P.theta := sub_pos.mpr hb
  have hh := meas_ge_le_variance_div_sq (memLp_family_finite μ familyActivationCount 2) hc
  rw [integral_familyActivationCount] at hh
  have hsub : {z : Fin n → FamilyRestSeed m | b < familyActivationCount z} ⊆
      {z | b - (n : ℝ) * P.theta ≤ |familyActivationCount z - (n : ℝ) * P.theta|} := by
    intro z hz
    change b < familyActivationCount z at hz
    exact (by linarith : b - (n : ℝ) * P.theta ≤ familyActivationCount z - (n : ℝ) * P.theta).trans (le_abs_self _)
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top ((measure_mono hsub).trans hh)
  rw [ENNReal.toReal_ofReal (div_nonneg (variance_nonneg _ _) (sq_nonneg _)), variance_familyActivationCount] at hreal
  have hvar : (n : ℝ) * P.theta * (1 - P.theta) ≤ (n : ℝ) * P.theta := by
    have hp : 0 ≤ (n : ℝ) * P.theta ^ 2 := by positivity
    nlinarith only [hp]
  exact hreal.trans (div_le_div_of_nonneg_right hvar (sq_nonneg _))

theorem integral_familyMaskedSignMaximum_le (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m) ≤ (n : ℝ) * P.theta := by
  rw [← integral_familyActivationCount P n m]
  apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
  intro z
  exact (le_abs_self _).trans (abs_familyMaskedSignMaximum_le z)

theorem familyMaskedSignMaximum_mean_deficit (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (n : ℝ) * P.theta - (∫ z, familyMaskedSignMaximum z ∂familyRestArrayLaw P n m) ≤
      2 * Real.sqrt ((n : ℝ) * P.theta * ((n : ℝ) * P.theta + 1)) *
        Real.sqrt ((familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z}) := by
  classical
  let μ := familyRestArrayLaw P n m
  let F : Set (Fin n → FamilyRestSeed m) := {z | familyMaskedSignMaximum z ≠ familyActivationCount z}
  let g : (Fin n → FamilyRestSeed m) → ℝ := F.indicator 1
  have hgn (z : Fin n → FamilyRestSeed m) : 0 ≤ g z := by
    by_cases hz : z ∈ F <;> simp [g, hz]
  have hLpN : MemLp familyActivationCount (ENNReal.ofReal 2) μ := memLp_family_finite μ _ _
  have hLpg : MemLp g (ENNReal.ofReal 2) μ := memLp_family_finite μ _ _
  have hCS := integral_mul_le_Lp_mul_Lq_of_nonneg
    (by norm_num [Real.holderConjugate_iff] : (2 : ℝ).HolderConjugate 2)
    (ae_of_all μ familyActivationCount_nonneg) (ae_of_all μ hgn) hLpN hLpg
  have hg2 : (∫ z, g z ^ 2 ∂μ) = μ.real F := by
    have hpoint : (fun z => g z ^ 2) = g := by
      funext z
      by_cases hz : z ∈ F <;> simp [g, hz]
    rw [hpoint]
    exact integral_indicator_one (Set.toFinite F).measurableSet
  have hCS' : (∫ z, familyActivationCount z * g z ∂μ) ≤
      Real.sqrt (∫ z, familyActivationCount z ^ 2 ∂μ) * Real.sqrt (μ.real F) := by
    norm_num only [Real.rpow_two, hg2, Real.sqrt_eq_rpow] at hCS ⊢
    exact hCS
  have hp : (∫ z, familyActivationCount z ^ 2 ∂μ) ≤
      (n : ℝ) * P.theta * ((n : ℝ) * P.theta + 1) := by
    exact (integral_familyActivationCount_sq_le P n m).trans_eq (by ring)
  have hCsqrt := mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt hp) (Real.sqrt_nonneg (μ.real F))
  calc
    _ = ∫ z, familyActivationCount z - familyMaskedSignMaximum z ∂μ := by
      rw [integral_sub (integrable_family_finite _ _) (integrable_family_finite _ _), integral_familyActivationCount]
    _ ≤ ∫ z, 2 * (familyActivationCount z * g z) ∂μ := by
      apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
      intro z
      by_cases hz : z ∈ F
      · simp only [g, Set.indicator_of_mem hz, Pi.one_apply, mul_one]
        have hh := (abs_le.mp (abs_familyMaskedSignMaximum_le z)).1
        linarith
      · have heq : familyMaskedSignMaximum z = familyActivationCount z := by simpa only [F, mem_setOf_eq, not_not] using hz
        simp only [g, Set.indicator_of_not_mem hz, mul_zero, heq, sub_self, le_refl]
    _ = 2 * ∫ z, familyActivationCount z * g z ∂μ := integral_const_mul _ _
    _ ≤ 2 * (Real.sqrt (∫ z, familyActivationCount z ^ 2 ∂μ) * Real.sqrt (μ.real F)) :=
      mul_le_mul_of_nonneg_left hCS' (by norm_num)
    _ ≤ _ := by nlinarith only [hCsqrt]

end
end RectangleCLT.Companion.SplitV4
