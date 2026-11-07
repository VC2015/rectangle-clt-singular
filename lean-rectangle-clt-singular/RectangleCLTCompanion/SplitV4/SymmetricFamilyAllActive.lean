import RectangleCLTCompanion.SplitV4.SymmetricFamilyActivation
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-! A genuine all-active-column bound, including the coordinate masks pi<1. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familyAllSelected {n : ℕ} (I : Fin n → Bool) : Set (Fin n → FamilyMaskSign) :=
  univ.pi (fun i => if I i then {(true, true)} else univ)

def familyColumnMaximum {n m : ℕ} [NeZero m] (I : Fin n → Bool) (z : Fin m → Fin n → FamilyMaskSign) : ℝ :=
  finiteMaximum (fun u => familyActivationColumnSum I (z u))

theorem familyActivationColumnCount_eq_sum {n : ℕ} (I : Fin n → Bool) :
    (familyActivationColumnCount I : ℝ) = ∑ i, familyIndicator (I i) := by
  simp [familyActivationColumnCount, familyIndicator]

theorem familyActivationColumnSum_le_count {n : ℕ} (I : Fin n → Bool) (z : Fin n → FamilyMaskSign) :
    familyActivationColumnSum I z ≤ (familyActivationColumnCount I : ℝ) := by
  rw [familyActivationColumnCount_eq_sum]
  apply Finset.sum_le_sum
  intro i _
  apply (le_abs_self _).trans
  rw [abs_mul, abs_familySign, mul_one,
    abs_of_nonneg (mul_nonneg (familyIndicator_nonneg _) (familyIndicator_nonneg _))]
  exact (mul_le_mul_of_nonneg_left (familyIndicator_le_one _) (familyIndicator_nonneg _)).trans_eq (mul_one _)

theorem familyActivationColumnSum_eq_count_of_allSelected {n : ℕ} (I : Fin n → Bool)
    (z : Fin n → FamilyMaskSign) (hz : z ∈ familyAllSelected I) :
    familyActivationColumnSum I z = (familyActivationColumnCount I : ℝ) := by
  rw [familyActivationColumnCount_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  have hi := hz i (mem_univ i)
  by_cases hI : I i = true
  · have hpair : z i = (true, true) := by simpa [familyAllSelected, hI] using hi
    simp [hI, hpair, familyIndicator, familySign]
  · simp [hI, familyIndicator]

theorem familyColumnMaximum_eq_count_of_selected {n m : ℕ} [NeZero m] (I : Fin n → Bool)
    (z : Fin m → Fin n → FamilyMaskSign) (hz : ∃ u, z u ∈ familyAllSelected I) :
    familyColumnMaximum I z = (familyActivationColumnCount I : ℝ) := by
  apply le_antisymm
  · exact finiteMaximum_le _ (fun u => familyActivationColumnSum_le_count I (z u))
  · obtain ⟨u, hu⟩ := hz
    rw [← familyActivationColumnSum_eq_count_of_allSelected I (z u) hu]
    exact le_finiteMaximum (fun v => familyActivationColumnSum I (z v)) u

theorem familyMaskSignLaw_atom (P : SymmetricFamilyParameters) :
    familyMaskSignLaw P {(true, true)} = ENNReal.ofReal (P.pi / 2) := by
  rw [familyMaskSignLaw, ← singleton_prod_singleton, Measure.prod_prod]
  simp only [familyBernoulli, familyHalf, familyPi, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply', Set.mem_singleton_iff, Bool.false_eq_true, not_false_eq_true,
    if_false, if_true, eq_self, smul_eq_mul, mul_zero, zero_add, mul_one]
  norm_num
  rw [← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  congr 1
  ring

theorem familyAllSelected_probability (P : SymmetricFamilyParameters) {n : ℕ} (I : Fin n → Bool) :
    (Measure.pi (fun _ : Fin n => familyMaskSignLaw P)).real (familyAllSelected I) =
      (P.pi / 2) ^ familyActivationColumnCount I := by
  have hr : 0 ≤ P.pi / 2 := by linarith [P.pi_pos]
  have hmeasure : (Measure.pi (fun _ : Fin n => familyMaskSignLaw P)) (familyAllSelected I) =
      (ENNReal.ofReal (P.pi / 2)) ^ familyActivationColumnCount I := by
    rw [familyAllSelected, Measure.pi_pi]
    rw [familyActivationColumnCount, ← Finset.prod_pow_eq_pow_sum]
    apply Finset.prod_congr rfl
    intro i _
    by_cases hI : I i = true <;> simp [hI, familyMaskSignLaw_atom]
  exact (congrArg ENNReal.toReal hmeasure).trans (by simp only [ENNReal.toReal_pow, ENNReal.toReal_ofReal hr])

theorem familyNoSelectedColumns_probability (P : SymmetricFamilyParameters) {n m : ℕ} (I : Fin n → Bool) :
    (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P))).real
      {z | ∀ u, z u ∉ familyAllSelected I} =
        (1 - (P.pi / 2) ^ familyActivationColumnCount I) ^ m := by
  let κ := Measure.pi (fun _ : Fin n => familyMaskSignLaw P)
  letI : IsProbabilityMeasure κ := by constructor; simp [κ, Measure.pi_univ]
  have heq : {z : Fin m → Fin n → FamilyMaskSign | ∀ u, z u ∉ familyAllSelected I} =
      univ.pi (fun _ : Fin m => (familyAllSelected I)ᶜ) := by ext z; simp
  rw [heq, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  change κ.real (familyAllSelected I)ᶜ = _
  rw [measureReal_compl (Set.toFinite _).measurableSet, measureReal_univ_eq_one,
    familyAllSelected_probability]

theorem familyColumnMaximum_failure_bound (P : SymmetricFamilyParameters) {n m : ℕ} [NeZero m]
    (I : Fin n → Bool) {b : ℕ} (hb : familyActivationColumnCount I ≤ b) :
    (Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P))).real
      {z | familyColumnMaximum I z ≠ (familyActivationColumnCount I : ℝ)} ≤
        Real.exp (-(m : ℝ) * (P.pi / 2) ^ b) := by
  let κ := Measure.pi (fun _ : Fin n => familyMaskSignLaw P)
  letI : IsProbabilityMeasure κ := by constructor; simp [κ, Measure.pi_univ]
  letI : IsProbabilityMeasure (Measure.pi (fun _ : Fin m => κ)) := by constructor; simp [Measure.pi_univ]
  have hsub : {z : Fin m → Fin n → FamilyMaskSign | familyColumnMaximum I z ≠ (familyActivationColumnCount I : ℝ)} ⊆
      {z | ∀ u, z u ∉ familyAllSelected I} := by
    intro z hz u hu
    exact hz (familyColumnMaximum_eq_count_of_selected I z ⟨u, hu⟩)
  apply (measureReal_mono hsub).trans
  rw [familyNoSelectedColumns_probability]
  have hr0 : 0 ≤ P.pi / 2 := by linarith [P.pi_pos]
  have hr1 : P.pi / 2 ≤ 1 := by linarith [P.pi_le_one]
  have hpow := pow_le_pow_of_le_one hr0 hr1 hb
  have hbase0 : 0 ≤ 1 - (P.pi / 2) ^ familyActivationColumnCount I :=
    sub_nonneg.mpr (pow_le_one₀ hr0 hr1)
  have hstep := Real.add_one_le_exp (-((P.pi / 2) ^ b))
  have hbexp : 1 - (P.pi / 2) ^ familyActivationColumnCount I ≤ Real.exp (-((P.pi / 2) ^ b)) := by linarith
  have hh := pow_le_pow_left₀ hbase0 hbexp m
  rw [← Real.exp_nat_mul] at hh
  exact hh.trans_eq (by congr 1; ring)


theorem finite_product_probability_bound {A B : Type*} [Fintype A] [Fintype B]
    [MeasurableSpace A] [MeasurableSpace B] [MeasurableSingletonClass A] [MeasurableSingletonClass B]
    (μ : Measure A) [IsProbabilityMeasure μ] (ν : Measure B) [IsProbabilityMeasure ν]
    (F : Set (A × B)) (D : Set A) {c : ℝ} (hc : 0 ≤ c)
    (hsection : ∀ a, a ∉ D → ν.real {b | (a,b) ∈ F} ≤ c) :
    (μ.prod ν).real F ≤ μ.real D + c := by
  classical
  have hF := (Set.toFinite F).measurableSet
  have hs (a : A) := (Set.toFinite {b : B | (a,b) ∈ F}).measurableSet
  have heq : (μ.prod ν).real F = ∫ a, ν.real {b | (a,b) ∈ F} ∂μ := by
    rw [← integral_indicator_one hF, integral_prod _ (integrable_family_finite _ _)]
    apply integral_congr_ae
    apply ae_of_all
    intro a
    dsimp only
    have hfun : (fun b => F.indicator (1 : A × B → ℝ) (a,b)) = ({b | (a,b) ∈ F} : Set B).indicator 1 := by
      funext b
      by_cases h : (a,b) ∈ F <;> simp [h]
    rw [hfun, integral_indicator_one (hs a)]
  rw [heq]
  calc
    _ ≤ ∫ a, D.indicator (1 : A → ℝ) a + c ∂μ := by
      apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
      intro a
      dsimp only
      by_cases ha : a ∈ D
      · rw [Set.indicator_of_mem ha]
        simp only [Pi.one_apply]
        have hh : ν.real {b | (a,b) ∈ F} ≤ 1 := (measureReal_mono (subset_univ _)).trans_eq measureReal_univ_eq_one
        linarith
      · simpa only [Set.indicator_of_not_mem ha, zero_add] using hsection a ha
    _ = μ.real D + c := by
      rw [integral_add (integrable_family_finite _ _) (integrable_const _), integral_indicator_one (Set.toFinite D).measurableSet]
      simp

/-- Exact finite-law version of the all-active bound. Natural cutoffs
suffice for both dense and sparse parameter calibrations. -/
theorem familyMaskedSignMaximum_all_active_bound (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] (b : ℕ) :
    (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z} ≤
      (familyRestArrayLaw P n m).real {z | (b : ℝ) < familyActivationCount z} +
        Real.exp (-(m : ℝ) * (P.pi / 2) ^ b) := by
  classical
  let μI := Measure.pi (fun _ : Fin n => familyBernoulli (familyTheta P))
  let μC := Measure.pi (fun _ : Fin m => Measure.pi (fun _ : Fin n => familyMaskSignLaw P))
  letI : IsProbabilityMeasure μC := by constructor; simp [μC, Measure.pi_univ]
  let F : Set (FamilyActivationColumnsSeed n m) :=
    {z | familyColumnMaximum z.1 z.2 ≠ (familyActivationColumnCount z.1 : ℝ)}
  let D : Set (Fin n → Bool) := {I | (b : ℝ) < (familyActivationColumnCount I : ℝ)}
  have hprob := finite_product_probability_bound μI μC F D (Real.exp_pos _).le (fun I hI => by
    have hIb : familyActivationColumnCount I ≤ b := by
      change ¬ (b : ℝ) < (familyActivationColumnCount I : ℝ) at hI
      exact_mod_cast le_of_not_gt hI
    exact familyColumnMaximum_failure_bound P I hIb)
  have hp := familyRestToActivationColumns_preserving P n m
  have hfailure : (familyRestArrayLaw P n m).real {z | familyMaskedSignMaximum z ≠ familyActivationCount z} =
      (familyActivationColumnsLaw P n m).real F := by
    have hh := congrArg (fun κ : Measure (FamilyActivationColumnsSeed n m) => κ.real F) hp.map_eq
    dsimp only at hh
    rw [map_measureReal_apply hp.measurable (Set.toFinite F).measurableSet] at hh
    have hset : familyRestToActivationColumns ⁻¹' F =
        {z : Fin n → FamilyRestSeed m | familyMaskedSignMaximum z ≠ familyActivationCount z} := by
      ext z
      simp only [mem_preimage, F, mem_setOf_eq, familyColumnMaximum,
        ← familyMaskedSignCount_columns, ← familyActivationCount_columns, familyMaskedSignMaximum]
    rw [hset] at hh
    exact hh
  have hfst : MeasurePreserving Prod.fst (familyActivationColumnsLaw P n m) μI := by
    refine ⟨measurable_fst, ?_⟩
    change (μI.prod μC).map Prod.fst = μI
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
  have hIp := hfst.comp hp
  have htail : (familyRestArrayLaw P n m).real {z | (b : ℝ) < familyActivationCount z} = μI.real D := by
    have hh := congrArg (fun κ : Measure (Fin n → Bool) => κ.real D) hIp.map_eq
    dsimp only at hh
    rw [map_measureReal_apply hIp.measurable (Set.toFinite D).measurableSet] at hh
    have hset : (Prod.fst ∘ familyRestToActivationColumns) ⁻¹' D =
        {z : Fin n → FamilyRestSeed m | (b : ℝ) < familyActivationCount z} := by
      ext z
      simp only [mem_preimage, Function.comp_apply, D, mem_setOf_eq, ← familyActivationCount_columns]
    rw [hset] at hh
    exact hh
  rw [hfailure, htail]
  exact hprob

end
end RectangleCLT.Companion.SplitV4
