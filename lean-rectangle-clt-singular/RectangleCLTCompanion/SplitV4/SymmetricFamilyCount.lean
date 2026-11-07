import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaximum
import Mathlib.Probability.Variance

/-! Actual activation-count moments and masked-maximum moment bounds. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 theorem integral_familyRest_indicator_function (P : SymmetricFamilyParameters) (m : ℕ) (f : Bool → ℝ) :
    (∫ z : FamilyRestSeed m, f z.2.1 ∂familyRestLaw P m) = ∫ b, f b ∂familyBernoulli (familyTheta P) := by
  have h1 := MeasureTheory.integral_fun_snd (μ := familySignLaw m)
    (ν := (familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))
    (fun z : Bool × FamilySigns m => f z.1)
  have h2 := MeasureTheory.integral_fun_fst (μ := familyBernoulli (familyTheta P)) (ν := familyMaskLaw P m) f
  simp only [measureReal_univ_eq_one, one_smul] at h1 h2
  exact h1.trans h2

theorem integral_familyRestArray_function (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (f : FamilyRestSeed m → ℝ) :
    (∫ z, f (z i) ∂familyRestArrayLaw P n m) = ∫ y, f y ∂familyRestLaw P m := by
  have hh := integral_map (μ := familyRestArrayLaw P n m) (measurable_pi_apply i).aemeasurable
    (measurable_of_finite f).aestronglyMeasurable
  rw [show (familyRestArrayLaw P n m).map (fun z => z i) = familyRestLaw P m from
    familyPi_map_eval (fun _ : Fin n => familyRestLaw P m) i] at hh
  exact hh.symm

theorem integral_familyActivationIndicator (P : SymmetricFamilyParameters) {n m : ℕ} (i : Fin n) :
    (∫ z, familyIndicator (z i).2.1 ∂familyRestArrayLaw P n m) = P.theta := by
  rw [integral_familyRestArray_function P i (fun y => familyIndicator y.2.1),
    integral_familyRest_indicator_function, integral_familyIndicator]
  rfl

theorem familyActivationCount_nonneg {n m : ℕ} (z : Fin n → FamilyRestSeed m) : 0 ≤ familyActivationCount z :=
  Finset.sum_nonneg (fun _ _ => familyIndicator_nonneg _)

theorem integral_familyActivationCount (P : SymmetricFamilyParameters) (n m : ℕ) :
    (∫ z, familyActivationCount z ∂familyRestArrayLaw P n m) = (n : ℝ) * P.theta := by
  unfold familyActivationCount
  rw [integral_finset_sum _ (fun _ _ => integrable_family_finite _ _)]
  simp only [integral_familyActivationIndicator, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

theorem familyActivationIndicators_independent (P : SymmetricFamilyParameters) (n m : ℕ) :
    iIndepFun (fun i (z : Fin n → FamilyRestSeed m) => familyIndicator (z i).2.1) (familyRestArrayLaw P n m) :=
  (familyPi_iIndepFun (fun _ : Fin n => familyRestLaw P m)).comp
    (fun _ y => familyIndicator y.2.1) (fun _ => measurable_of_finite _)

theorem variance_familyActivationCount (P : SymmetricFamilyParameters) (n m : ℕ) :
    variance familyActivationCount (familyRestArrayLaw P n m) = (n : ℝ) * P.theta * (1 - P.theta) := by
  let μ := familyRestArrayLaw P n m
  let I : Fin n → (Fin n → FamilyRestSeed m) → ℝ := fun i z => familyIndicator (z i).2.1
  have hLp (i : Fin n) : MemLp (I i) 2 μ := memLp_family_finite μ (I i) 2
  have hvar (i : Fin n) : variance (I i) μ = P.theta - P.theta ^ 2 := by
    rw [variance_def' (hLp i)]
    have he : (∫ z, I i z ^ 2 ∂μ) = P.theta := by
      simp_rw [I, familyIndicator_sq]
      exact integral_familyActivationIndicator P i
    change (∫ z, I i z ^ 2 ∂μ) - (∫ z, I i z ∂μ) ^ 2 = _
    rw [he, show (∫ z, I i z ∂μ) = P.theta from integral_familyActivationIndicator P i]
  have hh := IndepFun.variance_sum (s := Finset.univ) (fun i _ => hLp i)
    (fun i _ j _ hij => (familyActivationIndicators_independent P n m).indepFun hij)
  have heq : (∑ i : Fin n, I i) = familyActivationCount := by
    funext z
    simp only [Finset.sum_apply, I, familyActivationCount]
  rw [heq] at hh
  simp only [hvar, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hh
  change variance familyActivationCount (familyRestArrayLaw P n m) = _ at hh
  rw [hh]
  ring

theorem integral_familyActivationCount_sq (P : SymmetricFamilyParameters) (n m : ℕ) :
    (∫ z, familyActivationCount z ^ 2 ∂familyRestArrayLaw P n m) =
      ((n : ℝ) * P.theta) ^ 2 + (n : ℝ) * P.theta * (1 - P.theta) := by
  have hh := variance_def' (memLp_family_finite (familyRestArrayLaw P n m) familyActivationCount 2)
  rw [variance_familyActivationCount, integral_familyActivationCount] at hh
  change _ = (∫ z, familyActivationCount z ^ 2 ∂familyRestArrayLaw P n m) - _ at hh
  linarith

theorem integral_familyActivationCount_sq_le (P : SymmetricFamilyParameters) (n m : ℕ) :
    (∫ z, familyActivationCount z ^ 2 ∂familyRestArrayLaw P n m) ≤
      ((n : ℝ) * P.theta) ^ 2 + (n : ℝ) * P.theta := by
  rw [integral_familyActivationCount_sq]
  have hh : 0 ≤ (n : ℝ) * P.theta ^ 2 := by positivity
  nlinarith only [hh]

theorem abs_familyMaskedSignCount_le {n m : ℕ} (z : Fin n → FamilyRestSeed m) (u : Fin m) :
    |familyMaskedSignCount z u| ≤ familyActivationCount z := by
  calc
    _ ≤ ∑ i, |familyIndicator (z i).2.1 * familyIndicator ((z i).2.2 u) * familySign ((z i).1 u)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, familyIndicator (z i).2.1 := by
      apply Finset.sum_le_sum
      intro i _
      rw [abs_mul, abs_familySign, mul_one, abs_of_nonneg (mul_nonneg (familyIndicator_nonneg _) (familyIndicator_nonneg _))]
      exact (mul_le_mul_of_nonneg_left (familyIndicator_le_one _) (familyIndicator_nonneg _)).trans_eq (mul_one _)
    _ = _ := rfl

theorem abs_familyMaskedSignMaximum_le {n m : ℕ} [NeZero m] (z : Fin n → FamilyRestSeed m) :
    |familyMaskedSignMaximum z| ≤ familyActivationCount z := by
  obtain ⟨u, hu⟩ := finiteMaximum_attains (familyMaskedSignCount z)
  change |finiteMaximum (familyMaskedSignCount z)| ≤ _
  rw [← hu]
  exact abs_familyMaskedSignCount_le z u

theorem integral_familyMaskedSignMaximum_sq_le (P : SymmetricFamilyParameters) (n m : ℕ) [NeZero m] :
    (∫ z, familyMaskedSignMaximum z ^ 2 ∂familyRestArrayLaw P n m) ≤
      ((n : ℝ) * P.theta) ^ 2 + (n : ℝ) * P.theta := by
  apply (integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
    (fun z => ?_)).trans (integral_familyActivationCount_sq_le P n m)
  have hh := pow_le_pow_left₀ (abs_nonneg _) (abs_familyMaskedSignMaximum_le z) 2
  simpa only [sq_abs] using hh

end
end RectangleCLT.Companion.SplitV4
