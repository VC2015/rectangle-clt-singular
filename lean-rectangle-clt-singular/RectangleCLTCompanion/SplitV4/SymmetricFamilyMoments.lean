import RectangleCLTCompanion.SplitV4.SymmetricFamilyFinite

/-! Exact finite-law moment calculations for the masked symmetric family. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem integral_family_finite_add {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsFiniteMeasure μ] (f g : Ω → ℝ) :
    (∫ ω, f ω + g ω ∂μ) = (∫ ω, f ω ∂μ) + (∫ ω, g ω ∂μ) :=
  integral_add (integrable_family_finite μ f) (integrable_family_finite μ g)

theorem integral_familyBooleanPi {m : ℕ} (t : FamilyProbability) (j : Fin m) (f : Bool → ℝ) :
    (∫ z : FamilySigns m, f (z j) ∂Measure.pi (fun _ => familyBernoulli t)) =
      ∫ b, f b ∂familyBernoulli t := by
  have hh := integral_map (μ := Measure.pi (fun _ : Fin m => familyBernoulli t))
    (measurable_pi_apply j).aemeasurable (measurable_of_finite f).aestronglyMeasurable
  rw [familyPi_map_eval] at hh
  exact hh.symm

theorem integral_familySignLaw_sign {m : ℕ} (j : Fin m) :
    (∫ z, familySign (z j) ∂familySignLaw m) = 0 :=
  (integral_familyBooleanPi familyHalf j familySign).trans integral_familySign

theorem integral_familyMaskLaw_indicator (P : SymmetricFamilyParameters) {m : ℕ} (u : Fin m) :
    (∫ z, familyIndicator (z u) ∂familyMaskLaw P m) = P.pi :=
  (integral_familyBooleanPi (familyPi P) u familyIndicator).trans (integral_familyIndicator (familyPi P))

theorem integral_familySignLaw_product {m : ℕ} (j k : Fin m) :
    (∫ z, familySign (z j) * familySign (z k) ∂familySignLaw m) = if j = k then 1 else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    simp only [if_pos rfl, ← pow_two, familySign_sq, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
    norm_num
  · rw [if_neg hjk]
    have hi := ((familyPi_iIndepFun (fun _ : Fin m => familyBernoulli familyHalf)).indepFun hjk).comp
      (measurable_of_finite familySign) (measurable_of_finite familySign)
    have hh := hi.integral_mul_of_integrable
      (integrable_family_finite (familySignLaw m) (fun z => familySign (z j)))
      (integrable_family_finite (familySignLaw m) (fun z => familySign (z k)))
    change (∫ z, familySign (z j) * familySign (z k) ∂familySignLaw m) =
      (∫ z, familySign (z j) ∂familySignLaw m) * (∫ z, familySign (z k) ∂familySignLaw m) at hh
    simpa only [integral_familySignLaw_sign, mul_zero] using hh

theorem integral_familySignLaw_affine {m : ℕ} (j : Fin m) (c d : ℝ) :
    (∫ z, c * familySign (z j) + d ∂familySignLaw m) = d := by
  rw [integral_family_finite_add, integral_const_mul, integral_familySignLaw_sign]
  simp

theorem integral_familySignLaw_affine_product {m : ℕ} (j k : Fin m) (c d e : ℝ) :
    (∫ z, (c * familySign (z j) + d) * (c * familySign (z k) + e) ∂familySignLaw m) =
      c ^ 2 * (if j = k then 1 else 0) + d * e := by
  have heq : (fun z : FamilySigns m => (c * familySign (z j) + d) * (c * familySign (z k) + e)) =
      fun z => c ^ 2 * (familySign (z j) * familySign (z k)) +
        (c * e) * familySign (z j) + (c * d) * familySign (z k) + d * e := by
    funext z
    ring
  rw [heq]
  simp only [integral_family_finite_add, integral_const_mul, integral_familySignLaw_product,
    integral_familySignLaw_sign, mul_zero, add_zero, integral_const, measureReal_univ_eq_one,
    smul_eq_mul, one_mul]

theorem integral_familySignLaw_affine_fourth {m : ℕ} (j : Fin m) (c d : ℝ) :
    (∫ z, (c * familySign (z j) + d) ^ 4 ∂familySignLaw m) = c ^ 4 + 6 * c ^ 2 * d ^ 2 + d ^ 4 := by
  rw [show (∫ z, (c * familySign (z j) + d) ^ 4 ∂familySignLaw m) =
      ∫ b, (c * familySign b + d) ^ 4 ∂familyBernoulli familyHalf from
        integral_familyBooleanPi familyHalf j (fun b => (c * familySign b + d) ^ 4),
    integral_familyBernoulli]
  norm_num [familyHalf, familySign]
  ring

theorem familyActivated_sq (P : SymmetricFamilyParameters) {m : ℕ}
    (z : FamilySigns m × (Bool × FamilySigns m)) (u : Fin m) :
    familyActivated P z u ^ 2 = P.amplitude ^ 2 * familyIndicator z.2.1 * familyIndicator (z.2.2 u) := by
  unfold familyActivated
  simp only [mul_pow, familyIndicator_sq, familySign_sq, mul_one]

theorem familyActivated_fourth (P : SymmetricFamilyParameters) {m : ℕ}
    (z : FamilySigns m × (Bool × FamilySigns m)) (u : Fin m) :
    familyActivated P z u ^ 4 = P.amplitude ^ 4 * familyIndicator z.2.1 * familyIndicator (z.2.2 u) := by
  unfold familyActivated
  simp only [mul_pow, familyIndicator_fourth, familySign_fourth, mul_one]

theorem integral_familyIndicator_product (P : SymmetricFamilyParameters) {m : ℕ} (u : Fin m) :
    (∫ z : Bool × FamilySigns m, familyIndicator z.1 * familyIndicator (z.2 u)
      ∂(familyBernoulli (familyTheta P)).prod (familyMaskLaw P m)) = P.theta * P.pi := by
  exact (integral_prod_mul familyIndicator (fun z : FamilySigns m => familyIndicator (z u))).trans
    (by rw [integral_familyIndicator, integral_familyMaskLaw_indicator]; rfl)

theorem integral_familyActivated (P : SymmetricFamilyParameters) {m : ℕ} (u : Fin m) :
    (∫ z, familyActivated P z u ∂familyRestLaw P m) = 0 := by
  rw [familyRestLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  have he (y : Bool × FamilySigns m) :
      (∫ z : FamilySigns m, familyActivated P (z, y) u ∂familySignLaw m) = 0 := by
    unfold familyActivated
    change (∫ z : FamilySigns m,
      (P.amplitude * familyIndicator y.1 * familyIndicator (y.2 u)) * familySign (z u)
      ∂familySignLaw m) = 0
    rw [integral_const_mul, integral_familySignLaw_sign]
    simp
  simp_rw [he]
  simp

theorem integral_familyActivated_sq (P : SymmetricFamilyParameters) {m : ℕ} (u : Fin m) :
    (∫ z, familyActivated P z u ^ 2 ∂familyRestLaw P m) = P.variance := by
  simp_rw [familyActivated_sq]
  change (∫ z : FamilySigns m × (Bool × FamilySigns m),
    (fun y : Bool × FamilySigns m => P.amplitude ^ 2 * familyIndicator y.1 * familyIndicator (y.2 u)) z.2
      ∂(familySignLaw m).prod ((familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))) = _
  rw [MeasureTheory.integral_fun_snd (μ := familySignLaw m)
    (ν := (familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))
    (fun y : Bool × FamilySigns m => P.amplitude ^ 2 * familyIndicator y.1 * familyIndicator (y.2 u))]
  simp only [measureReal_univ_eq_one, one_smul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_familyIndicator_product]
  unfold SymmetricFamilyParameters.variance
  ring

theorem integral_familyActivated_fourth (P : SymmetricFamilyParameters) {m : ℕ} (u : Fin m) :
    (∫ z, familyActivated P z u ^ 4 ∂familyRestLaw P m) = P.theta * P.pi * P.amplitude ^ 4 := by
  simp_rw [familyActivated_fourth]
  change (∫ z : FamilySigns m × (Bool × FamilySigns m),
    (fun y : Bool × FamilySigns m => P.amplitude ^ 4 * familyIndicator y.1 * familyIndicator (y.2 u)) z.2
      ∂(familySignLaw m).prod ((familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))) = _
  rw [MeasureTheory.integral_fun_snd (μ := familySignLaw m)
    (ν := (familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))
    (fun y : Bool × FamilySigns m => P.amplitude ^ 4 * familyIndicator y.1 * familyIndicator (y.2 u))]
  simp only [measureReal_univ_eq_one, one_smul]
  simp_rw [mul_assoc]
  rw [integral_const_mul, integral_familyIndicator_product]
  ring


theorem integral_familyActivated_product (P : SymmetricFamilyParameters) {m : ℕ} (u w : Fin m) :
    (∫ z, familyActivated P z u * familyActivated P z w ∂familyRestLaw P m) =
      P.variance * (if u = w then 1 else 0) := by
  classical
  by_cases huw : u = w
  · subst w
    simpa [← pow_two] using integral_familyActivated_sq P u
  · rw [if_neg huw, mul_zero, familyRestLaw,
      integral_prod_symm _ (integrable_family_finite _ _)]
    have he (y : Bool × FamilySigns m) :
        (∫ z : FamilySigns m, familyActivated P (z, y) u * familyActivated P (z, y) w
          ∂familySignLaw m) = 0 := by
      have hpoint : (fun z : FamilySigns m => familyActivated P (z, y) u * familyActivated P (z, y) w) =
          fun z => (P.amplitude * familyIndicator y.1 * familyIndicator (y.2 u) *
            (P.amplitude * familyIndicator y.1 * familyIndicator (y.2 w))) *
              (familySign (z u) * familySign (z w)) := by
        funext z
        unfold familyActivated
        ring
      rw [hpoint, integral_const_mul, integral_familySignLaw_product, if_neg huw, mul_zero]
    simp_rw [he]
    simp

theorem integral_familyObservation (P : SymmetricFamilyParameters) {m : ℕ} (r : Fin (m * m)) :
    (∫ z, familyObservation P z r ∂familySeedLaw P m) = 0 := by
  rw [familySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns m,
      P.scale * familySign (z (finProdFinEquiv.symm r).1) +
        familyActivated P y (finProdFinEquiv.symm r).2 ∂familySignLaw m) ∂familyRestLaw P m) = 0
  simp_rw [integral_familySignLaw_affine]
  exact integral_familyActivated P _

theorem integral_familyObservation_product (P : SymmetricFamilyParameters) {m : ℕ}
    (r r' : Fin (m * m)) :
    (∫ z, familyObservation P z r * familyObservation P z r' ∂familySeedLaw P m) =
      familyCovariance m P.variance r r' := by
  classical
  rw [familySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns m,
      (P.scale * familySign (z (finProdFinEquiv.symm r).1) +
        familyActivated P y (finProdFinEquiv.symm r).2) *
      (P.scale * familySign (z (finProdFinEquiv.symm r').1) +
        familyActivated P y (finProdFinEquiv.symm r').2) ∂familySignLaw m) ∂familyRestLaw P m) = _
  simp_rw [integral_familySignLaw_affine_product]
  rw [integral_family_finite_add, integral_const, measureReal_univ_eq_one, one_smul,
    integral_familyActivated_product, P.scale_sq]
  rfl

theorem integral_familyObservation_fourth (P : SymmetricFamilyParameters) {m : ℕ}
    (r : Fin (m * m)) :
    (∫ z, familyObservation P z r ^ 4 ∂familySeedLaw P m) =
      1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4 := by
  rw [familySeedLaw, integral_prod_symm _ (integrable_family_finite _ _)]
  change (∫ y, (∫ z : FamilySigns m,
      (P.scale * familySign (z (finProdFinEquiv.symm r).1) +
        familyActivated P y (finProdFinEquiv.symm r).2) ^ 4 ∂familySignLaw m) ∂familyRestLaw P m) = _
  simp_rw [integral_familySignLaw_affine_fourth]
  simp only [integral_family_finite_add, integral_const_mul, integral_familyActivated_sq,
    integral_familyActivated_fourth, integral_const, measureReal_univ_eq_one, one_smul]
  have hs := P.scale_sq
  nlinarith [sq_nonneg (P.scale ^ 2 - (1 - P.variance))]

end
end RectangleCLT.Companion.SplitV4
