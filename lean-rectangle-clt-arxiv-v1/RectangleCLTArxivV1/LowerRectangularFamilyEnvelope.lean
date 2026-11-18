import RectangleCLTArxivV1.LowerRectangularFamilyProperties

/-! The actual Lq envelope of the independent-count symmetric family. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

theorem integral_lowerFamilySeed_indicator_function (P : SymmetricFamilyParameters) (r m : ℕ) (f : Bool → ℝ) :
    (∫ z : LowerFamilySeed r m, f z.2.2.1 ∂lowerFamilySeedLaw P r m) = ∫ b, f b ∂familyBernoulli (familyTheta P) := by
  have h1 := MeasureTheory.integral_fun_snd (μ := familySignLaw r) (ν := familyRestLaw P m)
    (fun z : FamilySigns m × (Bool × FamilySigns m) => f z.2.1)
  have h2 := MeasureTheory.integral_fun_snd (μ := familySignLaw m)
    (ν := (familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))
    (fun z : Bool × FamilySigns m => f z.1)
  have h3 := MeasureTheory.integral_fun_fst (μ := familyBernoulli (familyTheta P))
    (ν := familyMaskLaw P m) f
  simp only [measureReal_univ_eq_one, one_smul] at h1 h2 h3
  exact h1.trans (h2.trans h3)


theorem integral_lowerFamilyActivation_rpow (P : SymmetricFamilyParameters) (r m : ℕ)
    {q : ℝ} (hq : 0 < q) :
    (∫ z : LowerFamilySeed r m, ‖P.amplitude * familyIndicator z.2.2.1‖ ^ q ∂lowerFamilySeedLaw P r m) =
      P.theta * P.amplitude ^ q := by
  rw [integral_lowerFamilySeed_indicator_function P r m
    (fun b => ‖P.amplitude * familyIndicator b‖ ^ q), integral_familyBernoulli]
  simp [familyIndicator, Real.norm_eq_abs, abs_of_pos P.amplitude_pos,
    Real.zero_rpow hq.ne', familyTheta]

theorem family_rpow_q_root {a q : ℝ} (ha : 0 ≤ a) (hq : 0 < q) :
    (a ^ q) ^ (1 / q) = a := by
  rw [← Real.rpow_mul ha]
  simp [hq.ne']

theorem lowerFamilyObservation_Lq_envelope (P : SymmetricFamilyParameters) (r m : ℕ)
    {q : ℝ} (hq : 1 ≤ q) :
    (∫ z : LowerFamilySeed r m, ‖lowerFamilyObservation P z‖ ^ q ∂lowerFamilySeedLaw P r m) ^ (1 / q) ≤
      P.scale + P.amplitude * P.theta ^ (1 / q) := by
  have hqpos : 0 < q := lt_of_lt_of_le zero_lt_one hq
  have hnonneg (z : LowerFamilySeed r m) : 0 ≤ P.scale + P.amplitude * familyIndicator z.2.2.1 :=
    add_nonneg P.scale_pos.le (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _))
  have hmono : (∫ z : LowerFamilySeed r m, ‖lowerFamilyObservation P z‖ ^ q ∂lowerFamilySeedLaw P r m) ≤
      ∫ z : LowerFamilySeed r m, ‖P.scale + P.amplitude * familyIndicator z.2.2.1‖ ^ q ∂lowerFamilySeedLaw P r m := by
    apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
    intro z
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg z)]
    exact Real.rpow_le_rpow (norm_nonneg _) (lowerFamilyObservation_norm_le P z) hqpos.le
  have htri := familyFinite_minkowski (lowerFamilySeedLaw P r m) (fun _ => P.scale)
    (fun z : LowerFamilySeed r m => P.amplitude * familyIndicator z.2.2.1) hq
  have hc : (∫ z : LowerFamilySeed r m, ‖P.scale‖ ^ q ∂lowerFamilySeedLaw P r m) ^ (1 / q) = P.scale := by
    simp only [integral_const, measureReal_univ_eq_one, one_smul, Real.norm_eq_abs,
      abs_of_pos P.scale_pos]
    exact family_rpow_q_root P.scale_pos.le hqpos
  have ha : (∫ z : LowerFamilySeed r m, ‖P.amplitude * familyIndicator z.2.2.1‖ ^ q
      ∂lowerFamilySeedLaw P r m) ^ (1 / q) = P.amplitude * P.theta ^ (1 / q) := by
    rw [integral_lowerFamilyActivation_rpow P r m hqpos,
      Real.mul_rpow P.theta_pos.le (Real.rpow_nonneg P.amplitude_pos.le q),
      family_rpow_q_root P.amplitude_pos.le hqpos]
    ring
  exact (Real.rpow_le_rpow (integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _))
    hmono (by positivity)).trans (by simpa only [hc, ha] using htri)

theorem lowerFamilyRawObservations_Lq_envelope (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) {q : ℝ} (hq : 1 ≤ q) :
    (∫ z, ‖lowerFamilyRawObservations P i z‖ ^ q ∂lowerFamilyArrayLaw P n r m) ^ (1 / q) ≤
      P.scale + P.amplitude * P.theta ^ (1 / q) := by
  have hi := (lowerFamilyRawObservations_identDistrib P (r := r) (m := m) i).comp
    (continuous_norm.measurable.pow_const q)
  have heq := hi.integral_eq
  change (∫ z, ‖lowerFamilyRawObservations P i z‖ ^ q ∂lowerFamilyArrayLaw P n r m) =
    ∫ z, ‖lowerFamilyObservation P z‖ ^ q ∂lowerFamilySeedLaw P r m at heq
  rw [heq]
  exact lowerFamilyObservation_Lq_envelope P r m hq

end
end RectangleCLTArxivV1
