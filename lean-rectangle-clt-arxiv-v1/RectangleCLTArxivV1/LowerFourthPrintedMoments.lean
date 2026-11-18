import RectangleCLTArxivV1.LowerFourthParameters

/-! The literal quartic envelope estimate displayed in the printed
fourth-moment construction. This supplements the frozen L4-norm proof. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

theorem lower_fourth_power_add_le (s t : ℝ) : (s + t) ^ 4 ≤ 8 * (s ^ 4 + t ^ 4) := by
  nlinarith [sq_nonneg ((s - t) ^ 2), sq_nonneg (s ^ 2 - t ^ 2)]

theorem lowerFamilyRawObservations_fourth_envelope_le (P : SymmetricFamilyParameters)
    {n r m : ℕ} (i : Fin n) :
    (∫ z, ‖lowerFamilyRawObservations P i z‖ ^ 4 ∂lowerFamilyArrayLaw P n r m) ≤
      8 * (P.scale ^ 4 + P.theta * P.amplitude ^ 4) := by
  have heq := ((lowerFamilyRawObservations_identDistrib P (r := r) (m := m) i).comp
    (measurable_norm.pow_const (4 : ℕ))).integral_eq
  change (∫ z, ‖lowerFamilyRawObservations P i z‖ ^ 4 ∂lowerFamilyArrayLaw P n r m) =
    ∫ z, ‖lowerFamilyObservation P z‖ ^ 4 ∂lowerFamilySeedLaw P r m at heq
  rw [heq]
  have hactivation : (∫ z : LowerFamilySeed r m, (P.amplitude * familyIndicator z.2.2.1) ^ 4
      ∂lowerFamilySeedLaw P r m) = P.theta * P.amplitude ^ 4 := by
    rw [integral_lowerFamilySeed_indicator_function P r m
      (fun b => (P.amplitude * familyIndicator b) ^ 4), integral_familyBernoulli]
    simp [familyIndicator, familyTheta]
  calc
    _ ≤ ∫ z : LowerFamilySeed r m, 8 * (P.scale ^ 4 +
        (P.amplitude * familyIndicator z.2.2.1) ^ 4) ∂lowerFamilySeedLaw P r m := by
      apply integral_mono (integrable_family_finite _ _) (integrable_family_finite _ _)
      intro z
      exact (pow_le_pow_left₀ (norm_nonneg _) (lowerFamilyObservation_norm_le P z) 4).trans
        (lower_fourth_power_add_le _ _)
    _ = _ := by
      rw [integral_const_mul, integral_add (integrable_const _) (integrable_family_finite _ _),
        integral_const, measureReal_univ_eq_one, one_smul, hactivation]

theorem eventually_lowerFourth_printed_envelope {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ i : Fin n,
      (∫ z, ‖lowerFamilyRawObservations (lowerFourthParameters m n) i z‖ ^ 4
        ∂lowerFamilyArrayLaw (lowerFourthParameters m n) n (r n) (m n)) ≤
        8 * ((lowerFourthParameters m n).scale ^ 4 +
          (lowerFourthParameters m n).theta * (lowerFourthParameters m n).amplitude ^ 4) ∧
      8 * ((lowerFourthParameters m n).scale ^ 4 +
          (lowerFourthParameters m n).theta * (lowerFourthParameters m n).amplitude ^ 4) ≤ 16 := by
  filter_upwards [eventually_lowerFourth_fourth_factor hr hm hmTop hsmall] with n hn
  intro i
  refine ⟨lowerFamilyRawObservations_fourth_envelope_le _ i, ?_⟩
  rw [hn]
  have hs := pow_le_pow_left₀ (lowerFourthParameters m n).scale_pos.le
    (familyScale_le_one (lowerFourthParameters m n)) 4
  norm_num at hs
  linarith

theorem eventually_lowerFourth_variance_sqrt {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (lowerFourthParameters m n).variance = Real.sqrt (lowerFourthParameters m n).theta := by
  filter_upwards [eventually_lowerFourth_fourth_factor hr hm hmTop hsmall] with n hn
  let P := lowerFourthParameters m n
  have hp : P.pi = 1 := lowerUnmaskedSequence_pi _ _ _
  have hv : P.variance = P.theta * P.amplitude ^ 2 := by
    unfold SymmetricFamilyParameters.variance
    rw [hp, mul_one]
  symm
  apply (Real.sqrt_eq_iff_eq_sq P.theta_pos.le P.variance_pos.le).mpr
  rw [hv]
  change P.theta * P.amplitude ^ 4 = 1 at hn
  calc
    P.theta = P.theta * (P.theta * P.amplitude ^ 4) := by rw [hn, mul_one]
    _ = _ := by ring

end
end RectangleCLTArxivV1
