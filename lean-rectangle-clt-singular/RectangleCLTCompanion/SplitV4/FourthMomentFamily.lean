import RectangleCLTCompanion.SplitV4.SymmetricBoundedParameters
import RectangleCLTCompanion.SplitV4.FourthLowerCalibrationScales
import RectangleCLTCompanion.SplitV4.PolynomialUniform

/-! The genuine unmasked fourth-moment lower model: amplitude θ^(-1/4).
The fallback only assigns valid laws at irrelevant initial indices. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators ENNReal Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def unmaskedFourthParameters (θ : ℝ) (hθ0 : 0 < θ) (hθquarter : θ < 1/4) : SymmetricFamilyParameters where
  theta := θ
  pi := 1
  amplitude := θ^(-1/4 : ℝ)
  theta_pos := hθ0
  theta_le_one := by linarith
  pi_pos := by norm_num
  pi_le_one := le_rfl
  amplitude_pos := Real.rpow_pos_of_pos hθ0 _
  variance_lt_half := by
    rw [mul_one, fourth_amplitude_square_identity hθ0]
    have hs := Real.sq_sqrt hθ0.le
    have hs0 := Real.sqrt_nonneg θ
    nlinarith

def fourthFamilyParameters (n m : ℕ) : SymmetricFamilyParameters :=
  if h : 0 < fourthLowerTheta n (Real.log (m : ℝ)) ∧ fourthLowerTheta n (Real.log (m : ℝ)) < 1/4 then
    unmaskedFourthParameters (fourthLowerTheta n (Real.log (m : ℝ))) h.1 h.2
  else unmaskedUnitParameters (1/4) (by norm_num) (by norm_num)

theorem fourthFamilyParameters_pi (n m : ℕ) : (fourthFamilyParameters n m).pi = 1 := by
  unfold fourthFamilyParameters
  split_ifs <;> rfl

theorem fourthFamilyParameters_theta {n m : ℕ}
    (hθ0 : 0 < fourthLowerTheta n (Real.log (m : ℝ)))
    (hθquarter : fourthLowerTheta n (Real.log (m : ℝ)) < 1/4) :
    (fourthFamilyParameters n m).theta = fourthLowerTheta n (Real.log (m : ℝ)) := by
  have hg : 0 < fourthLowerTheta n (Real.log (m : ℝ)) ∧ fourthLowerTheta n (Real.log (m : ℝ)) < 1/4 := ⟨hθ0,hθquarter⟩
  simp only [fourthFamilyParameters, dif_pos hg, unmaskedFourthParameters]

theorem fourthFamilyParameters_amplitude {n m : ℕ}
    (hθ0 : 0 < fourthLowerTheta n (Real.log (m : ℝ)))
    (hθquarter : fourthLowerTheta n (Real.log (m : ℝ)) < 1/4) :
    (fourthFamilyParameters n m).amplitude = fourthLowerAmplitude n (Real.log (m : ℝ)) := by
  have hg : 0 < fourthLowerTheta n (Real.log (m : ℝ)) ∧ fourthLowerTheta n (Real.log (m : ℝ)) < 1/4 := ⟨hθ0,hθquarter⟩
  simp only [fourthFamilyParameters, dif_pos hg, unmaskedFourthParameters, fourthLowerAmplitude]

theorem fourthFamilyParameters_envelope_factor (n m : ℕ) :
    (fourthFamilyParameters n m).amplitude * (fourthFamilyParameters n m).theta^(1/4 : ℝ) ≤ 1 := by
  unfold fourthFamilyParameters
  split_ifs with h
  · exact (fourth_amplitude_inverse_identity h.1).le
  · change (1 : ℝ)*(1/4 : ℝ)^(1/4 : ℝ) ≤ 1
    rw [one_mul]
    exact Real.rpow_le_one (by norm_num) (by norm_num) (by norm_num)

theorem fourthFamilyParameters_fourth_factor (n m : ℕ) :
    (fourthFamilyParameters n m).theta * (fourthFamilyParameters n m).pi *
      (fourthFamilyParameters n m).amplitude^4 ≤ 1 := by
  rw [fourthFamilyParameters_pi, mul_one]
  unfold fourthFamilyParameters
  split_ifs with h
  · exact (fourth_amplitude_fourth_identity h.1).le
  · change (1/4 : ℝ)*1^4 ≤ 1
    norm_num

theorem fourthFamily_observations_envelope_moment (n m : ℕ) (i : Fin n) :
    (∫ z, ‖familyRawObservations (fourthFamilyParameters n m) i z‖^(4 : ℝ)
      ∂familyArrayLaw (fourthFamilyParameters n m) n m) ≤ 2^(4 : ℝ) := by
  let P := fourthFamilyParameters n m
  have hroot := familyRawObservations_Lq_envelope P (m := m) i (q := 4) (by norm_num)
  have htwo : P.scale + P.amplitude * P.theta^(1/(4 : ℝ)) ≤ 2 := by
    have hs := familyScale_le_one P
    have ha := fourthFamilyParameters_envelope_factor n m
    change P.amplitude*P.theta^(1/4 : ℝ) ≤ 1 at ha
    linarith
  have hI : 0 ≤ ∫ z, ‖familyRawObservations P i z‖^(4 : ℝ) ∂familyArrayLaw P n m :=
    integral_nonneg (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hh := Real.rpow_le_rpow (Real.rpow_nonneg hI (1/4 : ℝ)) (hroot.trans htwo) (by norm_num : (0 : ℝ) ≤ 4)
  rw [← Real.rpow_mul hI, show (1/(4 : ℝ))*4 = 1 by norm_num, Real.rpow_one] at hh
  exact hh

theorem fourthFamily_observations_coordinate_fourth (n m : ℕ) (i : Fin n) (j : Fin (m*m)) :
    (∫ z, familyRawObservations (fourthFamilyParameters n m) i z j ^ 4
      ∂familyArrayLaw (fourthFamilyParameters n m) n m) ≤ (2 : ℝ)^2 := by
  rw [familyRawObservations_fourth]
  have hv := (fourthFamilyParameters n m).variance_lt_half
  change (fourthFamilyParameters n m).variance < 1/2 at hv
  have hf := fourthFamilyParameters_fourth_factor n m
  nlinarith only [hv, hf, sq_nonneg (fourthFamilyParameters n m).variance]

/-- Membership in the literal polynomial class, including the genuine
fourth moments and average marginal variance. -/
theorem fourthFamily_polynomialIndependent {n m : ℕ} (hn : 1 ≤ n) :
    PolynomialIndependentHypotheses (familyArrayLaw (fourthFamilyParameters n m) n m)
      (familyRawObservations (fourthFamilyParameters n m)) 4 2 := by
  let P := fourthFamilyParameters n m
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_zero_of_lt hn)
  refine ⟨fun _ => measurable_of_finite _, familyRawObservations_independent P n m,
    familyRawObservations_centered P, fun _ => integrable_family_finite _ _,
    fun _ _ => integrable_family_finite _ _, ?_, fourthFamily_observations_envelope_moment n m, ?_⟩
  · intro j
    simp_rw [pow_two, familyRawObservations_second, familyCovariance_unit_diagonal]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    simpa only [one_div] using inv_mul_cancel₀ hN
  · intro j
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun i _ => fourthFamily_observations_coordinate_fourth n m i j)
    have hdiv := mul_le_mul_of_nonneg_left hh (by positivity : 0 ≤ 1/(n : ℝ))
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
      ← mul_assoc, one_div, inv_mul_cancel₀ hN, one_mul] using hdiv

end
end RectangleCLT.Companion.SplitV4
