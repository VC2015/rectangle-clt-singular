import RectangleCLTArxivV1.LowerDenseParameters
import RectangleCLTArxivV1.PairedIntrinsicBennett

/-! The literal fourth-moment lower construction and its actual moment
membership under the width-sensitive regime. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerFourthParameters (m : ℕ → ℕ) (n : ℕ) : SymmetricFamilyParameters :=
  lowerDenseParameters 4 (fun _ => 2) m n

def lowerFourthWidthRate (n r m : ℕ) : ℝ :=
  independentAbsGaussianMean r * dimensionLog (r * m) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)

theorem lowerDense_four_rate (n r m : ℕ) :
    lowerDenseWidthRate 4 2 n r m = 2 * lowerFourthWidthRate n r m := by
  norm_num [lowerDenseWidthRate, lowerFourthWidthRate]
  ring

theorem tendsto_lowerFourth_dense_rate {r m : ℕ → ℕ}
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    Tendsto (fun n => lowerDenseWidthRate 4 2 n (r n) (m n)) atTop (𝓝 0) := by
  simpa only [lowerDense_four_rate, mul_zero] using hsmall.const_mul 2

/-- The exact printed fourth-power activation budget. -/
theorem eventually_lowerFourth_fourth_factor {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, (lowerFourthParameters m n).theta * (lowerFourthParameters m n).amplitude ^ 4 = 1 := by
  have hs := tendsto_lowerFourth_dense_rate hsmall
  have hraw := tendsto_lowerDense_raw_width_scale (by norm_num : (2 : ℝ) < 4)
    (fun _ => le_rfl : ∀ _ : ℕ, (2 : ℝ) ≤ 2) hr hm hs
  have ha := eventually_lowerDenseAmplitude_ge_one (by norm_num : (2 : ℝ) < 4)
    (fun _ => le_rfl : ∀ _ : ℕ, (2 : ℝ) ≤ 2) hr hm hmTop hs
  filter_upwards [eventually_lowerUnmaskedSequence_fields hr hm hmTop ha hraw,eventually_ge_atTop 1]
    with n hfields hn
  rcases hfields with ⟨hθ, hamp, _⟩
  change (lowerFourthParameters m n).theta = _ at hθ
  change (lowerFourthParameters m n).amplitude = _ at hamp
  rw [hθ, hamp, lowerDenseAmplitude]
  have hell : 0 < Real.log (m n : ℝ) := Real.log_pos (by exact_mod_cast (by have := hm n; omega : 1 < m n))
  have ht : 0 < Real.log (m n : ℝ) / (2 * n) := by positivity
  have hh := lowerDenseAmplitude_moment_identity ht 4 2 4
  norm_num at hh ⊢
  exact hh

theorem eventually_lowerFourth_coordinate_fourth {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, ∀ i : Fin n, ∀ j : Fin (r n * m n),
      (∫ z, lowerFamilyRawObservations (lowerFourthParameters m n) i z j ^ 4
        ∂lowerFamilyArrayLaw (lowerFourthParameters m n) n (r n) (m n)) ≤ 14 / 5 := by
  filter_upwards [eventually_lowerFourth_fourth_factor hr hm hmTop hsmall] with n hn
  intro i j
  rw [lowerFamilyRawObservations_fourth]
  have hp : (lowerFourthParameters m n).pi = 1 := lowerUnmaskedSequence_pi _ _ _
  rw [hp, mul_one, hn]
  nlinarith [sq_nonneg ((lowerFourthParameters m n).variance - 2 / 5)]

theorem eventually_lowerFourth_membership {r m : ℕ → ℕ}
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 2 ≤ m n) (hmTop : Tendsto m atTop atTop)
    (hsmall : Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0)) :
    ∀ᶠ n in atTop, PolynomialFourthHypotheses
      (lowerFamilyArrayLaw (lowerFourthParameters m n) n (r n) (m n))
      (lowerFamilyRawObservations (lowerFourthParameters m n)) 4 2 := by
  filter_upwards [eventually_lowerDense_envelope (by norm_num : (2 : ℝ) < 4)
    (fun _ => le_rfl : ∀ _ : ℕ, (2 : ℝ) ≤ 2) hr hm hmTop (tendsto_lowerFourth_dense_rate hsmall),
    eventually_lowerFourth_fourth_factor hr hm hmTop hsmall,eventually_ge_atTop 1]
    with n henv hfour hn
  apply lowerFamily_polynomialFourth_of_moments _ hn henv
  have hp : (lowerFourthParameters m n).pi = 1 := lowerUnmaskedSequence_pi _ _ _
  change _ + (lowerFourthParameters m n).theta * (lowerFourthParameters m n).pi *
    (lowerFourthParameters m n).amplitude ^ 4 ≤ _
  rw [hp, mul_one, hfour]
  nlinarith [sq_nonneg ((lowerFourthParameters m n).variance - 2 / 5)]

/-- Theorem5's actual iid centrally symmetric construction inC4(2),
including the width profile and the signed detecting orthant. -/
theorem theorem_5_fourth_moment_lower :
    ∃ c : ℝ, 0 < c ∧ ∀ (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) /
        independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerFourthParameters m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerFourthParameters m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerFourthParameters m n)) 4 2 ∧
        c * (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
          lowerFamilyShiftedCDFDifference (lowerFourthParameters m n) n (r n) (m n) (lowerLeadingThreshold (r n)) ∧
        c * (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
          lowerFamilyComparisonDistance (lowerFourthParameters m n) n (r n) (m n) := by
  obtain ⟨c, hc, hlower⟩ := theorem_7_polynomial_envelope_lower 4 (by norm_num)
  refine ⟨2 * c, by positivity, ?_⟩
  intro r m _ _ hr hm hrm hmTop hsmall
  obtain ⟨hw, hevent⟩ := hlower (fun _ => 2) r m (fun _ => le_rfl) hr hm hrm hmTop
    (tendsto_lowerFourth_dense_rate hsmall)
  refine ⟨hw, ?_⟩
  filter_upwards [hevent, eventually_lowerFourth_membership hr hm hmTop hsmall] with n hn hfour
  refine ⟨hn.1, hfour, ?_, ?_⟩
  · convert hn.2.2.1 using 1
    norm_num [lowerFourthParameters]
    ring
  · convert hn.2.2.2 using 1
    norm_num [lowerFourthParameters]
    ring

theorem lowerFamily_normalizedObservationSum_eq (P : SymmetricFamilyParameters) (n r m : ℕ) :
    normalizedObservationSum (lowerFamilyRawObservations P : Fin n → (Fin n → LowerFamilySeed r m) → Vector (r * m)) =
      sumVector (lowerFamilyNormalizedObservations P) := by
  funext z
  simp only [normalizedObservationSum, sumVector, lowerFamilyNormalizedObservations, Finset.smul_sum, one_div]

theorem fourthWidthRate_fixed_budget_identity (n p : ℕ) (g : ℝ) :
    polynomialFourthWidthRate n p 2 4 g =
      ((2 : ℝ) ^ (1 / 2 : ℝ) + 2 / Real.log (Real.exp 1 + 2) ^ (3 / 4 : ℝ)) *
        (g * dimensionLog p ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) := by
  norm_num [polynomialFourthWidthRate]
  ring

/-- The matching upper bound comes from the actual new Theorem2(ii),
applied to the same finite observations and covariance factor. -/
theorem exists_lowerFourth_upper_constant :
    ∃ C : ℝ, 0 < C ∧ ∀ (P : SymmetricFamilyParameters) (n r m : ℕ),
      1 ≤ n → 1 ≤ r → 1 ≤ m →
      PolynomialFourthHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) 4 2 →
      lowerFamilyComparisonDistance P n r m ≤
        C * (gaussianMaximumMean (lowerFamilyGaussianFactor P r m) *
          dimensionLog (r * m) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨C, hC, hbound⟩ := theorem_2_ii_intrinsic 4 (by norm_num)
  let K := (2 : ℝ) ^ (1 / 2 : ℝ) + 2 / Real.log (Real.exp 1 + 2) ^ (3 / 4 : ℝ)
  have hK : 0 < K := by
    have hh : 0 < Real.log (Real.exp 1 + 2) := Real.log_pos (by linarith [Real.exp_pos (1 : ℝ)])
    dsimp [K]
    positivity
  refine ⟨C * K, mul_pos hC hK, ?_⟩
  intro P n r m hn hr hm hX
  have hW := lowerFamily_normalizedObservationSum_eq P n r m
  have hA : lowerFamilyGaussianFactor P r m * (lowerFamilyGaussianFactor P r m).transpose =
      covariance (lowerFamilyArrayLaw P n r m) (normalizedObservationSum (lowerFamilyRawObservations P)) := by
    rw [hW, lowerFamilyNormalizedObservations_covariance P hn]
    exact lowerFamilyGaussianFactor_gram P r m
  have hh := hbound (r * m) n (by nlinarith : 1 ≤ r * m) hn 2 (by norm_num)
    (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P) hX (lowerFamilyGaussianFactor P r m) hA
  rw [hW] at hh
  apply hh.trans
  apply (mul_le_mul_of_nonneg_left (min_le_right _ _) hC.le).trans_eq
  rw [fourthWidthRate_fixed_budget_identity]
  change C * (K * _) = _
  ring

/-- The full two-sided conclusion of Theorem5 for the actual constructed
laws. Both constants are universal and precede the coordinate counts. -/
theorem theorem_5_fourth_moment_two_sided :
    ∃ c C : ℝ, 0 < c ∧ 0 < C ∧ ∀ (r m : ℕ → ℕ)
      [∀ n, NeZero (r n)] [∀ n, NeZero (m n)],
      (∀ n, 1 ≤ r n) → (∀ n, 2 ≤ m n) → (∀ n, r n ≤ m n) → Tendsto m atTop atTop →
      Tendsto (fun n => lowerFourthWidthRate n (r n) (m n)) atTop (𝓝 0) →
      Tendsto (fun n => gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) /
        independentAbsGaussianMean (r n)) atTop (𝓝 1) ∧
      ∀ᶠ n in atTop,
        LowerRectangularFamilyProperties (lowerFourthParameters m n) n (r n) (m n) ∧
        PolynomialFourthHypotheses (lowerFamilyArrayLaw (lowerFourthParameters m n) n (r n) (m n))
          (lowerFamilyRawObservations (lowerFourthParameters m n)) 4 2 ∧
        c * (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) *
          dimensionLog (r n * m n) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) ≤
          lowerFamilyComparisonDistance (lowerFourthParameters m n) n (r n) (m n) ∧
        lowerFamilyComparisonDistance (lowerFourthParameters m n) n (r n) (m n) ≤
          C * (gaussianMaximumMean (lowerFamilyGaussianFactor (lowerFourthParameters m n) (r n) (m n)) *
            dimensionLog (r n * m n) ^ (3 / 4 : ℝ) / (n : ℝ) ^ (1 / 4 : ℝ)) := by
  obtain ⟨c, hc, hlower⟩ := theorem_5_fourth_moment_lower
  obtain ⟨C, hC, hupper⟩ := exists_lowerFourth_upper_constant
  refine ⟨c, C, hc, hC, ?_⟩
  intro r m _ _ hr hm hrm hmTop hsmall
  obtain ⟨hw, hevent⟩ := hlower r m hr hm hrm hmTop hsmall
  refine ⟨hw, ?_⟩
  filter_upwards [hevent, eventually_ge_atTop 1] with n hn hnn
  exact ⟨hn.1, hn.2.1, hn.2.2.2, hupper _ n (r n) (m n) hnn (hr n) (by have := hm n; omega) hn.2.1⟩

end
end RectangleCLTArxivV1
