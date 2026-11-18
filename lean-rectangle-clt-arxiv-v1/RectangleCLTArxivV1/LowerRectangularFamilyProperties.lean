import RectangleCLTArxivV1.LowerRectangularFamilyMoments

/-! Raw iid moments and actual normalized covariance for independent counts. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

theorem lowerFamilyRawObservations_centered (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) (k : Fin (r * m)) :
    (∫ z, lowerFamilyRawObservations P i z k ∂lowerFamilyArrayLaw P n r m) = 0 := by
  have hi := (lowerFamilyRawObservations_identDistrib P (m := m) i).comp (measurable_pi_apply k)
  exact hi.integral_eq.trans (integral_lowerFamilyObservation P k)

theorem lowerFamilyRawObservations_second (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) (k l : Fin (r * m)) :
    (∫ z, lowerFamilyRawObservations P i z k * lowerFamilyRawObservations P i z l ∂lowerFamilyArrayLaw P n r m) =
      lowerFamilyCovariance r m P.variance k l := by
  have hi := (lowerFamilyRawObservations_identDistrib P (m := m) i).comp
    ((measurable_pi_apply k).mul (measurable_pi_apply l))
  exact hi.integral_eq.trans (integral_lowerFamilyObservation_product P k l)

theorem lowerFamilyRawObservations_fourth (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) (k : Fin (r * m)) :
    (∫ z, lowerFamilyRawObservations P i z k ^ 4 ∂lowerFamilyArrayLaw P n r m) =
      1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4 := by
  have hi := (lowerFamilyRawObservations_identDistrib P (m := m) i).comp
    ((measurable_pi_apply k).pow_const 4)
  exact hi.integral_eq.trans (integral_lowerFamilyObservation_fourth P k)

theorem lowerFamilyRawObservations_boundedIndependent (P : SymmetricFamilyParameters) (n r m : ℕ) :
    BoundedIndependentHypotheses (lowerFamilyArrayLaw P n r m) (lowerFamilyRawObservations P)
      (P.scale + P.amplitude) := by
  refine ⟨fun _ => measurable_of_finite _, lowerFamilyRawObservations_independent P n r m,
    lowerFamilyRawObservations_centered P, ?_, add_nonneg P.scale_pos.le P.amplitude_pos.le⟩
  intro i
  exact Filter.Eventually.of_forall (fun z => lowerFamilyObservation_envelope P (z i))

def lowerFamilyNormalizedObservations (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) (z : Fin n → LowerFamilySeed r m) : Vector (r * m) :=
  (1 / Real.sqrt n) • lowerFamilyRawObservations P i z

theorem lowerFamilyNormalizedObservations_covariance (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1 ≤ n) :
    covariance (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P)) =
      lowerFamilyCovariance r m P.variance := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hh := (lowerFamilyRawObservations_boundedIndependent P n r m).covariance_sum_smul (1 / Real.sqrt n)
  change covariance (lowerFamilyArrayLaw P n r m)
    (sumVector (fun i z => (1 / Real.sqrt n) • lowerFamilyRawObservations P i z)) = _
  ext k l
  rw [hh]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [(lowerFamilyRawObservations_boundedIndependent P n r m).covariance_sum]
  simp_rw [lowerFamilyRawObservations_second]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_pow, one_pow, Real.sq_sqrt hnpos.le]
  field_simp

theorem lowerFamilyCovariance_unit_diagonal (r m : ℕ) (v : ℝ) (k : Fin (r*m)) :
    lowerFamilyCovariance r m v k k = 1 := by
  simp only [lowerFamilyCovariance,if_true,mul_one]
  ring

theorem lowerFamilyNormalizedObservations_unit_covariance (P : SymmetricFamilyParameters)
    {n r m : ℕ} (hn : 1≤n) (k : Fin (r*m)) :
    covariance (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P)) k k = 1 := by
  rw [lowerFamilyNormalizedObservations_covariance P hn]
  exact lowerFamilyCovariance_unit_diagonal r m P.variance k

end
end RectangleCLTArxivV1
