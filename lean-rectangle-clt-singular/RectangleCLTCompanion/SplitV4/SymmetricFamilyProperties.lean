import RectangleCLTCompanion.SplitV4.SymmetricFamily
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMoments
import RectangleCLTCompanion.SplitV4.SymmetricFamilyGeometry

/-! Exact iid moments and normalized covariance for Lemma F.3's actual law. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyRawObservations_centered (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (r : Fin (m * m)) :
    (∫ z, familyRawObservations P i z r ∂familyArrayLaw P n m) = 0 := by
  have hi := (familyRawObservations_identDistrib P (m := m) i).comp (measurable_pi_apply r)
  exact hi.integral_eq.trans (integral_familyObservation P r)

theorem familyRawObservations_second (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (r r' : Fin (m * m)) :
    (∫ z, familyRawObservations P i z r * familyRawObservations P i z r' ∂familyArrayLaw P n m) =
      familyCovariance m P.variance r r' := by
  have hi := (familyRawObservations_identDistrib P (m := m) i).comp
    ((measurable_pi_apply r).mul (measurable_pi_apply r'))
  exact hi.integral_eq.trans (integral_familyObservation_product P r r')

theorem familyRawObservations_fourth (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (r : Fin (m * m)) :
    (∫ z, familyRawObservations P i z r ^ 4 ∂familyArrayLaw P n m) =
      1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4 := by
  have hi := (familyRawObservations_identDistrib P (m := m) i).comp
    ((measurable_pi_apply r).pow_const 4)
  exact hi.integral_eq.trans (integral_familyObservation_fourth P r)

theorem familyRawObservations_boundedIndependent (P : SymmetricFamilyParameters) (n m : ℕ) :
    BoundedIndependentHypotheses (familyArrayLaw P n m) (familyRawObservations P)
      (P.scale + P.amplitude) := by
  refine ⟨fun _ => measurable_of_finite _, familyRawObservations_independent P n m,
    familyRawObservations_centered P, ?_, add_nonneg P.scale_pos.le P.amplitude_pos.le⟩
  intro i
  exact Filter.Eventually.of_forall (fun z => familyObservation_envelope P (z i))

def familyNormalizedObservations (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (z : Fin n → FamilySeed m) : Vector (m * m) :=
  (1 / Real.sqrt n) • familyRawObservations P i z

theorem familyNormalizedObservations_covariance (P : SymmetricFamilyParameters)
    {n m : ℕ} (hn : 1 ≤ n) :
    covariance (familyArrayLaw P n m) (sumVector (familyNormalizedObservations P)) =
      familyCovariance m P.variance := by
  classical
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hh := (familyRawObservations_boundedIndependent P n m).covariance_sum_smul (1 / Real.sqrt n)
  change covariance (familyArrayLaw P n m)
    (sumVector (fun i z => (1 / Real.sqrt n) • familyRawObservations P i z)) = _
  ext r r'
  rw [hh]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [(familyRawObservations_boundedIndependent P n m).covariance_sum]
  simp_rw [familyRawObservations_second]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    div_pow, one_pow, Real.sq_sqrt hnpos.le]
  field_simp

theorem familyNormalizedObservations_rank (P : SymmetricFamilyParameters)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) :
    Matrix.rank (covariance (familyArrayLaw P n m) (sumVector (familyNormalizedObservations P))) =
      2 * m - 1 := by
  rw [familyNormalizedObservations_covariance P hn]
  exact familyCovariance_rank hm P.variance_pos (lt_trans P.variance_lt_half (by norm_num))

theorem familyNormalizedObservations_pairGap (P : SymmetricFamilyParameters)
    {n m : ℕ} (hn : 1 ≤ n) (hm : 2 ≤ m) :
    pairGap
      (covariance (familyArrayLaw P n m) (sumVector (familyNormalizedObservations P))) = P.variance := by
  rw [familyNormalizedObservations_covariance P hn]
  exact familyCovariance_pairGap hm P.variance_pos P.variance_lt_half

end
end RectangleCLT.Companion.SplitV4
