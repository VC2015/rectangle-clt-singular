import RectangleCLTCompanion.SplitV4.SymmetricFamilyEnvelope

/-! Full actual-law endpoint for Lemma F.3 (lower:family-properties). -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem familyRawObservations_covariance (P : SymmetricFamilyParameters) {n m : ℕ} (i : Fin n) :
    covariance (familyArrayLaw P n m) (familyRawObservations P i) = familyCovariance m P.variance := by
  ext r r'
  simp only [covariance, familyRawObservations_centered, mul_zero, sub_zero]
  exact familyRawObservations_second P i r r'

theorem familyRawObservations_unit_variance (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (r : Fin (m * m)) :
    covariance (familyArrayLaw P n m) (familyRawObservations P i) r r = 1 := by
  rw [familyRawObservations_covariance]
  exact familyCovariance_unit_diagonal m P.variance r

theorem familyRawObservations_fourth_scale (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (r : Fin (m * m)) :
    (∫ z, familyRawObservations P i z r ^ 4 ∂familyArrayLaw P n m) =
      P.scale ^ 4 + 6 * P.scale ^ 2 * P.variance + P.theta * P.pi * P.amplitude ^ 4 := by
  rw [familyRawObservations_fourth]
  have hs := P.scale_sq
  nlinarith [sq_nonneg (P.scale ^ 2 - (1 - P.variance))]

/-- Every field is a conclusion about the explicit finite product law.
The structure contains no unproved probabilistic or moment hypotheses. -/
structure CommonSymmetricFamilyProperties (P : SymmetricFamilyParameters) (n m : ℕ) : Prop where
  independent : iIndepFun (familyRawObservations P (n := n) (m := m)) (familyArrayLaw P n m)
  identicallyDistributed : ∀ i k : Fin n, IdentDistrib
    (familyRawObservations P i : (Fin n → FamilySeed m) → Vector (m * m))
    (familyRawObservations P k) (familyArrayLaw P n m) (familyArrayLaw P n m)
  centered : ∀ (i : Fin n) (r : Fin (m * m)),
    (∫ z, familyRawObservations P i z r ∂familyArrayLaw P n m) = 0
  centrallySymmetric : ∀ i : Fin n, IdentDistrib
    (familyRawObservations P i : (Fin n → FamilySeed m) → Vector (m * m))
    (fun z => -familyRawObservations P i z) (familyArrayLaw P n m) (familyArrayLaw P n m)
  covariance : ∀ i : Fin n, RectangleCLT.covariance (familyArrayLaw P n m)
    (familyRawObservations P i) = familyCovariance m P.variance
  unitVariance : ∀ (i : Fin n) (r : Fin (m * m)),
    RectangleCLT.covariance (familyArrayLaw P n m) (familyRawObservations P i) r r = 1
  sumCovariance : RectangleCLT.covariance (familyArrayLaw P n m)
    (sumVector (familyNormalizedObservations P)) = familyCovariance m P.variance
  rank : Matrix.rank (familyCovariance m P.variance) = 2 * m - 1
  maxCorrelation : maxOffDiagonal (familyCovariance m P.variance) = 1 - P.variance
  correlationGap : pairGap (familyCovariance m P.variance) = P.variance
  fourthScale : ∀ (i : Fin n) (r : Fin (m * m)),
    (∫ z, familyRawObservations P i z r ^ 4 ∂familyArrayLaw P n m) =
      P.scale ^ 4 + 6 * P.scale ^ 2 * P.variance + P.theta * P.pi * P.amplitude ^ 4
  fourth : ∀ (i : Fin n) (r : Fin (m * m)),
    (∫ z, familyRawObservations P i z r ^ 4 ∂familyArrayLaw P n m) =
      1 + 4 * P.variance - 5 * P.variance ^ 2 + P.theta * P.pi * P.amplitude ^ 4
  envelope : ∀ (i : Fin n) (z : Fin n → FamilySeed m),
    ‖familyRawObservations P i z‖ ≤ P.scale + P.amplitude * familyIndicator (z i).2.2.1
  momentIntegrable : ∀ (i : Fin n) (q : ℝ),
    Integrable (fun z => ‖familyRawObservations P i z‖ ^ q) (familyArrayLaw P n m)
  LqEnvelope : ∀ (i : Fin n) (q : ℝ), 1 ≤ q →
    (∫ z, ‖familyRawObservations P i z‖ ^ q ∂familyArrayLaw P n m) ^ (1 / q) ≤
      P.scale + P.amplitude * P.theta ^ (1 / q)

/-- Lemma F.3 for the actual independent sign/activation/mask product model. -/
theorem symmetricFamilyProperties (P : SymmetricFamilyParameters) {n m : ℕ}
    (hn : 1 ≤ n) (hm : 2 ≤ m) : CommonSymmetricFamilyProperties P n m := by
  refine ⟨familyRawObservations_independent P n m, familyRawObservations_iid P,
    familyRawObservations_centered P, familyRawObservations_centrally_symmetric P,
    familyRawObservations_covariance P, familyRawObservations_unit_variance P,
    familyNormalizedObservations_covariance P hn,
    familyCovariance_rank (by omega) P.variance_pos (by have := P.variance_lt_half; change P.variance < 1 / 2 at this; linarith),
    familyCovariance_maxOffDiagonal hm P.variance_pos P.variance_lt_half,
    familyCovariance_pairGap hm P.variance_pos P.variance_lt_half,
    familyRawObservations_fourth_scale P, familyRawObservations_fourth P,
    familyRawObservations_norm_le P, ?_, ?_⟩
  · intro i q
    exact integrable_family_finite _ _
  · intro i q hq
    exact familyRawObservations_Lq_envelope P i hq

end
end RectangleCLT.Companion.SplitV4
