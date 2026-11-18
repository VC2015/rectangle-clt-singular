import RectangleCLTArxivV1.LowerRectangularFamilyOrthant
import RectangleCLTArxivV1.LowerRectangularFamilyEnvelope
import RectangleCLTArxivV1.LowerLeadingDensity

/-! The complete finite model in Lemma `lower:family-properties`. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- Every field concerns the explicitly constructed product law and its
actual observations; this structure is the theorem's output. -/
structure LowerRectangularFamilyProperties (P : SymmetricFamilyParameters) (n r m : ℕ) : Prop where
  independent : iIndepFun (lowerFamilyRawObservations P) (lowerFamilyArrayLaw P n r m)
  iid : ∀ i j : Fin n, IdentDistrib (lowerFamilyRawObservations P i) (lowerFamilyRawObservations P j)
    (lowerFamilyArrayLaw P n r m) (lowerFamilyArrayLaw P n r m)
  symmetric : ∀ i : Fin n, IdentDistrib (lowerFamilyRawObservations P i) (fun z => -lowerFamilyRawObservations P i z)
    (lowerFamilyArrayLaw P n r m) (lowerFamilyArrayLaw P n r m)
  centered : ∀ i : Fin n, ∀ j : Fin (r*m),
    (∫ z, lowerFamilyRawObservations P i z j ∂lowerFamilyArrayLaw P n r m) = 0
  second : ∀ i : Fin n, ∀ j k : Fin (r*m),
    (∫ z, lowerFamilyRawObservations P i z j*lowerFamilyRawObservations P i z k ∂lowerFamilyArrayLaw P n r m) =
      lowerFamilyCovariance r m P.variance j k
  unit_second : ∀ i : Fin n, ∀ j : Fin (r*m),
    (∫ z, lowerFamilyRawObservations P i z j^2 ∂lowerFamilyArrayLaw P n r m) = 1
  covariance : covariance (lowerFamilyArrayLaw P n r m) (sumVector (lowerFamilyNormalizedObservations P)) =
    lowerFamilyCovariance r m P.variance
  rank : Matrix.rank (lowerFamilyCovariance r m P.variance) = r+m-1
  gap : pairGap (lowerFamilyCovariance r m P.variance) = P.variance
  fourth : ∀ i : Fin n, ∀ j : Fin (r*m),
    (∫ z, lowerFamilyRawObservations P i z j^4 ∂lowerFamilyArrayLaw P n r m) =
      1+4*P.variance-5*P.variance^2+P.theta*P.pi*P.amplitude^4
  envelope : ∀ i : Fin n, ∀ z : Fin n → LowerFamilySeed r m,
    ‖lowerFamilyRawObservations P i z‖ ≤ P.scale+P.amplitude*familyIndicator (z i).2.2.1
  envelope_moment : ∀ q : ℝ, 1 ≤ q → ∀ i : Fin n,
    (∫ z, ‖lowerFamilyRawObservations P i z‖^q ∂lowerFamilyArrayLaw P n r m)^(1/q) ≤
      P.scale+P.amplitude*P.theta^(1/q)
  gaussian : ∃ A : Matrix (Fin (r*m)) (Fin (r*m)) ℝ,
    A*A.transpose = lowerFamilyCovariance r m P.variance ∧
    lowerGridGaussianLaw r m P.scale (Real.sqrt P.variance) = gaussianLaw A ∧
    P.scale*independentAbsGaussianMean r ≤ gaussianMaximumMean A ∧
    gaussianMaximumMean A ≤ P.scale*independentAbsGaussianMean r+
      Real.sqrt P.variance*independentAbsGaussianMean m

theorem lemma_lower_family_properties (P : SymmetricFamilyParameters) {n r m : ℕ}
    (hn : 1 ≤ n) (hr : 1 ≤ r) (hm : 2 ≤ m) : LowerRectangularFamilyProperties P n r m := by
  refine ⟨lowerFamilyRawObservations_independent P n r m,lowerFamilyRawObservations_iid P,
    lowerFamilyRawObservations_centrally_symmetric P,lowerFamilyRawObservations_centered P,
    lowerFamilyRawObservations_second P,?_,lowerFamilyNormalizedObservations_covariance P hn,
    lowerFamilyCovariance_rank hr (by omega) P.variance_pos (lt_trans P.variance_lt_half (by norm_num)),
    lowerFamilyCovariance_pairGap hr hm P.variance_pos P.variance_lt_half,
    lowerFamilyRawObservations_fourth P,?_,?_,?_⟩
  · intro i j
    simp_rw [pow_two]
    rw [lowerFamilyRawObservations_second]
    exact lowerFamilyCovariance_unit_diagonal r m P.variance j
  · intro i z
    exact lowerFamilyObservation_norm_le P (z i)
  · intro q hq i
    exact lowerFamilyRawObservations_Lq_envelope P i hq
  · let A := lowerFamilyGaussianFactor P r m
    have hA := lowerFamilyGaussianFactor_gram P r m
    have hwidth := lowerFamilyGaussian_width_bounds P hr (by omega) A hA
    exact ⟨A,hA,lowerFamilyGaussianLaw_eq P A hA,hwidth⟩

end
end RectangleCLTArxivV1
