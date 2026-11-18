import RectangleCLTArxivV1.SupplementalGTimeMeasurability
import Mathlib.LinearAlgebra.Matrix.Spectrum
import RectangleCLTCompanion.FactorExistence

/-! An actual covariance factor with exactly rankΣ columns. Zero spectral
columns are removed algebraically, without a lower eigenvalue bound. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_posSemidef_minimal_factor {p : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ) (hQ : Q.PosSemidef) :
    ∃ A : Matrix (Fin p) (Fin Q.rank) ℝ, A*A.transpose=Q := by
  classical
  let eig := hQ.1.eigenvalues
  let U : Matrix (Fin p) (Fin p) ℝ := hQ.1.eigenvectorUnitary
  let I := {j : Fin p // eig j ≠ 0}
  have hcard : Fintype.card (Fin Q.rank)=Fintype.card I := by
    simpa only [Fintype.card_fin,I,eig] using hQ.1.rank_eq_card_non_zero_eigs
  let e : Fin Q.rank ≃ I := Fintype.equivOfCardEq hcard
  let A : Matrix (Fin p) (Fin Q.rank) ℝ := fun i j => U i (e j).1*Real.sqrt (eig (e j).1)
  refine ⟨A,?_⟩
  have hspec : Q = U*Matrix.diagonal eig*U.transpose := by
    simpa only [U,eig,Matrix.star_eq_conjTranspose,Matrix.conjTranspose_eq_transpose_of_trivial,
      RCLike.ofReal_real_eq_id,Function.comp_id] using hQ.1.spectral_theorem
  ext i k
  rw [Matrix.mul_apply]
  change (∑ j, (U i (e j).1*Real.sqrt (eig (e j).1))*(U k (e j).1*Real.sqrt (eig (e j).1)))=Q i k
  rw [e.sum_comp (fun j : I => (U i j.1*Real.sqrt (eig j.1))*(U k j.1*Real.sqrt (eig j.1)))]
  have he (j : I) : (U i j.1*Real.sqrt (eig j.1))*(U k j.1*Real.sqrt (eig j.1)) = U i j.1*eig j.1*U k j.1 := by
    have hs : (Real.sqrt (eig j.1))^2=eig j.1 := Real.sq_sqrt (hQ.eigenvalues_nonneg j.1)
    nlinarith [congrArg (fun z : ℝ => U i j.1*U k j.1*z) hs]
  simp_rw [he]
  have hz : (∑ j : {j : Fin p // ¬eig j ≠ 0}, U i j.1*eig j.1*U k j.1)=0 := by
    apply Finset.sum_eq_zero
    intro j _
    have hj : eig j.1=0 := not_ne_iff.mp j.2
    simp only [hj,mul_zero,zero_mul]
  have hsum := Fintype.sum_subtype_add_sum_subtype (fun j : Fin p => eig j ≠ 0)
    (fun j => U i j*eig j*U k j)
  rw [hz,add_zero] at hsum
  rw [hsum,hspec]
  simp only [Matrix.mul_apply,Matrix.diagonal_apply,Matrix.transpose_apply]
  simp

theorem cap_covariance_minimal_factor
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) :
    ∃ A : Matrix (Fin p) (Fin (covariance μ (sumVector ξ)).rank) ℝ,
      A*A.transpose=covariance μ (sumVector ξ) :=
  cap_posSemidef_minimal_factor _ (covariance_posSemidef_of_boundedIndependent h)

theorem cap_covariance_rank_pos
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1) : 1 ≤ (covariance μ (sumVector ξ)).rank := by
  classical
  obtain ⟨A,hA⟩ := cap_covariance_minimal_factor h
  let j : Fin p := ⟨0,lt_of_lt_of_le (by decide : 0<1) hp⟩
  have hd : (A*A.transpose) j j=1 := by rw [hA]; exact hunit j
  have hn : Nonempty (Fin (covariance μ (sumVector ξ)).rank) := by
    by_contra hno
    letI : IsEmpty (Fin (covariance μ (sumVector ξ)).rank) := not_nonempty_iff.mp hno
    have hzero : (A*A.transpose) j j=0 := by simp [Matrix.mul_apply]
    rw [hzero] at hd
    norm_num at hd
  simpa only [Fintype.card_fin] using Fintype.card_pos_iff.mpr hn

theorem cap_covariance_rank_le_dimension
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) :
    (covariance μ (sumVector ξ)).rank ≤ p := by
  simpa only [Fintype.card_fin] using Matrix.rank_le_card_width (covariance μ (sumVector ξ))

/-- The literal complementary remainder bound with the intrinsic rank of
the actual covariance, and without an auxiliary factor witness. -/
theorem cap_seededFourthRemainder_rank_complementary_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ ε t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀)
    (hε : 0 ≤ ε) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |seededFourthRemainder s μ ξ C x ε t| ≤ capSeededComplementaryConstant*
      ((s.faces.card : ℝ)*((covariance μ (sumVector ξ)).rank : ℝ)*δ^2/((t+ε)*Real.sqrt (t+ε))+
        (s.faces.card : ℝ)^2*Real.sqrt ((covariance μ (sumVector ξ)).rank : ℝ)*δ^2/(h₀*Real.sqrt (t+ε))) := by
  obtain ⟨A,hA⟩ := cap_covariance_minimal_factor h
  exact cap_seededFourthRemainder_complementary_bound h A C hA hC hunit
    (cap_covariance_rank_pos h hp hunit) s x hh₀ hwidth hband hε ht

/-- Genuine time integrability with intrinsic rank instantiated internally. -/
theorem cap_seededFourthRemainder_rank_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ ε : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀) (hε : 0 < ε) :
    IntervalIntegrable (fun t => seededFourthRemainder s μ ξ C x ε t) volume 0 1 := by
  obtain ⟨A,hA⟩ := cap_covariance_minimal_factor h
  exact cap_seededFourthRemainder_intervalIntegrable h A C hA hC hunit
    (cap_covariance_rank_pos h hp hunit) s x hh₀ hwidth hband hε

theorem cap_seededFourthRemainder_rank_abs_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (C : Matrix (Fin p) (Fin p) ℝ) (hC : C*C.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) {h₀ ε : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀) (hε : 0 < ε) :
    IntervalIntegrable (fun t => |seededFourthRemainder s μ ξ C x ε t|) volume 0 1 := by
  simpa only [Real.norm_eq_abs] using
    (cap_seededFourthRemainder_rank_intervalIntegrable h hp hunit C hC s x hh₀ hwidth hband hε).norm

end
end RectangleCLTArxivV1
