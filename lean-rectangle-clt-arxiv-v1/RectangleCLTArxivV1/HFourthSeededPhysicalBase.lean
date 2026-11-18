import RectangleCLTArxivV1.HFourthSeededModel

/-! A genuine Gaussian-support base for the geometric H suppliers. The
retained sum is reconstructed from its own actual covariance factor; this
also covers the zero retained variance at t=1. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def hFourthRetainedSupportCoordinates {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (t : ℝ) (b : Fin n → Vector p) : Vector r :=
  Real.sqrt (1-t) • ∑ i, whitenedObservation (Real.sqrt (1-t)•A) (fun i b => b i) i b

def hFourthPhysicalSeededBase {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (ε t : ℝ) (z : (Fin n → Vector p) × Vector r) : Vector r :=
  hFourthRetainedSupportCoordinates A t z.1+seededSplitGaussianScale ε t • z.2

theorem hFourthRetainedSupportCoordinates_continuous {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (t : ℝ) :
    Continuous (hFourthRetainedSupportCoordinates (n := n) A t) := by
  unfold hFourthRetainedSupportCoordinates whitenedObservation
  fun_prop

theorem hFourthPhysicalSeededBase_continuous {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (ε t : ℝ) :
    Continuous (hFourthPhysicalSeededBase (n := n) A ε t) :=
  ((hFourthRetainedSupportCoordinates_continuous A t).comp continuous_fst).add
    (continuous_const.smul continuous_snd)

theorem hFourth_retained_support_reconstruct
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ))
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    (fun b => A.mulVec (hFourthRetainedSupportCoordinates A t b)) =ᵐ[bernoulliArrayLaw μ ξ t] arraySum := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let B := Real.sqrt (1-t)•A
  have hB : B*B.transpose=covariance (bernoulliArrayLaw μ ξ t)
      (sumVector (fun i (b : Fin n → Vector p) => b i)) := by
    rw [h.thinned_sum_covariance t ht.1 ht.2]
    dsimp only [B]
    rw [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,smul_smul,← pow_two,
      Real.sq_sqrt (by linarith [ht.2] : 0≤1-t),hA]
  have hre (i : Fin n) := whitenedObservation_reconstruct (h.thinned t ht.1 ht.2) B hB i
  filter_upwards [ae_all_iff.mpr hre] with b hb
  change A.mulVec (Real.sqrt (1-t) • ∑ i, whitenedObservation B (fun i b => b i) i b)=∑ i, b i
  rw [Matrix.mulVec_smul]
  have hs := map_sum A.mulVecLin (fun i : Fin n => whitenedObservation B (fun i b => b i) i b) Finset.univ
  simp only [Matrix.mulVecLin_apply] at hs
  rw [hs,Finset.smul_sum]
  exact Finset.sum_congr rfl (fun i _ => by simpa only [B,Matrix.smul_mulVec_assoc] using hb i)

/-- The exact actual half-base has a measurable physical preimage on the
Gaussian support; no face-coordinate support premise is assumed. -/
theorem hFourth_seeded_base_eq_physical
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose=covariance μ (sumVector ξ)) (x : Vector p) (ε : ℝ)
    {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    capSeededBaseValue A x ε t =ᵐ[(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)]
      (fun z => x+A.mulVec (hFourthPhysicalSeededBase A ε t z)) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae (hFourth_retained_support_reconstruct h A hA ht)] with z hz
  simp only [capSeededBaseValue,hFourthPhysicalSeededBase,Matrix.mulVec_add,Matrix.mulVec_smul,
    Matrix.smul_mulVec_assoc, hz,add_assoc]

end
end RectangleCLTArxivV1
