import RectangleCLTCompanion.SplitV4.PolyhedralGeometry
import RectangleCLTCompanion.SplitV4.RelativeMomentTransfer
import RectangleCLTCompanion.RectangleDistance
import RectangleCLTCompanion.SubexponentialGaussian
import RectangleCLTCompanion.FactorExistence
import RectangleCLTCompanion.SharpMain

/-!
# Gaussian law and polyhedral distance under a face map

The Gaussian pushforward is identified through the proved rectangular-factor
characteristic-function theorem. Singular covariance and rectangular face
maps are retained. The bounded endpoint here is the envelope specialization
of Corollary 3; it does not assert its relative-moment or polynomial parts.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- Mapping a square-factor Gaussian by an arbitrary rectangular matrix
gives the concrete rectangular-factor Gaussian law. -/
theorem gaussianLaw_map_mulVec {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ) :
    (gaussianLaw A).map M.mulVec = rectangularGaussianLaw (M * A) := by
  unfold gaussianLaw rectangularGaussianLaw
  rw [Measure.map_map (measurable_rectangular_mulVec M) (measurable_mulVec A)]
  congr 1
  funext x
  exact Matrix.mulVec_mulVec x M A

/-- Exact square-factor identification from the transformed covariance.
No positive eigenvalue or rank assumption is imposed. -/
theorem gaussianLaw_map_mulVec_eq_of_gram {p m : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (C : Matrix (Fin m) (Fin m) ℝ)
    (hgram : C * C.transpose = M * (A * A.transpose) * M.transpose) :
    (gaussianLaw A).map M.mulVec = gaussianLaw C := by
  rw [gaussianLaw_map_mulVec]
  apply rectangularGaussianLaw_eq_gaussianLaw
  simpa only [Matrix.transpose_mul, Matrix.mul_assoc] using hgram.symm

/-- A closed polyhedron is the exact preimage of a lower orthant. -/
theorem facePolyhedron_eq_preimage_lowerOrthant {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (a : Vector m) :
    facePolyhedron ν a = ν.mulVec ⁻¹' (lowerOrthant a).carrier := by
  ext x
  change x ∈ facePolyhedron ν a ↔ ν.mulVec x ∈ (lowerOrthant a).carrier
  rw [mem_lowerOrthant]
  rfl

theorem measurableSet_facePolyhedron {p m : ℕ}
    (ν : Matrix (Fin m) (Fin p) ℝ) (a : Vector m) :
    MeasurableSet (facePolyhedron ν a) := by
  rw [facePolyhedron_eq_preimage_lowerOrthant]
  exact (lowerOrthant a).measurableSet_carrier.preimage (measurable_rectangular_mulVec ν)

/-- Probability discrepancy for one polyhedron against the original
Gaussian law, before applying the standardized face map. -/
def polyhedronError {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (a : Vector m) : ℝ :=
  |μ.real (W ⁻¹' facePolyhedron ν a) - (gaussianLaw A).real (facePolyhedron ν a)|

/-- The manuscript's supremum over thresholds for fixed face normals. -/
def polyhedralDistance {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) : ℝ :=
  sSup (Set.range (polyhedronError μ W A ν))

theorem polyhedronError_le_one {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : Matrix (Fin m) (Fin p) ℝ) (a : Vector m) :
    polyhedronError μ W A ν a ≤ 1 := by
  unfold polyhedronError
  have hw0 : 0 ≤ μ.real (W ⁻¹' facePolyhedron ν a) := measureReal_nonneg
  have hw1 : μ.real (W ⁻¹' facePolyhedron ν a) ≤ 1 := measureReal_le_one
  have hz0 : 0 ≤ (gaussianLaw A).real (facePolyhedron ν a) := measureReal_nonneg
  have hz1 : (gaussianLaw A).real (facePolyhedron ν a) ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem polyhedralErrors_bddAbove {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : Matrix (Fin m) (Fin p) ℝ) :
    BddAbove (Set.range (polyhedronError μ W A ν)) := by
  refine ⟨1, ?_⟩
  rintro x ⟨a, rfl⟩
  exact polyhedronError_le_one μ W A ν a

theorem polyhedronError_eq_projected_rectangleError
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ a : Vector m) (hσ : ∀ α, 0 < σ α)
    (hgram : C * C.transpose =
      standardizedFaceMap ν σ * (A * A.transpose) * (standardizedFaceMap ν σ).transpose) :
    polyhedronError μ W A ν a =
      rectangleError μ (fun ω => (standardizedFaceMap ν σ).mulVec (W ω)) C
        (lowerOrthant (fun α => a α / σ α)) := by
  unfold polyhedronError
  rw [facePolyhedron_eq_preimage_standardized ν σ a hσ]
  rw [← map_measureReal_apply (μ := gaussianLaw A)
    (measurable_rectangular_mulVec (standardizedFaceMap ν σ))
    (lowerOrthant (fun α => a α / σ α)).measurableSet_carrier]
  rw [gaussianLaw_map_mulVec_eq_of_gram _ A C hgram]
  rfl

/-- The actual supremum over polyhedra is bounded by the full measurable
rectangle distance after standardizing the faces. -/
theorem polyhedralDistance_le_projected_rectangleDistance
    {Ω : Type*} [MeasurableSpace Ω] {p m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (C : Matrix (Fin m) (Fin m) ℝ)
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (hσ : ∀ α, 0 < σ α)
    (hgram : C * C.transpose =
      standardizedFaceMap ν σ * (A * A.transpose) * (standardizedFaceMap ν σ).transpose) :
    polyhedralDistance μ W A ν ≤
      rectangleDistance μ (fun ω => (standardizedFaceMap ν σ).mulVec (W ω)) C := by
  apply csSup_le (show (Set.range (polyhedronError μ W A ν)).Nonempty from ⟨_, ⟨0, rfl⟩⟩)
  rintro x ⟨a, rfl⟩
  rw [polyhedronError_eq_projected_rectangleError μ W A C ν σ a hσ hgram]
  exact rectangleError_le_rectangleDistance _ _ _ _

theorem sumVector_mulVec {Ω : Type*} {p m n : ℕ}
    (M : Matrix (Fin m) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) (ω : Ω) :
    sumVector (fun i ω => M.mulVec (ξ i ω)) ω = M.mulVec (sumVector ξ ω) := by
  ext α
  simp only [sumVector, Finset.sum_apply, Matrix.mulVec, dotProduct, Finset.mul_sum]
  exact Finset.sum_comm

/-- The bounded-envelope part of the polyhedral transfer, with its actual
supremum over all thresholds. The Gaussian factor is chosen inside the
proof from the actual projected covariance. The constant is fixed before
the dimensions, array, face normals, and probability model. -/
theorem boundedPolyhedralEnvelopeCLT
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hm : 1 ≤ m) (hn : 1 ≤ n)
    (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (h : BoundedIndependentHypotheses μ ξ δ)
    (hA : A * A.transpose = covariance μ (sumVector ξ))
    (ν : Matrix (Fin m) (Fin p) ℝ) (σ : Vector m) (J : ℝ)
    (hσ : ∀ α, 0 < σ α) (hJ : 0 ≤ J)
    (hν : ∀ α, (∑ j, |ν α j|) ≤ J * σ α)
    (hvariance : ∀ α,
      dotProduct (ν α) ((covariance μ (sumVector ξ)).mulVec (ν α)) = (σ α) ^ 2) :
    polyhedralDistance μ (sumVector ξ) A ν ≤
      (2 * companionUniversalConstant) *
        min 1 (unrestrictedRate (J * δ) (dimensionLog m)) := by
  let M := standardizedFaceMap ν σ
  have hM : ∀ α, (∑ j, |M α j|) ≤ J := standardizedFaceMap_row_l1_le ν σ J hσ hν
  let η : Fin n → Ω → Vector m := fun i ω => M.mulVec (ξ i ω)
  have hη : BoundedIndependentHypotheses μ η (J * δ) :=
    boundedIndependent_projected h M J hJ hM
  have hcov : covariance μ (sumVector η) = M * covariance μ (sumVector ξ) * M.transpose :=
    covariance_projected_sum h M J hJ hM
  have hunit : ∀ α, covariance μ (sumVector η) α α = 1 := by
    intro α
    rw [hcov]
    exact standardizedFaceMap_covariance_unit_diagonal ν σ _ hσ hvariance α
  obtain ⟨C, hC⟩ := gaussian_factor_exists_of_boundedIndependent hη
  have hgram : C * C.transpose = M * (A * A.transpose) * M.transpose := by
    simpa only [hA] using hC.trans hcov
  have hd := polyhedralDistance_le_projected_rectangleDistance
    μ (sumVector ξ) A C ν σ hσ hgram
  have hsum : sumVector η = fun ω => M.mulVec (sumVector ξ ω) :=
    funext (sumVector_mulVec M ξ)
  change polyhedralDistance μ (sumVector ξ) A ν ≤
    rectangleDistance μ (fun ω => M.mulVec (sumVector ξ ω)) C at hd
  rw [← hsum] at hd
  apply hd.trans
  apply rectangleDistance_le
  intro R
  exact unrestrictedCLT μ m n hm hn η (J * δ) C hη hunit hC R

end

end RectangleCLT.Companion.SplitV4
