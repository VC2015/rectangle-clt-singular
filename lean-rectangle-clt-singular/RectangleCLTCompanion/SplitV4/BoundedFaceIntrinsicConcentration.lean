import RectangleCLTCompanion.SplitV4.BoundedIntrinsicConcentration
import RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The bounded half of Lemma 1 for arbitrary fixed face normals, in the
same actual polyhedral event and projection seminorm as the Gaussian half.
Only the projected observations are bounded. Raw vectors have genuine
first moments and are centered; their coordinates need not be independent.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def faceProjectedArray {Ω : Type*} {p m n : ℕ}
    (U : Matrix (Fin m) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) : Fin n → Ω → Vector m :=
  fun i ω => U.mulVec (ξ i ω)

theorem sum_faceProjectedArray {Ω : Type*} {p m n : ℕ}
    (U : Matrix (Fin m) (Fin p) ℝ) (ξ : Fin n → Ω → Vector p) (ω : Ω) :
    (∑ i, faceProjectedArray U ξ i ω) = U.mulVec (∑ i, ξ i ω) := by
  simpa only [Matrix.toLin'_apply] using
    (map_sum (Matrix.toLin' U) (fun i => ξ i ω) Finset.univ).symm

theorem boundedIndependent_faceProjectedArray {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin p) ℝ)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hcenter : ∀ i, (∫ ω, ξ i ω ∂μ) = 0) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ η) :
    BoundedIndependentHypotheses μ (faceProjectedArray U ξ) η := by
  refine ⟨fun i => (measurable_rectangular_mulVec U).comp (hξ i),
    hind.comp (fun _ => U.mulVec) (fun _ => measurable_rectangular_mulVec U), ?_, hbound, hη⟩
  intro i j
  let L : Vector p →L[ℝ] Vector m := (Matrix.toLin' U).toContinuousLinearMap
  have he := ((ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ).comp L).integral_comp_comm (hξi i)
  change (∫ ω, U.mulVec (ξ i ω) j ∂μ) = U.mulVec (∫ ω, ξ i ω ∂μ) j at he
  change (∫ ω, U.mulVec (ξ i ω) j ∂μ) = 0
  rw [he, hcenter i, Matrix.mulVec_zero]
  rfl

theorem projected_covariance_diagonal_eq_variance {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (j : Fin p) : covariance μ (sumVector ξ) j j = variance (fun ω => sumVector ξ ω j) μ := by
  have hm : Measurable (fun ω => sumVector ξ ω j) := (measurable_pi_apply j).comp h.measurable_sum
  have hb : ∀ᵐ ω ∂μ, ‖sumVector ξ ω j‖ ≤ (n : ℝ) * η := by
    filter_upwards [h.sum_norm_bound] with ω hω
    exact (norm_le_pi_norm _ j).trans hω
  have hLp : MemLp (fun ω => sumVector ξ ω j) 2 μ := MemLp.of_bound hm.aestronglyMeasurable _ hb
  rw [variance_def' hLp]
  simp only [covariance, Pi.pow_apply, pow_two]

theorem face_layer_eq_projected {p m : ℕ} (U : Matrix (Fin m) (Fin p) ℝ)
    (a : Vector m) (s : ℝ) (x : Vector p) :
    x ∈ gaussianPolyhedronLayer U a s ↔ U.mulVec x ∈ projectedFaceLayer a s := by
  simp only [gaussianPolyhedronLayer, projectedFaceLayer, projectedFacePolyhedron,
    facePolyhedron, Set.mem_diff, Set.mem_setOf_eq, Matrix.mulVec, sub_eq_add_neg]

/-- **Lemma 1, bounded intrinsic assertion for arbitrary face normals.**
The face variances are the actual variances of the original projected
sum, and the expectation is the actual projection seminorm of that sum.
The measurable shift is independent of the original sum. -/
theorem bounded_face_intrinsic_concentration
    {Ω : Type*} [MeasurableSpace Ω] {p m n : ℕ} [NeZero m]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (U : Matrix (Fin m) (Fin p) ℝ)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hξi : ∀ i, Integrable (ξ i) μ)
    (hcenter : ∀ i, (∫ ω, ξ i ω ∂μ) = 0) {η v : ℝ} (hη : 0 ≤ η) (hv : 0 < v)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, faceProjectionNorm U (ξ i ω) ≤ η)
    (hvariance : ∀ α, variance (fun ω => dotProduct (U α) (sumVector ξ ω)) μ = v)
    (R : Ω → Vector p) (hR : Measurable R) (hRind : IndepFun (sumVector ξ) R μ)
    (a : Vector m) {s : ℝ} (hs : 0 ≤ s) :
    μ.real {ω | (sumVector ξ ω + R ω) ∈ gaussianPolyhedronLayer U a s} ≤
      256 * min 1 (min (((s + η) / v) * ∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ)
        ((s + η) * Real.sqrt (dimensionLog m / v))) := by
  let ζ := faceProjectedArray U ξ
  have hζ := boundedIndependent_faceProjectedArray μ U ξ hξ hind hξi hcenter hη hbound
  have hsum (ω : Ω) : sumVector ζ ω = U.mulVec (sumVector ξ ω) := sum_faceProjectedArray U ξ ω
  have hdiag (α : Fin m) : covariance μ (sumVector ζ) α α = v := by
    rw [projected_covariance_diagonal_eq_variance μ ζ hζ α]
    simpa only [hsum, Matrix.mulVec] using hvariance α
  have hRI : IndepFun (sumVector ζ) (fun ω => U.mulVec (R ω)) μ := by
    rw [show sumVector ζ = (fun ω => U.mulVec (sumVector ξ ω)) from funext hsum]
    simpa only [Function.comp_def] using
      hRind.comp (measurable_rectangular_mulVec U) (measurable_rectangular_mulVec U)
  have hb := bounded_intrinsic_layer_independent_shift_min μ ζ hζ hv hdiag
    (fun ω => U.mulVec (R ω)) ((measurable_rectangular_mulVec U).comp hR) hRI a hs
  have hevent : {ω | ((∑ i, ζ i ω) + U.mulVec (R ω)) ∈ projectedFaceLayer a s} =
      {ω | (sumVector ξ ω + R ω) ∈ gaussianPolyhedronLayer U a s} := by
    ext ω
    change ((∑ i, ζ i ω) + U.mulVec (R ω) ∈ projectedFaceLayer a s) ↔
      (sumVector ξ ω + R ω ∈ gaussianPolyhedronLayer U a s)
    rw [face_layer_eq_projected]
    change (sumVector ζ ω + U.mulVec (R ω) ∈ projectedFaceLayer a s) ↔ _
    rw [hsum, Matrix.mulVec_add]
  rw [hevent] at hb
  have hmean : (∫ ω, ‖∑ i, ζ i ω‖ ∂μ) =
      ∫ ω, faceProjectionNorm U (sumVector ξ ω) ∂μ := by
    apply integral_congr_ae
    filter_upwards [] with ω
    change ‖sumVector ζ ω‖ = _
    rw [hsum]
    rfl
  rw [hmean] at hb
  exact hb

end

end RectangleCLT.Companion.SplitV4
