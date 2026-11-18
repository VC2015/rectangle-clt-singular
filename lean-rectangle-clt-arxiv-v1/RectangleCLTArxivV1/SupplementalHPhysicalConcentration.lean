import RectangleCLTArxivV1.SmoothingMatrixIntrinsic
import RectangleCLTArxivV1.SupplementalHLocalizedTube
import RectangleCLTArxivV1.SupplementalGRectangularHessian

/-! Actual physical-base concentration under a rectangular factor. An
almost-sure whitening reconstruction and a deterministic threshold shift
suffice; no covariance inverse or rank hypothesis is introduced. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

/-- Uniform rectangle layers also control every reindexed physical face
system, including repeated and dependent normals. -/
theorem intrinsicRectangleConcentration_physical_layer {p r m : ℕ}
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (A : Matrix (Fin p) (Fin r) ℝ) {C₀ δ κ : ℝ}
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (f : Fin m → Face p) (b : Vector m) {s : ℝ} (hs : 0 < s) :
    ν.real (faceLayer (fun j => capRectangularFactorNormal A (f j)) b s) ≤ C₀*κ*(s+δ) := by
  let t := reindexedRectangle f b
  have hA : Measurable (fun x : Vector r => A.mulVec x) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  have hset : {x : Vector r | A.mulVec x+0 ∈ t.boundaryLayer s} =
      faceLayer (fun j => capRectangularFactorNormal A (f j)) b s := by
    ext x
    simp only [add_zero,Set.mem_setOf_eq]
    rw [FaceSmoother.mem_boundaryLayer_iff_score]
    change ((∀ g∈(reindexedRectangle f b).faces,
      (reindexedRectangle f b).faceScore g (A.mulVec x)≤s) ∧
      ¬∀ g∈(reindexedRectangle f b).faces,
        (reindexedRectangle f b).faceScore g (A.mulVec x)≤-s) ↔ _
    rw [←reindexedRectangle_scores f b (A.mulVec x) s,
      ←reindexedRectangle_scores f b (A.mulVec x) (-s)]
    simp_rw [cap_rectangular_normalDot_factor]
    rfl
  have hm : MeasurableSet {y : Vector p | y+0 ∈ t.boundaryLayer s} :=
    (t.measurableSet_boundaryLayer s).preimage (measurable_id.add_const 0)
  have hmap : (ν.map (fun x => A.mulVec x)).real {y | y+0 ∈ t.boundaryLayer s} =
      ν.real {x | A.mulVec x+0 ∈ t.boundaryLayer s} := map_measureReal_apply hA hm
  have hh := hc t 0 s hs
  rw [hmap,hset] at hh
  exact hh

/-- Remove a deterministic face-coordinate translation using the actual
a.e. reconstruction, before applying the physical surface theorem. -/
theorem intrinsicRectangleConcentration_remove_ae_shift
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → Vector r) (hB : Measurable B)
    (R : Ω → Vector p) (hR : Measurable R)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (hrec : ∀ᵐ ω ∂μ, R ω=x+A.mulVec (B ω)) {C₀ δ κ : ℝ}
    (hc : IntrinsicRectangleConcentration (μ.map R) C₀ δ κ) :
    IntrinsicRectangleConcentration ((μ.map B).map (fun z => A.mulVec z)) C₀ δ κ := by
  have hA : Measurable (fun z : Vector r => A.mulVec z) := by
    unfold Matrix.mulVec dotProduct
    fun_prop
  rw [Measure.map_map hA hB]
  change IntrinsicRectangleConcentration (μ.map (fun ω => A.mulVec (B ω))) C₀ δ κ
  intro t z s hs
  have hmAB : MeasurableSet {y : Vector p | y+z ∈ t.boundaryLayer s} :=
    (t.measurableSet_boundaryLayer s).preimage (measurable_id.add_const z)
  have hmR : MeasurableSet {y : Vector p | y+(z-x) ∈ t.boundaryLayer s} :=
    (t.measurableSet_boundaryLayer s).preimage (measurable_id.add_const (z-x))
  have he : {ω | A.mulVec (B ω)+z ∈ t.boundaryLayer s} =ᵐ[μ]
      {ω | R ω+(z-x) ∈ t.boundaryLayer s} := by
    filter_upwards [hrec] with ω hω
    change (A.mulVec (B ω)+z ∈ t.boundaryLayer s) = (R ω+(z-x) ∈ t.boundaryLayer s)
    rw [hω]
    have harg : x+A.mulVec (B ω)+(z-x)=A.mulVec (B ω)+z := by abel
    rw [harg]
  calc
    _ = μ.real {ω | A.mulVec (B ω)+z ∈ t.boundaryLayer s} :=
      map_measureReal_apply (hA.comp hB) hmAB
    _ = μ.real {ω | R ω+(z-x) ∈ t.boundaryLayer s} :=
      congrArg ENNReal.toReal (measure_congr he)
    _ = (μ.map R).real {y | y+(z-x) ∈ t.boundaryLayer s} :=
      (map_measureReal_apply hR hmR).symm
    _ ≤ _ := hc t (z-x) s hs

/-- Direct interface for an actual physical reconstruction of the
seeded base. The unconditional physical layer budget is the conclusion. -/
theorem intrinsicRectangleConcentration_physical_layer_of_ae_shift
    {Ω : Type*} [MeasurableSpace Ω] {p r m : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Ω → Vector r) (hB : Measurable B)
    (R : Ω → Vector p) (hR : Measurable R)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (hrec : ∀ᵐ ω ∂μ, R ω=x+A.mulVec (B ω)) {C₀ δ κ : ℝ}
    (hc : IntrinsicRectangleConcentration (μ.map R) C₀ δ κ)
    (f : Fin m → Face p) (b : Vector m) {s : ℝ} (hs : 0 < s) :
    (μ.map B).real (faceLayer (fun j => capRectangularFactorNormal A (f j)) b s) ≤
      C₀*κ*(s+δ) := by
  letI : IsProbabilityMeasure (μ.map B) := isProbabilityMeasure_map hB.aemeasurable
  exact intrinsicRectangleConcentration_physical_layer (μ.map B) A
    (intrinsicRectangleConcentration_remove_ae_shift μ B hB R hR A x hrec hc) f b hs

end
end RectangleCLTArxivV1
