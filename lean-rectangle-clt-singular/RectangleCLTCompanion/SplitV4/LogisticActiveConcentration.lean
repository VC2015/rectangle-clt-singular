import RectangleCLTCompanion.SplitV4.LogisticActiveFaces
import RectangleCLTCompanion.SignedSurfaceConcentration

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def RectangleBaseConcentration {p : ℕ} (μ : Measure (Vector p)) (C δ L : ℝ) : Prop :=
  ∀ t : FaceSmoother p, ∀ z : Vector p, ∀ s : ℝ, 0 < s →
    μ.real {x | x + z ∈ t.boundaryLayer s} ≤ C * (s + δ) * Real.sqrt L

theorem uniformBoundaryConcentration_rectangleBase {p : ℕ}
    {μ : Measure (Vector p)} {C δ : ℝ}
    (hc : SignedSurface.UniformBoundaryConcentration μ C δ 1) :
    RectangleBaseConcentration μ C δ (dimensionLog p) := by
  simpa only [RectangleBaseConcentration, SignedSurface.UniformBoundaryConcentration, div_one] using hc

def originalFaceFiber {ι : Type*} [Fintype ι] {p : ℕ} (κ : ι → Face p) (f : Face p) : Finset ι :=
  Finset.univ.filter (fun i => κ i = f)

def originalFaceThreshold {ι : Type*} [Fintype ι] {p : ℕ}
    (κ : ι → Face p) (a : ι → ℝ) (f : Face p) : ℝ :=
  if h : (originalFaceFiber κ f).Nonempty then (originalFaceFiber κ f).inf' h a else 0

theorem originalFaceThreshold_le {ι : Type*} [Fintype ι] {p : ℕ}
    (κ : ι → Face p) (a : ι → ℝ) (i : ι) : originalFaceThreshold κ a (κ i) ≤ a i := by
  have hi : i ∈ originalFaceFiber κ (κ i) := by simp [originalFaceFiber]
  rw [originalFaceThreshold, dif_pos ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

theorem originalFaceThreshold_attains {ι : Type*} [Fintype ι] {p : ℕ}
    (κ : ι → Face p) (a : ι → ℝ) (f : Face p) (hf : f ∈ Finset.univ.image κ) :
    ∃ i, κ i = f ∧ originalFaceThreshold κ a f = a i := by
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hf
  have hn : (originalFaceFiber κ f).Nonempty := ⟨i, by simp [originalFaceFiber, hi]⟩
  obtain ⟨j, hj, he⟩ := Finset.exists_mem_eq_inf' (s := originalFaceFiber κ f) hn a
  refine ⟨j, (Finset.mem_filter.mp hj).2, ?_⟩
  rw [originalFaceThreshold, dif_pos hn]
  exact he

def reindexedRectangle {ι : Type*} [Fintype ι] {p : ℕ}
    (κ : ι → Face p) (a : ι → ℝ) : FaceSmoother p where
  faces := Finset.univ.image κ
  offsets := originalFaceThreshold κ a
  bandwidth := 1
  bandwidth_pos := by norm_num

theorem reindexedRectangle_scores {ι : Type*} [Fintype ι] {p : ℕ}
    (κ : ι → Face p) (a : ι → ℝ) (x : Vector p) (q : ℝ) :
    (∀ i, FaceSmoother.normalDot (κ i) x ≤ a i + q) ↔
      ∀ f ∈ (reindexedRectangle κ a).faces, (reindexedRectangle κ a).faceScore f x ≤ q := by
  constructor
  · intro hx f hf
    obtain ⟨i, hi, he⟩ := originalFaceThreshold_attains κ a f hf
    have hh := hx i
    simp only [reindexedRectangle, FaceSmoother.faceScore, he]
    rw [hi] at hh
    linarith
  · intro hx i
    have hh := hx (κ i) (by simp [reindexedRectangle])
    change FaceSmoother.normalDot (κ i) x - originalFaceThreshold κ a (κ i) ≤ q at hh
    have ht := originalFaceThreshold_le κ a i
    linarith

theorem RectangleBaseConcentration.reindexed_layer
    {p : ℕ} {μ : Measure (Vector p)} {C δ L : ℝ}
    (hc : RectangleBaseConcentration μ C δ L)
    {ι : Type*} [Fintype ι] (κ : ι → Face p) (a : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    μ.real {x | (∀ i, FaceSmoother.normalDot (κ i) x ≤ a i + s) ∧
      ¬ (∀ i, FaceSmoother.normalDot (κ i) x ≤ a i - s)} ≤ C * (s + δ) * Real.sqrt L := by
  have he : {x | (∀ i, FaceSmoother.normalDot (κ i) x ≤ a i + s) ∧
      ¬ (∀ i, FaceSmoother.normalDot (κ i) x ≤ a i - s)} =
      {x | x + 0 ∈ (reindexedRectangle κ a).boundaryLayer s} := by
    ext x
    simp only [add_zero, Set.mem_setOf_eq, FaceSmoother.mem_boundaryLayer_iff_score]
    rw [← reindexedRectangle_scores κ a x s, ← reindexedRectangle_scores κ a x (-s)]
    simp only [sub_eq_add_neg]
  rw [he]
  exact hc (reindexedRectangle κ a) 0 s hs

def oppositeCoordinateFace {p : ℕ} (f : Face p) : Face p := (f.1, !f.2)

def signedActiveOriginalFace {p : ℕ} (s : FaceSmoother p) (f : Face s.faces.card) : Face p :=
  if f.2 then (activeFaceEquiv s f.1).1 else oppositeCoordinateFace (activeFaceEquiv s f.1).1

theorem activeFaceProjection_signed_dot {p : ℕ} (s : FaceSmoother p)
    (x : Vector p) (z : Vector s.faces.card) (f : Face s.faces.card) :
    FaceSmoother.normalDot f (activeFaceProjection s x + z) =
      FaceSmoother.normalDot (signedActiveOriginalFace s f) x + FaceSmoother.normalDot f z := by
  rcases f with ⟨j, b⟩
  cases b <;>
    simp only [signedActiveOriginalFace, Bool.false_eq_true, if_false, if_true,
      Bool.true_eq, FaceSmoother.normalDot, activeFaceProjection, oppositeCoordinateFace,
      Pi.add_apply, Bool.not_eq_true'] <;>
    split_ifs <;> simp_all <;> ring

theorem RectangleBaseConcentration.active_projection_layer
    {p : ℕ} {μ : Measure (Vector p)} {C δ L : ℝ}
    (hc : RectangleBaseConcentration μ C δ L) (s : FaceSmoother p)
    (t : FaceSmoother s.faces.card) (z : Vector s.faces.card) {d : ℝ} (hd : 0 < d) :
    μ.real {x | activeFaceProjection s x + z ∈ t.boundaryLayer d} ≤
      C * (d + δ) * Real.sqrt L := by
  let κ : t.faces → Face p := fun f => signedActiveOriginalFace s f.1
  let a : t.faces → ℝ := fun f => t.offsets f.1 - FaceSmoother.normalDot f.1 z
  have he : {x | activeFaceProjection s x + z ∈ t.boundaryLayer d} =
      {x | (∀ f : t.faces, FaceSmoother.normalDot (κ f) x ≤ a f + d) ∧
        ¬ (∀ f : t.faces, FaceSmoother.normalDot (κ f) x ≤ a f - d)} := by
    ext x
    rw [mem_setOf_eq, t.mem_boundaryLayer_iff_score]
    have hf (f : Face s.faces.card) : t.faceScore f (activeFaceProjection s x + z) =
        FaceSmoother.normalDot (signedActiveOriginalFace s f) x -
          (t.offsets f - FaceSmoother.normalDot f z) := by
      rw [FaceSmoother.faceScore, activeFaceProjection_signed_dot]
      ring
    simp only [hf, κ, a, mem_setOf_eq, sub_le_iff_le_add]
    constructor
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun f => ?_, fun h => h₂ (fun f hf => ?_)⟩
      · have hh := h₁ f.1 f.2
        linarith
      · have hh := h ⟨f, hf⟩
        linarith
    · rintro ⟨h₁, h₂⟩
      refine ⟨fun f hf => ?_, fun h => h₂ (fun f => ?_)⟩
      · have hh := h₁ ⟨f, hf⟩
        linarith
      · have hh := h f.1 f.2
        linarith
  rw [he]
  exact hc.reindexed_layer κ a hd

theorem RectangleBaseConcentration.active_coordinate_concentration
    {p : ℕ} {μ : Measure (Vector p)} [IsProbabilityMeasure μ] {C δ L : ℝ}
    (hc : RectangleBaseConcentration μ C δ L) (s : FaceSmoother p) :
    PolyhedralBaseConcentration (μ.map (activeFaceProjection s))
      (1 : Matrix (Fin s.faces.card) (Fin s.faces.card) ℝ) C δ L := by
  intro a d hd
  have hS : MeasurableSet (gaussianPolyhedronLayer
      (1 : Matrix (Fin s.faces.card) (Fin s.faces.card) ℝ) a d) := by
    apply MeasurableSet.diff
    all_goals
      unfold facePolyhedron
      simp only [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_le (by unfold dotProduct; fun_prop) measurable_const
  rw [map_measureReal_apply (measurable_activeFaceProjection s) hS]
  have he : activeFaceProjection s ⁻¹' gaussianPolyhedronLayer
      (1 : Matrix (Fin s.faces.card) (Fin s.faces.card) ℝ) a d =
      {x | (∀ j, FaceSmoother.normalDot (activeFaceEquiv s j).1 x ≤ a j + d) ∧
        ¬ (∀ j, FaceSmoother.normalDot (activeFaceEquiv s j).1 x ≤ a j - d)} := by
    ext x
    simp [gaussianPolyhedronLayer, facePolyhedron, dotProduct, Matrix.one_apply,
      activeFaceProjection, Finset.sum_ite_eq, Finset.sum_ite_eq']
  rw [he]
  exact hc.reindexed_layer (fun j => (activeFaceEquiv s j).1) a hd

theorem RectangleBaseConcentration.active_transitionMassBound
    {p : ℕ} {μ : Measure (Vector p)} [IsProbabilityMeasure μ] {C δ L h : ℝ}
    (hc : RectangleBaseConcentration μ C δ L) (s : FaceSmoother p) (hh : 0 < h) :
    TransitionMassBound (μ.map (activeFaceProjection s)) id h
      (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
  let P := μ.map (activeFaceProjection s)
  letI : IsProbabilityMeasure P := isProbabilityMeasure_map (measurable_activeFaceProjection s).aemeasurable
  intro t ht z
  let τ := P.map (fun y => y + z)
  letI : IsProbabilityMeasure τ := isProbabilityMeasure_map (measurable_id.add_const z).aemeasurable
  have hb (q : FaceSmoother s.faces.card) :
      τ.real {y | (∀ f ∈ q.faces, q.faceScore f y ≤ t.bandwidth * Real.log 2) ∧
        ¬ (∀ f ∈ q.faces, q.faceScore f y ≤ -(t.bandwidth * Real.log 2))} ≤
        C * (h * Real.log 2 + δ) * Real.sqrt L := by
    have hd : 0 < h * Real.log 2 := mul_pos hh (Real.log_pos (by norm_num))
    have he : {y | (∀ f ∈ q.faces, q.faceScore f y ≤ t.bandwidth * Real.log 2) ∧
        ¬ (∀ f ∈ q.faces, q.faceScore f y ≤ -(t.bandwidth * Real.log 2))} =
        q.boundaryLayer (h * Real.log 2) := by
      ext y
      rw [q.mem_boundaryLayer_iff_score]
      simp only [mem_setOf_eq, ht]
    rw [he]
    have hmap : τ.real (q.boundaryLayer (h * Real.log 2)) =
        P.real {y | y + z ∈ q.boundaryLayer (h * Real.log 2)} :=
      map_measureReal_apply (measurable_id.add_const z) (q.measurableSet_boundaryLayer _)
    rw [hmap]
    have hm : MeasurableSet {y | y + z ∈ q.boundaryLayer (h * Real.log 2)} :=
      (q.measurableSet_boundaryLayer _).preimage (measurable_id.add_const z)
    have hmap' : P.real {y | y + z ∈ q.boundaryLayer (h * Real.log 2)} =
        μ.real {x | activeFaceProjection s x + z ∈ q.boundaryLayer (h * Real.log 2)} :=
      map_measureReal_apply (measurable_activeFaceProjection s) hm
    rw [hmap']
    exact hc.active_projection_layer s q z hd
  have hb' := t.integral_smallerEnvelope_le_of_boundary τ hb
  have hm : Measurable (fun y => t.F y * (1 - t.F y)) :=
    t.continuous_F.measurable.mul (measurable_const.sub t.continuous_F.measurable)
  have hmap : (∫ y, t.F y * (1 - t.F y) ∂τ) =
      ∫ y, t.F (y + z) * (1 - t.F (y + z)) ∂P :=
    integral_map (measurable_id.add_const z).aemeasurable hm.aestronglyMeasurable
  rw [hmap] at hb'
  exact hb'

end

end RectangleCLT.Companion.SplitV4
