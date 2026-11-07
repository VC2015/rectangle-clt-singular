import RectangleCLTCompanion.SplitV4.GaussianIntrinsicConcentration
import RectangleCLTCompanion.SelectorConcentration
import RectangleCLT.EnvelopeAveraging

/-! Concentration under deletion and duplication of face constraints, and
under signed face projection. Missing constraints are removed by an actual
increasing finite cutoff; duplicate thresholds are merged by their minimum.
This is the pullback needed for the padded-normal regularization in B.4.
-/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def PolyhedralBaseConcentration {r m : ℕ} (μ : Measure (Vector r))
    (u : Fin m → Vector r) (C δ L : ℝ) : Prop :=
  ∀ a : Vector m, ∀ s : ℝ, 0 < s →
    μ.real (gaussianPolyhedronLayer u a s) ≤ C * (s + δ) * Real.sqrt L

def faceIndexFiber {ι : Type*} [Fintype ι] (κ : ι → Fin m) (j : Fin m) : Finset ι :=
  Finset.univ.filter (fun i => κ i = j)

def mergedFaceThreshold {ι : Type*} [Fintype ι] (κ : ι → Fin m)
    (a : ι → ℝ) (j : Fin m) : ℝ :=
  if h : (faceIndexFiber κ j).Nonempty then (faceIndexFiber κ j).inf' h a else 0

theorem mergedFaceThreshold_le {ι : Type*} [Fintype ι] (κ : ι → Fin m)
    (a : ι → ℝ) (i : ι) : mergedFaceThreshold κ a (κ i) ≤ a i := by
  have hi : i ∈ faceIndexFiber κ (κ i) := by simp [faceIndexFiber]
  rw [mergedFaceThreshold, dif_pos ⟨i, hi⟩]
  exact Finset.inf'_le _ hi

theorem mergedFaceThreshold_attains {ι : Type*} [Fintype ι] (κ : ι → Fin m)
    (a : ι → ℝ) (j : Fin m) (hj : (faceIndexFiber κ j).Nonempty) :
    ∃ i, κ i = j ∧ mergedFaceThreshold κ a j = a i := by
  obtain ⟨i, hi, he⟩ := Finset.exists_mem_eq_inf' (s := faceIndexFiber κ j) hj a
  refine ⟨i, (Finset.mem_filter.mp hi).2, ?_⟩
  rw [mergedFaceThreshold, dif_pos hj]
  exact he

/-- Arbitrary finite face reindexing preserves the same concentration
constant, even when the map repeats or omits normals. -/
theorem PolyhedralBaseConcentration.reindex
    {r m : ℕ} {μ : Measure (Vector r)} [IsProbabilityMeasure μ]
    {u : Fin m → Vector r} {C δ L : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    {ι : Type*} [Fintype ι] (κ : ι → Fin m) (a : ι → ℝ) {s : ℝ} (hs : 0 < s) :
    μ.real {x | (∀ i, faceDot (u (κ i)) x ≤ a i + s) ∧
      ¬ (∀ i, faceDot (u (κ i)) x ≤ a i - s)} ≤ C * (s + δ) * Real.sqrt L := by
  let E : Set (Vector r) := {x | (∀ i, faceDot (u (κ i)) x ≤ a i + s) ∧
    ¬ (∀ i, faceDot (u (κ i)) x ≤ a i - s)}
  let cutoff (n : ℕ) : Set (Vector r) := {x | ∀ j, faceDot (u j) x ≤ (n : ℝ) - s}
  let aN (n : ℕ) (j : Fin m) : ℝ :=
    if (faceIndexFiber κ j).Nonempty then mergedFaceThreshold κ a j else n
  have hsub (n : ℕ) : E ∩ cutoff n ⊆ gaussianPolyhedronLayer u (aN n) s := by
    rintro x ⟨hx, hcut⟩
    refine ⟨?_, ?_⟩
    · intro j
      by_cases hj : (faceIndexFiber κ j).Nonempty
      · obtain ⟨i, hi, he⟩ := mergedFaceThreshold_attains κ a j hj
        have hh := hx.1 i
        simpa only [hi, aN, if_pos hj, he] using hh
      · have hh := hcut j
        change faceDot (u j) x ≤ aN n j + s
        simp only [aN, if_neg hj]
        linarith
    · intro hxinner
      apply hx.2
      intro i
      have hi : (faceIndexFiber κ (κ i)).Nonempty := ⟨i, by simp [faceIndexFiber]⟩
      have hh := hxinner (κ i)
      change faceDot (u (κ i)) x ≤ aN n (κ i) - s at hh
      simp only [aN, if_pos hi] at hh
      exact hh.trans (sub_le_sub_right (mergedFaceThreshold_le κ a i) s)
  have hmono : Monotone (fun n => E ∩ cutoff n) := by
    intro n n' hnn x hx
    refine ⟨hx.1, fun j => ?_⟩
    exact (hx.2 j).trans (sub_le_sub_right (by exact_mod_cast hnn) s)
  have hUnion : (⋃ n : ℕ, E ∩ cutoff n) = E := by
    apply subset_antisymm
    · exact iUnion_subset (fun _ => inter_subset_left)
    · intro x hx
      obtain ⟨n, hn⟩ := exists_nat_ge (s + ∑ j, |faceDot (u j) x|)
      refine mem_iUnion.mpr ⟨n, hx, fun j => ?_⟩
      have hj : faceDot (u j) x ≤ ∑ l, |faceDot (u l) x| :=
        (le_abs_self _).trans (Finset.single_le_sum
          (fun l _ => abs_nonneg (faceDot (u l) x)) (Finset.mem_univ j))
      linarith
  have ht := tendsto_measure_iUnion_atTop (μ := μ) hmono
  rw [hUnion] at ht
  have htr := (ENNReal.tendsto_toReal (measure_ne_top μ E)).comp ht
  exact le_of_tendsto htr (Eventually.of_forall (fun n =>
    (measureReal_mono (hsub n)).trans (hc (aN n) s hs)))

def signedOriginalFaceIndex {m : ℕ} (opposite : Fin m → Fin m) (f : Face m) : Fin m :=
  if f.2 then f.1 else opposite f.1

theorem signed_faceProjection_eq {r m : ℕ} (u : Fin m → Vector r)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    (x : Vector r) (z : Vector m) (f : Face m) :
    FaceSmoother.normalDot f (Matrix.mulVec u x + z) =
      faceDot (u (signedOriginalFaceIndex opposite f)) x + FaceSmoother.normalDot f z := by
  cases hb : f.2
  · simp only [signedOriginalFaceIndex, hb, Bool.false_eq_true, if_false,
      FaceSmoother.normalDot, Pi.add_apply, hopp]
    simp only [faceDot, Pi.neg_apply, neg_mul, Finset.sum_neg_distrib, Matrix.mulVec, dotProduct]
    ring
  · simp only [signedOriginalFaceIndex, hb, if_true, FaceSmoother.normalDot, Pi.add_apply]
    rfl

/-- Every signed subsystem of the projected coordinates pulls back to
original normals. Duplicates are merged by the proved reindexing theorem;
the new signed system itself need not be closed under negation. -/
theorem PolyhedralBaseConcentration.signed_projection_layer
    {r m : ℕ} {μ : Measure (Vector r)} [IsProbabilityMeasure μ]
    {u : Fin m → Vector r} {C δ L : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    (t : FaceSmoother m) (z : Vector m) {s : ℝ} (hs : 0 < s) :
    μ.real {x | Matrix.mulVec u x + z ∈ t.boundaryLayer s} ≤ C * (s + δ) * Real.sqrt L := by
  let κ : t.faces → Fin m := fun f => signedOriginalFaceIndex opposite f.1
  let a : t.faces → ℝ := fun f => t.offsets f.1 - FaceSmoother.normalDot f.1 z
  have he : {x | Matrix.mulVec u x + z ∈ t.boundaryLayer s} =
      {x | (∀ f : t.faces, faceDot (u (κ f)) x ≤ a f + s) ∧
        ¬ (∀ f : t.faces, faceDot (u (κ f)) x ≤ a f - s)} := by
    ext x
    rw [mem_setOf_eq, t.mem_boundaryLayer_iff_score]
    have hf (f : Face m) : t.faceScore f (Matrix.mulVec u x + z) =
        faceDot (u (signedOriginalFaceIndex opposite f)) x -
          (t.offsets f - FaceSmoother.normalDot f z) := by
      rw [FaceSmoother.faceScore, signed_faceProjection_eq u opposite hopp]
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
  exact hc.reindex κ a hs

/-- Exact face-coordinate pullback is enough to preserve every signed
subsystem concentration bound, including the B.4 padded base. -/
theorem PolyhedralBaseConcentration.projected_law_layer
    {r m : ℕ} {μ : Measure (Vector r)} [IsProbabilityMeasure μ]
    {u : Fin m → Vector r} {C δ L : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    (Y : Vector r → Vector m) (hY : Measurable Y) (hproj : ∀ x, Y x = Matrix.mulVec u x)
    (t : FaceSmoother m) (z : Vector m) {s : ℝ} (hs : 0 < s) :
    (μ.map Y).real {y | y + z ∈ t.boundaryLayer s} ≤ C * (s + δ) * Real.sqrt L := by
  have he : (μ.map Y).real {y | y + z ∈ t.boundaryLayer s} =
      μ.real {x | Y x + z ∈ t.boundaryLayer s} :=
    map_measureReal_apply hY ((t.measurableSet_boundaryLayer s).preimage (measurable_id.add_const z))
  rw [he]
  simpa only [hproj] using hc.signed_projection_layer opposite hopp t z hs

/-- The genuine exponential-clock mixture turns the proved base layer
bound into the uniform transition cap. The base requires no moments. -/
theorem PolyhedralBaseConcentration.transitionMassBound
    {r m : ℕ} {μ : Measure (Vector r)} [IsProbabilityMeasure μ]
    {u : Fin m → Vector r} {C δ L h : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j) (hh : 0 < h) :
    TransitionMassBound (μ.map (Matrix.mulVec u)) id h
      (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
  let P := μ.map (Matrix.mulVec u)
  have hU : Measurable (Matrix.mulVec u) := (continuous_const.matrix_mulVec continuous_id).measurable
  letI : IsProbabilityMeasure P := isProbabilityMeasure_map hU.aemeasurable
  intro t ht z
  let τ := P.map (fun y => y + z)
  letI : IsProbabilityMeasure τ := isProbabilityMeasure_map (measurable_id.add_const z).aemeasurable
  have hb (q : FaceSmoother m) :
      τ.real {y | (∀ f ∈ q.faces, q.faceScore f y ≤ t.bandwidth * Real.log 2) ∧
        ¬ (∀ f ∈ q.faces, q.faceScore f y ≤ -(t.bandwidth * Real.log 2))} ≤
        C * (h * Real.log 2 + δ) * Real.sqrt L := by
    have hs : 0 < h * Real.log 2 := mul_pos hh (Real.log_pos (by norm_num))
    have he : {y | (∀ f ∈ q.faces, q.faceScore f y ≤ t.bandwidth * Real.log 2) ∧
        ¬ (∀ f ∈ q.faces, q.faceScore f y ≤ -(t.bandwidth * Real.log 2))} =
        q.boundaryLayer (h * Real.log 2) := by
      ext y
      rw [q.mem_boundaryLayer_iff_score]
      simp only [mem_setOf_eq, ht]
    rw [he]
    have hmap : τ.real (q.boundaryLayer (h * Real.log 2)) =
        P.real {y | y + z ∈ q.boundaryLayer (h * Real.log 2)} :=
      map_measureReal_apply (measurable_id.add_const z) (q.measurableSet_boundaryLayer (h * Real.log 2))
    rw [hmap]
    exact hc.projected_law_layer opposite hopp (Matrix.mulVec u) hU (fun _ => rfl) q z hs
  have hh' := t.integral_smallerEnvelope_le_of_boundary τ hb
  have hm : Measurable (fun y => t.F y * (1 - t.F y)) :=
    t.continuous_F.measurable.mul (measurable_const.sub t.continuous_F.measurable)
  have hmap : (∫ y, t.F y * (1 - t.F y) ∂τ) =
      ∫ y, t.F (y + z) * (1 - t.F (y + z)) ∂P :=
    integral_map (measurable_id.add_const z).aemeasurable hm.aestronglyMeasurable
  rw [hmap] at hh'
  exact hh'

end

end RectangleCLT.Companion.SplitV4
