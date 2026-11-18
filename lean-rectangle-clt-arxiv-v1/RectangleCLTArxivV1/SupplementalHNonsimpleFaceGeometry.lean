import RectangleCLTArxivV1.SupplementalHActualFacetSelection
import RectangleCLTCompanion.SignedSurfacePolyhedron
import Mathlib.LinearAlgebra.Dimension.Constructions

/-! Actual faces are indexed by their complete active set, not by a
chosen triple of constraints.  In particular a codimension-three face
may carry more than three active original facets. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {m : ℕ}

def nonsimpleActiveSet (u : Fin m → E) (b : Fin m → ℝ) (x : E) : Finset (Fin m) :=
  Finset.univ.filter (fun j => ⟪u j,x⟫_ℝ=b j)

@[simp] theorem mem_nonsimpleActiveSet (u : Fin m → E) (b : Fin m → ℝ) (x : E) (j : Fin m) :
    j∈nonsimpleActiveSet u b x ↔ ⟪u j,x⟫_ℝ=b j := by
  classical
  simp [nonsimpleActiveSet]

theorem mem_exactStratum_iff_activeSet (u : Fin m → E) (b : Fin m → ℝ)
    (S : Finset (Fin m)) (x : E) :
    x∈exactStratum u b S ↔ x∈polyhedron u b ∧ nonsimpleActiveSet u b x=S := by
  classical
  constructor
  · rintro ⟨hx,he⟩
    exact ⟨hx,Finset.ext (fun j => (mem_nonsimpleActiveSet u b x j).trans (he j))⟩
  · rintro ⟨hx,rfl⟩
    exact ⟨hx,fun j => (mem_nonsimpleActiveSet u b x j).symm⟩

theorem nonsimpleActiveSet_exactStratum (u : Fin m → E) (b : Fin m → ℝ)
    {x : E} (hx : x∈polyhedron u b) : x∈exactStratum u b (nonsimpleActiveSet u b x) :=
  (mem_exactStratum_iff_activeSet u b _ x).mpr ⟨hx,rfl⟩

def nonsimpleClosedFace (u : Fin m → E) (b : Fin m → ℝ) (S : Finset (Fin m)) : Set E :=
  {x | x∈polyhedron u b ∧ ∀ j∈S,⟪u j,x⟫_ℝ=b j}

theorem exactStratum_subset_nonsimpleClosedFace (u : Fin m → E) (b : Fin m → ℝ)
    (S : Finset (Fin m)) : exactStratum u b S⊆nonsimpleClosedFace u b S := by
  intro x hx
  exact ⟨hx.1,fun j hj => (hx.2 j).mpr hj⟩

theorem nonsimpleClosedFace_antitone (u : Fin m → E) (b : Fin m → ℝ)
    {S T : Finset (Fin m)} (hST : S⊆T) : nonsimpleClosedFace u b T⊆nonsimpleClosedFace u b S := by
  intro x hx
  exact ⟨hx.1,fun j hj => hx.2 j (hST hj)⟩

theorem nonsimpleClosedFace_subset_iff (u : Fin m → E) (b : Fin m → ℝ)
    (S T : Finset (Fin m)) (hT : (exactStratum u b T).Nonempty) :
    nonsimpleClosedFace u b T⊆nonsimpleClosedFace u b S ↔ S⊆T := by
  constructor
  · intro h j hj
    obtain ⟨x,hx⟩ := hT
    exact (hx.2 j).mp ((h (exactStratum_subset_nonsimpleClosedFace u b T hx)).2 j hj)
  · exact nonsimpleClosedFace_antitone u b

theorem nonsimpleClosedFace_eq_iff (u : Fin m → E) (b : Fin m → ℝ)
    (S T : Finset (Fin m)) (hS : (exactStratum u b S).Nonempty)
    (hT : (exactStratum u b T).Nonempty) :
    nonsimpleClosedFace u b S=nonsimpleClosedFace u b T ↔ S=T := by
  constructor
  · intro h
    exact Finset.Subset.antisymm
      ((nonsimpleClosedFace_subset_iff u b S T hT).mp h.symm.subset)
      ((nonsimpleClosedFace_subset_iff u b T S hS).mp h.subset)
  · rintro rfl
    rfl

def nonsimpleFaceNormalSpace (u : Fin m → E) (S : Finset (Fin m)) : Submodule ℝ E :=
  Submodule.span ℝ (u '' (S : Set (Fin m)))

theorem nonsimpleFaceNormalSpace_mono (u : Fin m → E)
    {S T : Finset (Fin m)} (hST : S⊆T) :
    nonsimpleFaceNormalSpace u S≤nonsimpleFaceNormalSpace u T :=
  Submodule.span_mono (Set.image_mono (by simpa using hST))

theorem nonsimple_normal_mem (u : Fin m → E) (S : Finset (Fin m))
    (j : Fin m) (hj : j∈S) : u j∈nonsimpleFaceNormalSpace u S :=
  Submodule.subset_span ⟨j,hj,rfl⟩

/-- A genuine face with nonempty exact stratum and actual normal rank q. -/
abbrev NonsimpleFaceIndex (u : Fin m → E) (b : Fin m → ℝ) (q : ℕ) :=
  {S : Finset (Fin m) // (exactStratum u b S).Nonempty ∧
    Module.finrank ℝ (nonsimpleFaceNormalSpace u S)=q}

noncomputable instance nonsimpleFaceIndexFintype (u : Fin m → E) (b : Fin m → ℝ) (q : ℕ) :
    Fintype (NonsimpleFaceIndex u b q) := Fintype.ofFinite _

def nonsimpleFaceRepresentative (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) : E := F.2.1.choose

theorem nonsimpleFaceRepresentative_mem (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) :
    nonsimpleFaceRepresentative u b F∈exactStratum u b F.1 := F.2.1.choose_spec

theorem nonsimpleFaceRepresentative_levels (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) (j : Fin m) (hj : j∈F.1) :
    ⟪u j,nonsimpleFaceRepresentative u b F⟫_ℝ=b j :=
  ((nonsimpleFaceRepresentative_mem u b F).2 j).mpr hj

theorem nonsimpleFaceRepresentative_strict (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) (j : Fin m) (hj : j∉F.1) :
    ⟪u j,nonsimpleFaceRepresentative u b F⟫_ℝ<b j := by
  have hx := nonsimpleFaceRepresentative_mem u b F
  exact lt_of_le_of_ne (hx.1 j) (fun he => hj ((hx.2 j).mp he))

theorem nonsimpleFaceRepresentative_activeSet (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) :
    nonsimpleActiveSet u b (nonsimpleFaceRepresentative u b F)=F.1 :=
  ((mem_exactStratum_iff_activeSet u b _ _).mp (nonsimpleFaceRepresentative_mem u b F)).2

theorem nonsimpleFaceIndex_closedFace_injective (u : Fin m → E) (b : Fin m → ℝ) (q : ℕ) :
    Function.Injective (fun F : NonsimpleFaceIndex u b q => nonsimpleClosedFace u b F.1) := by
  intro F G h
  exact Subtype.ext ((nonsimpleClosedFace_eq_iff u b _ _ F.2.1 G.2.1).mp h)

def nonsimpleFaceIncidences (u : Fin m → E) (b : Fin m → ℝ) (q d : ℕ) :=
  {P : NonsimpleFaceIndex u b q × NonsimpleFaceIndex u b d // P.1.1⊆P.2.1}

noncomputable instance nonsimpleFaceIncidencesFintype (u : Fin m → E) (b : Fin m → ℝ) (q d : ℕ) :
    Fintype (nonsimpleFaceIncidences u b q d) := by
  unfold nonsimpleFaceIncidences
  exact Fintype.ofFinite _

theorem nonsimpleFaceIncidence_closedFace_subset (u : Fin m → E) (b : Fin m → ℝ) {q d : ℕ}
    (I : nonsimpleFaceIncidences u b q d) :
    nonsimpleClosedFace u b I.1.2.1⊆nonsimpleClosedFace u b I.1.1.1 :=
  nonsimpleClosedFace_antitone u b I.2

/-- The strict polar vector comes from an actual interior point minus
the actual face representative; it is not a cone-separation premise. -/
theorem nonsimpleFace_exists_strictPolar (u : Fin m → E) (b : Fin m → ℝ)
    (hi : ∃ x : E,∀ j,⟪u j,x⟫_ℝ<b j) {q : ℕ} (F : NonsimpleFaceIndex u b q) :
    ∃ d : E,∀ j∈F.1,⟪u j,d⟫_ℝ<0 := by
  obtain ⟨x,hx⟩ := hi
  refine ⟨x-nonsimpleFaceRepresentative u b F,?_⟩
  intro j hj
  rw [inner_sub_right,nonsimpleFaceRepresentative_levels u b F j hj]
  exact sub_neg.mpr (hx j)

theorem nonsimpleFace_generated_isOutward (u : Fin m → E) (b : Fin m → ℝ) {q : ℕ}
    (F : NonsimpleFaceIndex u b q) (c : Fin m → ℝ) (hc : ∀ j∈F.1,0≤c j) :
    IsOutwardNormal (polyhedron u b) (nonsimpleFaceRepresentative u b F)
      (coneDisplacement u F.1 c) :=
  coneDisplacement_isOutward u b F.1 (nonsimpleFaceRepresentative_mem u b F) c hc

end
end RectangleCLTArxivV1
