import RectangleCLTCompanion.SignedSurfaceGeometry

/-! Actual half-space intersections and their disjoint outward tubes. The
strata use the complete active set, so redundant descriptions cause no
unproved disjointness assertion. -/

open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable {ι : Type*}

def polyhedron (normal : ι → E) (offset : ι → ℝ) : Set E :=
  {z | ∀ j, ⟪normal j, z⟫_ℝ ≤ offset j}

def exactStratum (normal : ι → E) (offset : ι → ℝ) (active : Finset ι) : Set E :=
  {z | z ∈ polyhedron normal offset ∧
    ∀ j, ⟪normal j, z⟫_ℝ = offset j ↔ j ∈ active}

def coneDisplacement (normal : ι → E) (active : Finset ι) (coeff : ι → ℝ) : E :=
  ∑ j ∈ active, coeff j • normal j

theorem coneDisplacement_isOutward (normal : ι → E) (offset : ι → ℝ)
    (active : Finset ι) {z : E} (hz : z ∈ exactStratum normal offset active)
    (coeff : ι → ℝ) (hcoeff : ∀ j ∈ active, 0 ≤ coeff j) :
    IsOutwardNormal (polyhedron normal offset) z (coneDisplacement normal active coeff) := by
  intro w hw
  simp only [coneDisplacement, sum_inner]
  apply Finset.sum_nonpos
  intro j hj
  rw [inner_smul_left, conj_trivial]
  apply mul_nonpos_of_nonneg_of_nonpos (hcoeff j hj)
  rw [inner_sub_right, (hz.2 j).mpr hj]
  exact sub_nonpos.mpr (hw j)

theorem exactStratum_disjoint (normal : ι → E) (offset : ι → ℝ)
    {active other : Finset ι} (hne : active ≠ other) :
    Disjoint (exactStratum normal offset active) (exactStratum normal offset other) := by
  rw [Set.disjoint_left]
  intro z hz hw
  apply hne
  ext j
  exact (hz.2 j).symm.trans (hw.2 j)

/-- The tube is a genuine subset of the ambient space. Its base point has
exactly the stated active constraints and its displacement is a nonzero
positive combination of their outward normals. -/
def outwardTube (normal : ι → E) (offset : ι → ℝ) (active : Finset ι) (ε : ℝ) : Set E :=
  {y | ∃ z ∈ exactStratum normal offset active, ∃ coeff : ι → ℝ,
    (∀ j ∈ active, 0 ≤ coeff j) ∧
    coneDisplacement normal active coeff ≠ 0 ∧
    ‖coneDisplacement normal active coeff‖ ≤ ε ∧
    y = z + coneDisplacement normal active coeff}

theorem outwardTube_disjoint (normal : ι → E) (offset : ι → ℝ)
    {active other : Finset ι} (hne : active ≠ other) (ε η : ℝ) :
    Disjoint (outwardTube normal offset active ε) (outwardTube normal offset other η) := by
  rw [Set.disjoint_left]
  rintro y ⟨z, hz, c, hc, _, _, hy⟩ ⟨w, hw, d, hd, _, _, hy'⟩
  have hbase : z = w := outward_base_unique hz.1 hw.1
    (coneDisplacement_isOutward normal offset active hz c hc)
    (coneDisplacement_isOutward normal offset other hw d hd) (hy.symm.trans hy')
  exact Set.disjoint_left.mp (exactStratum_disjoint normal offset hne) hz (hbase.symm ▸ hw)

theorem outwardTube_subset_outerDifference (normal : ι → E) (offset : ι → ℝ)
    (hnormal : ∀ j, ‖normal j‖ = 1) (active : Finset ι) (ε : ℝ) :
    outwardTube normal offset active ε ⊆
      polyhedron normal (fun j => offset j + ε) \ polyhedron normal offset := by
  rintro y ⟨z, hz, c, hc, hv0, hvε, rfl⟩
  constructor
  · intro j
    have hinner : ⟪normal j, coneDisplacement normal active c⟫_ℝ ≤ ε := by
      calc
        _ ≤ |⟪normal j, coneDisplacement normal active c⟫_ℝ| := le_abs_self _
        _ ≤ ‖normal j‖ * ‖coneDisplacement normal active c‖ := abs_real_inner_le_norm _ _
        _ = ‖coneDisplacement normal active c‖ := by rw [hnormal j, one_mul]
        _ ≤ ε := hvε
    rw [inner_add_right]
    exact add_le_add (hz.1 j) hinner
  · exact outward_point_not_mem
      (coneDisplacement_isOutward normal offset active hz c hc) hv0

/-- A ridge rectangle sits in the tube of its actual active stratum when
its two unit normals are selected active constraints. -/
theorem ridgeRectangle_mem_outwardTube [DecidableEq ι] (normal : ι → E) (offset : ι → ℝ)
    (active : Finset ι) {j k : ι} (hj : j ∈ active) (hk : k ∈ active)
    {z : E} (hz : z ∈ exactStratum normal offset active)
    (hu : ‖normal j‖ = 1) (hv : ‖normal k‖ = 1)
    (hp : normal j + normal k ≠ 0) (hm : normal j - normal k ≠ 0)
    {ε : ℝ} (hε : 0 < ε) {st : ℝ × ℝ}
    (hst : st ∈ ridgeRectangle (normal j) (normal k) ε) :
    z + ridgeDisplacement (normal j) (normal k) st ∈
      outwardTube normal offset active ε := by
  obtain ⟨a, b, ha, hb, heq⟩ :=
    ridgeRectangle_maps_into_cone (normal j) (normal k) hu hv hp hm hε.le hst
  let c : ι → ℝ := fun i => (if i = j then a else 0) + (if i = k then b else 0)
  have hdisp : coneDisplacement normal active c =
      ridgeDisplacement (normal j) (normal k) st := by
    rw [heq]
    simp only [coneDisplacement, c, add_smul, ite_smul, zero_smul]
    rw [Finset.sum_add_distrib, Finset.sum_ite_eq' active j, Finset.sum_ite_eq' active k]
    simp [hj, hk]
  refine ⟨z, hz, c, ?_, ?_, ?_, ?_⟩
  · intro i hi
    dsimp [c]
    split_ifs <;> positivity
  · rw [hdisp]
    exact ridgeRectangle_displacement_ne_zero (normal j) (normal k) (hu.trans hv.symm) hp hε hst
  · rw [hdisp]
    exact ridgeRectangle_displacement_norm_le (normal j) (normal k) hu hv hp hm hε.le hst
  · rw [hdisp]

end
end RectangleCLT.Companion.SignedSurface
