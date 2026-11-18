import RectangleCLTArxivV1.SupplementalHTrihedralNormals
import RectangleCLTArxivV1.SupplementalHNormalChartIsometry
import RectangleCLTArxivV1.SupplementalHPositiveWedge

/-! The actual angle-weighted spherical balance of a generated trihedral
normal cone. Conormals, halfspaces, facet rays, and facet angles are all
constructed and identified before applying spherical balance. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set Metric RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)

def trihedralOutwardNormals (e : Basis (Fin 3) ℝ E3) (i : Fin 3) : Vector 3 :=
  WithLp.equiv 2 (Vector 3) (-trihedralInwardNormal e i)

theorem trihedralOutwardNormals_dot (e : Basis (Fin 3) ℝ E3) (i : Fin 3) (x : E3) :
    faceDot (trihedralOutwardNormals e i) (WithLp.equiv 2 (Vector 3) x)=
      ⟪-trihedralInwardNormal e i,x⟫_ℝ := by
  rw [faceDot_eq_euclidean_inner]
  rfl

theorem trihedralOutwardNormals_unit (e : Basis (Fin 3) ℝ E3) (i : Fin 3) :
    vectorNormSq (trihedralOutwardNormals e i)=1 := by
  rw [trihedralOutwardNormals,supplementalH_vectorNormSq_equiv,norm_neg,trihedralInwardNormal_norm,one_pow]

theorem trihedralOutwardNormals_nonparallel (e : Basis (Fin 3) ℝ E3) :
    PairwiseNonparallelNormals (trihedralOutwardNormals e) := by
  intro j l hlj hz
  have hother : faceDot (trihedralOutwardNormals e j) (WithLp.equiv 2 (Vector 3) (e l))=0 := by
    rw [trihedralOutwardNormals_dot,inner_neg_left,trihedralInwardNormal_orthogonal_other e j l hlj,neg_zero]
  have hown : faceDot (trihedralOutwardNormals e l) (WithLp.equiv 2 (Vector 3) (e l))≠0 := by
    rw [trihedralOutwardNormals_dot,inner_neg_left]
    exact neg_ne_zero.mpr (trihedralInwardNormal_positive_own e l).ne'
  have he := congrArg (fun w : Vector 3 => faceDot w (WithLp.equiv 2 (Vector 3) (e l)))
    (sub_eq_zero.mp hz)
  dsimp only at he
  rw [threshold_faceDot_smul_left,hother,mul_zero] at he
  exact hown he

theorem supplementalHPolyhedralCone_trihedral (e : Basis (Fin 3) ℝ E3) :
    supplementalHPolyhedralCone (trihedralOutwardNormals e)=trihedralGeneratedCone e := by
  rw [trihedralGeneratedCone_eq_halfspaces]
  ext x
  change (∀ i∈Finset.univ, faceDot (trihedralOutwardNormals e i)
    (WithLp.equiv 2 (Vector 3) x)≤0) ↔ ∀ i, ⟪-trihedralInwardNormal e i,x⟫_ℝ≤0
  simp only [Finset.mem_univ,forall_const,trihedralOutwardNormals_dot]

def trihedralFacetCoordinates (e : Basis (Fin 3) ℝ E3) (i j : Fin 3) : E2 :=
  (WithLp.equiv 2 (Vector 2)).symm (normalSectionCoordinates (0 : Fin 3)
    (trihedralOutwardNormals e i) (WithLp.equiv 2 (Vector 3) (e j)))

theorem trihedralFacetCoordinates_map (e : Basis (Fin 3) ℝ E3) (i j : Fin 3) (hji : j≠i) :
    euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i)
      (trihedralFacetCoordinates e i j)=e j := by
  have hx : faceDot (trihedralOutwardNormals e i) (WithLp.equiv 2 (Vector 3) (e j))=0 := by
    rw [trihedralOutwardNormals_dot,inner_neg_left,trihedralInwardNormal_orthogonal_other e i j hji,neg_zero]
  change (WithLp.equiv 2 (Vector 3)).symm
    (normalSectionChart (0 : Fin 3) (trihedralOutwardNormals e i) 0
      (normalSectionCoordinates (0 : Fin 3) (trihedralOutwardNormals e i)
        (WithLp.equiv 2 (Vector 3) (e j))))=e j
  rw [normalSectionChart_coordinates _ _ (trihedralOutwardNormals_unit e i) _ hx]
  exact Equiv.symm_apply_apply _ _

theorem trihedralFacetCoordinates_norm (e : Basis (Fin 3) ℝ E3) (i j : Fin 3) (hji : j≠i) :
    ‖trihedralFacetCoordinates e i j‖=‖e j‖ := by
  rw [← (euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i)).norm_map,
    trihedralFacetCoordinates_map e i j hji]

theorem trihedralFacetCoordinates_inner (e : Basis (Fin 3) ℝ E3) (i j k : Fin 3)
    (hji : j≠i) (hki : k≠i) :
    ⟪trihedralFacetCoordinates e i j,trihedralFacetCoordinates e i k⟫_ℝ=⟪e j,e k⟫_ℝ := by
  rw [← (euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i)).inner_map_map,
    trihedralFacetCoordinates_map e i j hji,trihedralFacetCoordinates_map e i k hki]

theorem trihedralFacetChart_mem_iff (e : Basis (Fin 3) ℝ E3) (i : Fin 3) (y : E2) :
    y∈supplementalHFacetCone (trihedralOutwardNormals e) i ↔
      euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i) y∈trihedralGeneratedCone e := by
  rw [← supplementalHPolyhedralCone_trihedral e]
  rfl

theorem trihedralFacetChart_orthogonal (e : Basis (Fin 3) ℝ E3) (i : Fin 3) (y : E2) :
    ⟪trihedralInwardNormal e i,
      euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i) y⟫_ℝ=0 := by
  have hh := normalSectionChart_on_hyperplane (0 : Fin 3) (trihedralOutwardNormals e i)
    (trihedralOutwardNormals_unit e i) 0 (WithLp.equiv 2 (Vector 2) y)
  change faceDot (trihedralOutwardNormals e i) (WithLp.equiv 2 (Vector 3)
    (euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i) y))=0 at hh
  rw [trihedralOutwardNormals_dot,inner_neg_left] at hh
  exact neg_eq_zero.mp hh

private theorem trihedral_sum_erase_two (e : Basis (Fin 3) ℝ E3) (i : Fin 3)
    (a : Fin 3 → ℝ) (hai : a i=0) :
    (∑ l∈Finset.univ.erase i, a l • e l)=
      a (i.succAbove 0) • e (i.succAbove 0)+a (i.succAbove 1) • e (i.succAbove 1) := by
  classical
  calc
    _ = ∑ l, a l • e l := by
      simpa only [hai,zero_smul,add_zero] using
        (Finset.sum_erase_add Finset.univ (fun l => a l • e l) (Finset.mem_univ i))
    _ = _ := by
      rw [Fin.sum_univ_succAbove _ i,hai,zero_smul,zero_add,Fin.sum_univ_two]

/-- The actual facet cone in the actual archived tangent chart is the
positive span of its two explicitly pulled-back generating rays. -/
theorem trihedralFacetCone_eq_positivePlanarWedge (e : Basis (Fin 3) ℝ E3) (i : Fin 3) :
    supplementalHFacetCone (trihedralOutwardNormals e) i=
      positivePlanarWedge (trihedralFacetCoordinates e i (i.succAbove 0))
        (trihedralFacetCoordinates e i (i.succAbove 1)) := by
  let A := euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i)
  have h0 := trihedralFacetCoordinates_map e i (i.succAbove 0) (Fin.succAbove_ne i 0)
  have h1 := trihedralFacetCoordinates_map e i (i.succAbove 1) (Fin.succAbove_ne i 1)
  ext y
  rw [trihedralFacetChart_mem_iff]
  constructor
  · intro hy
    have hfacet : A y∈{x | x∈trihedralGeneratedCone e ∧ ⟪trihedralInwardNormal e i,x⟫_ℝ=0} :=
      ⟨hy,trihedralFacetChart_orthogonal e i y⟩
    rw [trihedral_facet_eq_generated_other e i] at hfacet
    rcases hfacet with ⟨a,ha,hai,hsum⟩
    refine ⟨a (i.succAbove 0),a (i.succAbove 1),ha _,ha _,?_⟩
    apply A.injective
    rw [map_add,map_smul,map_smul,h0,h1]
    rw [trihedral_sum_erase_two e i a hai] at hsum
    exact hsum
  · rintro ⟨a,b,ha,hb,rfl⟩
    rw [map_add,map_smul,map_smul,h0,h1,mem_trihedralGeneratedCone_iff]
    intro l
    simp only [map_add,map_smul,Basis.repr_self,Finsupp.add_apply,Finsupp.smul_apply,
      smul_eq_mul,Finsupp.single_apply]
    positivity

theorem trihedralFacetCoordinates_nonparallel (e : Basis (Fin 3) ℝ E3)
    (i j k : Fin 3) (hji : j≠i) (hki : k≠i) (hjk : j≠k) :
    trihedralFacetCoordinates e i j+trihedralFacetCoordinates e i k≠0 ∧
      trihedralFacetCoordinates e i j-trihedralFacetCoordinates e i k≠0 := by
  let A := euclideanNormalSectionIsometry (0 : Fin 3) (trihedralOutwardNormals e i)
  have hj := trihedralFacetCoordinates_map e i j hji
  have hk := trihedralFacetCoordinates_map e i k hki
  constructor
  · intro hz
    have he : e j+e k=0 := by
      have hh := congrArg A hz
      simpa only [A,map_add,map_zero,hj,hk] using hh
    have hdep : (1 : ℝ) • e j=(-1 : ℝ) • e k := by
      simpa only [one_smul,neg_one_smul] using eq_neg_of_add_eq_zero_left he
    exact hjk (e.linearIndependent.eq_of_smul_apply_eq_smul_apply 1 (-1) j k (by norm_num) hdep)
  · intro hz
    have he : e j-e k=0 := by
      have hh := congrArg A hz
      simpa only [A,map_sub,map_zero,hj,hk] using hh
    exact hjk (e.linearIndependent.injective (sub_eq_zero.mp he))

def trihedralEdgeAngle (e : Basis (Fin 3) ℝ E3) (i : Fin 3) : ℝ :=
  Real.arccos ⟪e (i.succAbove 0),e (i.succAbove 1)⟫_ℝ

/-- Each existing Gaussian facet angle is identified with the ordinary
angle between the two actual unit generating rays. -/
theorem supplementalHFacetAngle_trihedral (e : Basis (Fin 3) ℝ E3)
    (hunit : ∀ i, ‖e i‖=1) (i : Fin 3) :
    supplementalHFacetAngle (trihedralOutwardNormals e) i=trihedralEdgeAngle e i := by
  have h0 := Fin.succAbove_ne i (0 : Fin 2)
  have h1 := Fin.succAbove_ne i (1 : Fin 2)
  have hjk : i.succAbove (0 : Fin 2)≠i.succAbove 1 :=
    (Fin.succAboveEmb i).injective.ne (by decide)
  have hp := trihedralFacetCoordinates_nonparallel e i _ _ h0 h1 hjk
  unfold supplementalHFacetAngle
  rw [trihedralFacetCone_eq_positivePlanarWedge e i,
    positivePlanarWedge_angular_area (by simp) _ _
      ((trihedralFacetCoordinates_norm e i _ h0).trans (hunit _))
      ((trihedralFacetCoordinates_norm e i _ h1).trans (hunit _)) hp.1 hp.2,
    trihedralFacetCoordinates_inner e i _ _ h0 h1]
  rfl

theorem trihedralOutwardNormals_inward (e : Basis (Fin 3) ℝ E3) (i : Fin 3) :
    -((WithLp.equiv 2 (Vector 3)).symm (trihedralOutwardNormals e i))=trihedralInwardNormal e i := by
  unfold trihedralOutwardNormals
  rw [Equiv.symm_apply_apply,neg_neg]

/-- Exact spherical balance of the actual generated trihedral cone.
The three weights are ordinary endpoint angles and the three vectors are
the constructed inward conormals, with no incidence/angle premise. -/
theorem trihedral_spherical_balance (e : Basis (Fin 3) ℝ E3) (hunit : ∀ i, ‖e i‖=1) :
    (∑ i, trihedralEdgeAngle e i • trihedralInwardNormal e i)=
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection (trihedralGeneratedCone e),
        ω.1 ∂(volume : Measure E3).toSphere := by
  have hh := supplementalH_spherical_balance_inward (trihedralOutwardNormals e)
    (trihedralOutwardNormals_unit e) (trihedralOutwardNormals_nonparallel e)
  simp_rw [supplementalHFacetAngle_trihedral e hunit,trihedralOutwardNormals_inward e] at hh
  rw [supplementalHPolyhedralCone_trihedral e] at hh
  exact hh

/-- The actual angle-weighted inward conormals are bounded by twice the
spherical area of their generated cone. -/
theorem trihedral_spherical_balance_norm_le (e : Basis (Fin 3) ℝ E3) (hunit : ∀ i, ‖e i‖=1) :
    ‖∑ i, trihedralEdgeAngle e i • trihedralInwardNormal e i‖ ≤
      2*(volume : Measure E3).toSphere.real (supplementalHSphericalSection (trihedralGeneratedCone e)) := by
  rw [trihedral_spherical_balance e hunit,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1
