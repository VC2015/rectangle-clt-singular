import RectangleCLTArxivV1.SupplementalHNonsimpleFaceGeometry
import RectangleCLTArxivV1.SupplementalHSphericalBalance

/-! A concrete nonsimple vertex: the square cone z >= |x|, |y| has four
genuine facets active at the origin and a three-dimensional normal space. -/
namespace RectangleCLTArxivV1
open Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def nonsimpleSquareScale : ℝ := (Real.sqrt 2)⁻¹

theorem nonsimpleSquareScale_pos : 0<nonsimpleSquareScale :=
  inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))

theorem nonsimpleSquareScale_sq : nonsimpleSquareScale^2=(1 : ℝ)/2 := by
  rw [nonsimpleSquareScale,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤2)]
  norm_num

def nonsimpleSquareRawNormals : Fin 4 → Vector 3 :=
  ![![1,0,-1],![-1,0,-1],![0,1,-1],![0,-1,-1]]

def nonsimpleSquareNormals (j : Fin 4) : Vector 3 :=
  nonsimpleSquareScale • nonsimpleSquareRawNormals j

def nonsimpleSquareDefect (x : Vector 3) : Vector 4 :=
  ![x 0-x 2,-x 0-x 2,x 1-x 2,-x 1-x 2]

theorem nonsimpleSquareNormals_dot (j : Fin 4) (x : Vector 3) :
    faceDot (nonsimpleSquareNormals j) x=
      nonsimpleSquareScale*nonsimpleSquareDefect x j := by
  fin_cases j <;>
    simp [nonsimpleSquareNormals,nonsimpleSquareRawNormals,nonsimpleSquareDefect,
      faceDot,Fin.sum_univ_succ] <;> ring

theorem nonsimpleSquareRawNormals_normSq (j : Fin 4) :
    vectorNormSq (nonsimpleSquareRawNormals j)=2 := by
  fin_cases j <;> norm_num [nonsimpleSquareRawNormals,vectorNormSq,Fin.sum_univ_succ]

theorem nonsimpleSquareNormals_unit (j : Fin 4) : vectorNormSq (nonsimpleSquareNormals j)=1 := by
  have hs : vectorNormSq (nonsimpleSquareNormals j)=
      nonsimpleSquareScale^2*vectorNormSq (nonsimpleSquareRawNormals j) := by
    simp only [nonsimpleSquareNormals,vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,
      Finset.mul_sum]
  rw [hs,nonsimpleSquareScale_sq,nonsimpleSquareRawNormals_normSq]
  norm_num

theorem nonsimpleSquare_four_normal_relation :
    nonsimpleSquareNormals 0+nonsimpleSquareNormals 1=
      nonsimpleSquareNormals 2+nonsimpleSquareNormals 3 := by
  ext k
  fin_cases k <;> norm_num [nonsimpleSquareNormals,nonsimpleSquareRawNormals]

def nonsimpleSquareCone : Set (Vector 3) :=
  {x | |x 0|≤x 2 ∧ |x 1|≤x 2}

theorem nonsimpleSquareCone_eq_thresholdEvent :
    nonsimpleSquareCone=gaussianFiniteThresholdEvent Finset.univ nonsimpleSquareNormals 0 := by
  ext x
  change (|x 0|≤x 2 ∧ |x 1|≤x 2) ↔
    ∀ j∈Finset.univ,faceDot (nonsimpleSquareNormals j) x≤0
  simp_rw [nonsimpleSquareNormals_dot]
  constructor
  · rintro ⟨hx,hy⟩ j _
    rcases abs_le.mp hx with ⟨hx0,hx1⟩
    rcases abs_le.mp hy with ⟨hy0,hy1⟩
    apply mul_nonpos_of_nonneg_of_nonpos nonsimpleSquareScale_pos.le
    fin_cases j <;> simp [nonsimpleSquareDefect] <;> linarith
  · intro h
    have hh (j : Fin 4) : nonsimpleSquareDefect x j≤0 :=
      (mul_le_mul_left nonsimpleSquareScale_pos).mp
        (by simpa only [mul_zero] using h j (Finset.mem_univ _))
    have h0 := hh 0
    have h1 := hh 1
    have h2 := hh 2
    have h3 := hh 3
    simp [nonsimpleSquareDefect] at h0 h1 h2 h3
    exact ⟨abs_le.mpr ⟨by linarith,by linarith⟩,abs_le.mpr ⟨by linarith,by linarith⟩⟩

theorem nonsimpleSquare_strictInterior : HasStrictFacetInterior nonsimpleSquareNormals 0 := by
  refine ⟨![0,0,1],?_⟩
  intro j
  rw [nonsimpleSquareNormals_dot]
  have hs := nonsimpleSquareScale_pos
  fin_cases j <;> norm_num [nonsimpleSquareDefect] <;> linarith

def nonsimpleSquareDeletionWitness : Fin 4 → Vector 3 :=
  ![![2,0,1],![-2,0,1],![0,2,1],![0,-2,1]]

theorem nonsimpleSquare_irredundant : HasIrredundantFacetWitnesses nonsimpleSquareNormals 0 := by
  intro j
  refine ⟨nonsimpleSquareDeletionWitness j,?_,?_⟩
  · intro k hkj
    rw [nonsimpleSquareNormals_dot]
    have hs := nonsimpleSquareScale_pos
    fin_cases j <;> fin_cases k <;>
      norm_num [nonsimpleSquareDeletionWitness,nonsimpleSquareDefect] at * <;> linarith
  · rw [nonsimpleSquareNormals_dot]
    have hs := nonsimpleSquareScale_pos
    fin_cases j <;> norm_num [nonsimpleSquareDeletionWitness,nonsimpleSquareDefect] <;> linarith

def nonsimpleSquareEuclideanNormals (j : Fin 4) : E3 :=
  (WithLp.equiv 2 (Vector 3)).symm (nonsimpleSquareNormals j)

def nonsimpleSquareEuclideanRawNormals (j : Fin 4) : E3 :=
  (WithLp.equiv 2 (Vector 3)).symm (nonsimpleSquareRawNormals j)

theorem nonsimpleSquareEuclideanNormals_inner (j : Fin 4) (x : E3) :
    ⟪nonsimpleSquareEuclideanNormals j,x⟫_ℝ=
      nonsimpleSquareScale*nonsimpleSquareDefect (WithLp.equiv 2 (Vector 3) x) j := by
  have h := nonsimpleSquareNormals_dot j (WithLp.equiv 2 (Vector 3) x)
  rw [faceDot_eq_euclidean_inner] at h
  exact h

theorem nonsimpleSquareEuclideanNormals_unit (j : Fin 4) :
    ‖nonsimpleSquareEuclideanNormals j‖=1 := by
  have h : ‖nonsimpleSquareEuclideanNormals j‖^2=1 := by
    rw [←supplementalH_vectorNormSq_equiv]
    exact nonsimpleSquareNormals_unit j
  nlinarith [norm_nonneg (nonsimpleSquareEuclideanNormals j)]

theorem nonsimpleSquare_euclidean_strictInterior :
    ∃ x : E3,∀ j,⟪nonsimpleSquareEuclideanNormals j,x⟫_ℝ<(0 : Vector 4) j := by
  obtain ⟨x,hx⟩ := nonsimpleSquare_strictInterior
  refine ⟨(WithLp.equiv 2 (Vector 3)).symm x,?_⟩
  intro j
  have h := hx j
  rw [faceDot_eq_euclidean_inner] at h
  exact h

theorem nonsimpleSquare_euclidean_irredundant :
    ∀ j,∃ x : E3,(∀ k,k≠j → ⟪nonsimpleSquareEuclideanNormals k,x⟫_ℝ≤0) ∧
      0<⟪nonsimpleSquareEuclideanNormals j,x⟫_ℝ := by
  intro j
  obtain ⟨x,hx,hj⟩ := nonsimpleSquare_irredundant j
  refine ⟨(WithLp.equiv 2 (Vector 3)).symm x,?_,?_⟩
  · intro k hkj
    have h := hx k hkj
    rw [faceDot_eq_euclidean_inner] at h
    exact h
  · rw [faceDot_eq_euclidean_inner] at hj
    exact hj

theorem nonsimpleSquareRawNormals_mem_normalSpace (j : Fin 4) :
    nonsimpleSquareEuclideanRawNormals j∈
      nonsimpleFaceNormalSpace nonsimpleSquareEuclideanNormals Finset.univ := by
  have he : nonsimpleSquareEuclideanRawNormals j=
      Real.sqrt 2 • nonsimpleSquareEuclideanNormals j := by
    apply PiLp.ext
    intro k
    change nonsimpleSquareRawNormals j k=
      Real.sqrt 2*(nonsimpleSquareScale*nonsimpleSquareRawNormals j k)
    rw [nonsimpleSquareScale,←mul_assoc,mul_inv_cancel₀ (Real.sqrt_pos.2 (by norm_num)).ne',one_mul]
  rw [he]
  exact Submodule.smul_mem _ _ (nonsimple_normal_mem _ _ j (Finset.mem_univ _))

theorem nonsimpleSquare_normalSpace_eq_top :
    nonsimpleFaceNormalSpace nonsimpleSquareEuclideanNormals Finset.univ=⊤ := by
  apply top_unique
  intro x _
  have he : x=((x 0-x 1-x 2)/2) • nonsimpleSquareEuclideanRawNormals 0+
      ((-x 0-x 1-x 2)/2) • nonsimpleSquareEuclideanRawNormals 1+
      x 1 • nonsimpleSquareEuclideanRawNormals 2 := by
    apply PiLp.ext
    intro k
    fin_cases k <;>
      simp [nonsimpleSquareEuclideanRawNormals,nonsimpleSquareRawNormals] <;> ring
  rw [he]
  exact Submodule.add_mem _
    (Submodule.add_mem _ (Submodule.smul_mem _ _ (nonsimpleSquareRawNormals_mem_normalSpace 0))
      (Submodule.smul_mem _ _ (nonsimpleSquareRawNormals_mem_normalSpace 1)))
    (Submodule.smul_mem _ _ (nonsimpleSquareRawNormals_mem_normalSpace 2))

theorem nonsimpleSquare_normal_rank_three :
    Module.finrank ℝ (nonsimpleFaceNormalSpace nonsimpleSquareEuclideanNormals Finset.univ)=3 := by
  rw [nonsimpleSquare_normalSpace_eq_top]
  simp

theorem nonsimpleSquare_origin_exactStratum :
    (0 : E3)∈exactStratum nonsimpleSquareEuclideanNormals 0 Finset.univ := by
  simp [exactStratum,polyhedron]

theorem nonsimpleSquare_exactStratum_eq_singleton :
    exactStratum nonsimpleSquareEuclideanNormals 0 Finset.univ={(0 : E3)} := by
  ext x
  constructor
  · intro hx
    have hinner (j : Fin 4) : ⟪nonsimpleSquareEuclideanNormals j,x⟫_ℝ=0 :=
      (hx.2 j).mpr (Finset.mem_univ _)
    have hd (j : Fin 4) : nonsimpleSquareDefect (WithLp.equiv 2 (Vector 3) x) j=0 := by
      have h := hinner j
      rw [nonsimpleSquareEuclideanNormals_inner] at h
      exact (mul_eq_zero.mp h).resolve_left nonsimpleSquareScale_pos.ne'
    have h0 := hd 0
    have h1 := hd 1
    have h2 := hd 2
    change x 0-x 2=0 at h0
    change -x 0-x 2=0 at h1
    change x 1-x 2=0 at h2
    apply Set.mem_singleton_iff.mpr
    apply PiLp.ext
    intro k
    fin_cases k
    · change x 0=0
      linarith
    · change x 1=0
      linarith
    · change x 2=0
      linarith
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    exact nonsimpleSquare_origin_exactStratum

/-- An actual codimension-three face with four active original facets. -/
def nonsimpleSquareActualVertex : NonsimpleFaceIndex nonsimpleSquareEuclideanNormals 0 3 :=
  ⟨Finset.univ,⟨⟨0,nonsimpleSquare_origin_exactStratum⟩,nonsimpleSquare_normal_rank_three⟩⟩

theorem nonsimpleSquareActualVertex_card : nonsimpleSquareActualVertex.1.card=4 := by
  norm_num [nonsimpleSquareActualVertex]

theorem nonsimpleSquareActualVertex_is_nonsimple : 3<nonsimpleSquareActualVertex.1.card := by
  rw [nonsimpleSquareActualVertex_card]
  norm_num

end
end RectangleCLTArxivV1
