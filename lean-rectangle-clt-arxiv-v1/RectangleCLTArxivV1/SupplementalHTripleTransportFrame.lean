import RectangleCLTArxivV1.SupplementalHTripleTransportDensity
import RectangleCLTArxivV1.SupplementalHTripleFiber

/-! A genuine three-normal frame from an actual linear isometry. The
section point is its actual affine normal point plus orthogonal residual. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tripleTransportFrame {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (i : Fin 3) : EuclideanSpace ℝ (Fin r) := L (EuclideanSpace.basisFun (Fin 3) ℝ i)

def tripleTransportNormal {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (i : Fin 3) : Vector r :=
  fun j => tripleTransportFrame L i j

theorem tripleTransportFrame_orthonormal {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :
    Orthonormal ℝ (tripleTransportFrame L) :=
  (EuclideanSpace.basisFun (Fin 3) ℝ).orthonormal.comp_linearIsometry L

theorem tripleTransportNormal_unit {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (i : Fin 3) :
    vectorNormSq (tripleTransportNormal L i)=1 := by
  rw [vectorNormSq_eq_euclidean_norm_sq]
  change ‖tripleTransportFrame L i‖^2=1
  rw [(tripleTransportFrame_orthonormal L).norm_eq_one i]
  norm_num

theorem tripleTransportNormal_orthogonal {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (i j : Fin 3) (hij : i≠j) : faceDot (tripleTransportNormal L i) (tripleTransportNormal L j)=0 := by
  have he : faceDot (tripleTransportNormal L i) (tripleTransportNormal L j)=
      ⟪tripleTransportFrame L i,tripleTransportFrame L j⟫_ℝ := faceDot_eq_euclidean_inner _ _
  rw [he]
  exact (tripleTransportFrame_orthonormal L).2 hij

theorem tripleTransportFrame_sum {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z : EuclideanSpace ℝ (Fin 3)) : L z=∑ i,z i • tripleTransportFrame L i := by
  have he := congrArg L ((EuclideanSpace.basisFun (Fin 3) ℝ).sum_repr z)
  simpa only [map_sum,map_smul,EuclideanSpace.basisFun_repr,tripleTransportFrame] using he.symm

def tripleTransportSection {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) : Vector r :=
  gaussianTripleSectionPoint (tripleTransportNormal L 0) (tripleTransportNormal L 1) (tripleTransportNormal L 2)
    (z 0) (z 1) (z 2) g

theorem tripleTransportSection_measurePreserving {n : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1))) :
    MeasurePreserving (fun z : EuclideanSpace ℝ (Fin 3) × Vector (n+1) => tripleTransportSection L z.1 z.2)
      (tripleEuclideanGaussian.prod (standardGaussian (n+1))) (standardGaussian (n+1)) :=
  gaussianTripleEuclideanSectionMap_measurePreserving _ _ _
    (tripleTransportNormal_unit L 0) (tripleTransportNormal_unit L 1) (tripleTransportNormal_unit L 2)

theorem tripleTransportSection_eq_frame {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    projectionEuclideanVector (tripleTransportSection L z g)=
      gaussianFrameSectionPoint (tripleTransportFrame L) (fun i => z i) (projectionEuclideanVector g) := by
  have horth (i j : Fin 3) (hij : i≠j) := tripleTransportNormal_orthogonal L i j hij
  unfold tripleTransportSection
  rw [gaussianTripleSectionPoint_eq_affine _ _ _ (horth 0 1 (by decide)) (horth 0 2 (by decide)) (horth 1 2 (by decide))]
  have hi (i : Fin 3) : ⟪tripleTransportFrame L i,projectionEuclideanVector g⟫_ℝ=faceDot (tripleTransportNormal L i) g :=
    (faceDot_eq_euclidean_inner _ _).symm
  unfold gaussianFrameSectionPoint gaussianFrameProjection
  simp_rw [hi]
  simp only [Fin.sum_univ_succ,Fin.val_zero,Fin.val_succ,Fin.sum_univ_zero,Fin.succ_zero_eq_one,
    Fin.reduceSucc,add_zero]
  ext k
  change (z 0*tripleTransportFrame L 0 k+z 1*tripleTransportFrame L 1 k+z 2*tripleTransportFrame L 2 k)+g k-
      (faceDot (tripleTransportNormal L 0) g*tripleTransportFrame L 0 k+
        faceDot (tripleTransportNormal L 1) g*tripleTransportFrame L 1 k+
        faceDot (tripleTransportNormal L 2) g*tripleTransportFrame L 2 k)=
    (z 0*tripleTransportFrame L 0 k+(z 1*tripleTransportFrame L 1 k+z 2*tripleTransportFrame L 2 k))+g k-
      (faceDot (tripleTransportNormal L 0) g*tripleTransportFrame L 0 k+
        (faceDot (tripleTransportNormal L 1) g*tripleTransportFrame L 1 k+
          faceDot (tripleTransportNormal L 2) g*tripleTransportFrame L 2 k))
  ring

/-- Actual affine normal point plus the orthogonal residual, independent
of the chosen orthonormal frame of the rank-three normal space. -/
theorem tripleTransportSection_eq_affine_projection {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    projectionEuclideanVector (tripleTransportSection L z g)=L z+projectionEuclideanVector g-
      (Submodule.span ℝ (Set.range (tripleTransportFrame L))).orthogonalProjection (projectionEuclideanVector g) := by
  rw [tripleTransportSection_eq_frame,gaussianFrameSectionPoint_eq_affine_projection _ (tripleTransportFrame_orthonormal L),
    ← tripleTransportFrame_sum]


def tripleTransportCoordinate {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) (g : Vector r) :
    EuclideanSpace ℝ (Fin 3) := projectionEuclideanVector (fun i => faceDot (tripleTransportNormal L i) g)

theorem measurable_tripleTransportCoordinate {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) : Measurable (tripleTransportCoordinate L) := by
  apply (PiLp.continuous_equiv_symm 2 _).measurable.comp
  exact measurable_pi_lambda _ (fun i => measurable_thresholdDot _)

theorem tripleTransportCoordinate_section {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z : EuclideanSpace ℝ (Fin 3)) (g : Vector r) : tripleTransportCoordinate L (tripleTransportSection L z g)=z := by
  have hl := gaussianTripleSectionPoint_levels (tripleTransportNormal L 0) (tripleTransportNormal L 1) (tripleTransportNormal L 2)
    (tripleTransportNormal_unit L 0) (tripleTransportNormal_unit L 1) (tripleTransportNormal_unit L 2)
    (tripleTransportNormal_orthogonal L 0 1 (by decide)) (tripleTransportNormal_orthogonal L 0 2 (by decide))
    (tripleTransportNormal_orthogonal L 1 2 (by decide)) (z 0) (z 1) (z 2) g
  ext i
  fin_cases i
  · exact hl.1
  · exact hl.2.1
  · exact hl.2.2

theorem tripleTransportSection_comp {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z y : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    tripleTransportSection L z (tripleTransportSection L y g)=tripleTransportSection L z g := by
  have ha (a : EuclideanSpace ℝ (Fin 3)) : tripleTransportSection L a g=
      (a 0 • tripleTransportNormal L 0+a 1 • tripleTransportNormal L 1+a 2 • tripleTransportNormal L 2)+g-
        (faceDot (tripleTransportNormal L 0) g • tripleTransportNormal L 0+
          faceDot (tripleTransportNormal L 1) g • tripleTransportNormal L 1+
          faceDot (tripleTransportNormal L 2) g • tripleTransportNormal L 2) :=
    gaussianTripleSectionPoint_eq_affine _ _ _
      (tripleTransportNormal_orthogonal L 0 1 (by decide)) (tripleTransportNormal_orthogonal L 0 2 (by decide))
      (tripleTransportNormal_orthogonal L 1 2 (by decide)) _ _ _ _
  have hl := tripleTransportCoordinate_section L y g
  have h0 : faceDot (tripleTransportNormal L 0) (tripleTransportSection L y g)=y 0 := congrArg (fun a => a 0) hl
  have h1 : faceDot (tripleTransportNormal L 1) (tripleTransportSection L y g)=y 1 := congrArg (fun a => a 1) hl
  have h2 : faceDot (tripleTransportNormal L 2) (tripleTransportSection L y g)=y 2 := congrArg (fun a => a 2) hl
  change gaussianTripleSectionPoint _ _ _ _ _ _ (tripleTransportSection L y g)=_
  rw [gaussianTripleSectionPoint_eq_affine _ _ _
    (tripleTransportNormal_orthogonal L 0 1 (by decide)) (tripleTransportNormal_orthogonal L 0 2 (by decide))
    (tripleTransportNormal_orthogonal L 1 2 (by decide)),h0,h1,h2,ha y,ha z]
  module

theorem tripleTransportSection_add_normal {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (z y : EuclideanSpace ℝ (Fin 3)) (g : Vector r) :
    projectionEuclideanVector (tripleTransportSection L (z+y) g)=
      projectionEuclideanVector (tripleTransportSection L z g)+L y := by
  rw [tripleTransportSection_eq_affine_projection,tripleTransportSection_eq_affine_projection,map_add]
  module

theorem measurable_tripleTransportSection {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r)) :
    Measurable (fun z : EuclideanSpace ℝ (Fin 3) × Vector r => tripleTransportSection L z.1 z.2) := by
  have hm := measurable_gaussianTripleSectionMap (tripleTransportNormal L 0) (tripleTransportNormal L 1) (tripleTransportNormal L 2)
  exact hm.comp (tripleEuclideanScalarEquiv.measurable.prodMap measurable_id)

theorem integral_tripleTransportSection {n : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (F : Vector (n+1) → ℝ) (hF : Measurable F) :
    (∫ z,F (tripleTransportSection L z.1 z.2) ∂tripleEuclideanGaussian.prod (standardGaussian (n+1)))=
      ∫ g,F g ∂standardGaussian (n+1) := by
  have hh := integral_map (μ := tripleEuclideanGaussian.prod (standardGaussian (n+1)))
    (tripleTransportSection_measurePreserving L).measurable.aemeasurable hF.aestronglyMeasurable
  rw [(tripleTransportSection_measurePreserving L).map_eq] at hh
  exact hh.symm

end
end RectangleCLTArxivV1
