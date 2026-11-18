import RectangleCLTArxivV1.SupplementalHTripleIncidenceAtoms
import RectangleCLTArxivV1.SupplementalHTripleTransportModel
import RectangleCLTArxivV1.SupplementalHTrihedralResidualConormal
import RectangleCLTArxivV1.SupplementalHTrihedralFiberBound

/-! The actual signed three-ridge incidence group in the concrete
three-dimensional normal-space model. All conormal and angle identities
are derived from the original normals and actual Gram--Schmidt frame. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

private theorem incidence_isometry_bisector {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (L : E →ₗᵢ[ℝ] G) (x y : E) : L (bisector x y)=bisector (L x) (L y) := by
  unfold bisector
  rw [map_smul,map_add]
  congr 1
  rw [← map_add,L.norm_map]

private theorem incidence_isometry_difference {E G : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup G] [InnerProductSpace ℝ G]
    (L : E →ₗᵢ[ℝ] G) (x y : E) :
    L (differenceDirection x y)=differenceDirection (L x) (L y) := by
  unfold differenceDirection
  rw [map_smul,map_sub]
  congr 1
  rw [← map_sub,L.norm_map]

theorem tripleIncidenceTransportIsometry_pair {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3) :
    tripleIncidenceTransportIsometry u F hi hu
        (trihedralPairBisector (tripleIncidenceTransportBasis u F hi hu) i)=
      (WithLp.equiv 2 (Vector r)).symm (tripleIncidenceFirst u F i) ∧
    tripleIncidenceTransportIsometry u F hi hu
        (trihedralPairDifference (tripleIncidenceTransportBasis u F hi hu) i)=
      (WithLp.equiv 2 (Vector r)).symm (tripleIncidenceSecond u F i) := by
  constructor
  · rw [trihedralPairBisector,incidence_isometry_bisector,
      tripleIncidenceTransportIsometry_basis,tripleIncidenceTransportIsometry_basis]
    exact (thresholdPairBisector_euclidean u _ _).symm
  · rw [trihedralPairDifference,incidence_isometry_difference,
      tripleIncidenceTransportIsometry_basis,tripleIncidenceTransportIsometry_basis]
    exact (thresholdPairDifference_euclidean u _ _).symm

theorem tripleIncidenceTransportIsometry_doubleResidual {m r : ℕ}
    (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3) :
    tripleIncidenceTransportIsometry u F hi hu
        (trihedralDoubleResidual (tripleIncidenceTransportBasis u F hi hu) i)=
      (WithLp.equiv 2 (Vector r)).symm
        (hardPairResidualNormal (tripleIncidenceFirst u F i)
          (tripleIncidenceSecond u F i) (u (F i))) := by
  let L := tripleIncidenceTransportIsometry u F hi hu
  let e := tripleIncidenceTransportBasis u F hi hu
  have hp := tripleIncidenceTransportIsometry_pair u F hi hu i
  have hleft : ⟪trihedralPairBisector e i,e i⟫_ℝ=
      faceDot (u (F i)) (tripleIncidenceFirst u F i) := by
    rw [← L.inner_map_map,tripleIncidenceTransportIsometry_basis,hp.1,
      faceDot_eq_euclidean_inner,real_inner_comm]
    rfl
  have hright : ⟪trihedralPairDifference e i,e i⟫_ℝ=
      faceDot (u (F i)) (tripleIncidenceSecond u F i) := by
    rw [← L.inner_map_map,tripleIncidenceTransportIsometry_basis,hp.2,
      faceDot_eq_euclidean_inner,real_inner_comm]
    rfl
  change L (e i-⟪trihedralPairBisector e i,e i⟫_ℝ • trihedralPairBisector e i-
    ⟪trihedralPairDifference e i,e i⟫_ℝ • trihedralPairDifference e i)=_
  rw [map_sub,map_sub,map_smul,map_smul,
    tripleIncidenceTransportIsometry_basis,hleft,hright,hp.1,hp.2,
    hardPairResidualNormal_eq_sub _ _ _ (tripleIncidence_pair_geometry u F hi hu i).2.2,
    WithLp.equiv_symm_sub,WithLp.equiv_symm_sub,
    WithLp.equiv_symm_smul,WithLp.equiv_symm_smul]
  rfl

theorem tripleIncidenceTransportIsometry_conormal {m r : ℕ}
    (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3) :
    tripleIncidenceTransportIsometry u F hi hu
        (trihedralInwardNormal (tripleIncidenceTransportBasis u F hi hu) i)=
      (WithLp.equiv 2 (Vector r)).symm (tripleIncidenceThird u F i) := by
  let L := tripleIncidenceTransportIsometry u F hi hu
  let e := tripleIncidenceTransportBasis u F hi hu
  have hn : ‖trihedralDoubleResidual e i‖=tripleIncidenceScale u F i := by
    rw [← L.norm_map,tripleIncidenceTransportIsometry_doubleResidual]
    change ‖(WithLp.equiv 2 (Vector r)).symm
      (hardPairResidualNormal (tripleIncidenceFirst u F i)
        (tripleIncidenceSecond u F i) (u (F i)))‖=
      Real.sqrt (vectorNormSq (hardPairResidualNormal (tripleIncidenceFirst u F i)
        (tripleIncidenceSecond u F i) (u (F i))))
    rw [vectorNormSq_eq_euclidean_norm_sq,Real.sqrt_sq (norm_nonneg _)]
  rw [← trihedralResidualUnitNormal_eq_inward e
    (tripleIncidenceTransportBasis_norm u F hi hu) i]
  change L (‖trihedralDoubleResidual e i‖⁻¹ • trihedralDoubleResidual e i)=_
  rw [map_smul,hn,tripleIncidenceTransportIsometry_doubleResidual]
  change _=(WithLp.equiv 2 (Vector r)).symm
    ((tripleIncidenceScale u F i)⁻¹ • hardPairResidualNormal
      (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (u (F i)))
  rw [WithLp.equiv_symm_smul]

theorem tripleIncidenceTransportBasis_angle {m r : ℕ}
    (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3) :
    trihedralEdgeAngle (tripleIncidenceTransportBasis u F hi hu) i=
      tripleIncidenceAngle u F i := by
  unfold trihedralEdgeAngle tripleIncidenceAngle
  congr 1
  rw [← (tripleIncidenceTransportIsometry u F hi hu).inner_map_map,
    tripleIncidenceTransportIsometry_basis,tripleIncidenceTransportIsometry_basis,
    faceDot_eq_euclidean_inner]
  rfl

theorem tripleIncidenceTransportIsometry_weighted_conormals {m r : ℕ}
    (u : Fin m → Vector r) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) :
    tripleIncidenceTransportIsometry u F hi hu
        (∑ i,trihedralEdgeAngle (tripleIncidenceTransportBasis u F hi hu) i •
          trihedralInwardNormal (tripleIncidenceTransportBasis u F hi hu) i)=
      ∑ i,tripleIncidenceAngle u F i •
        (WithLp.equiv 2 (Vector r)).symm (tripleIncidenceThird u F i) := by
  simp_rw [map_sum,map_smul,tripleIncidenceTransportBasis_angle,
    tripleIncidenceTransportIsometry_conormal]

theorem tripleIncidence_shift_scale_eq_conormal_pairing {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (i : Fin 3) :
    tripleIncidenceShift u b F i/tripleIncidenceScale u F i=
      ⟪trihedralInwardNormal (tripleIncidenceTransportBasis u F hi hu) i,
        tripleIncidenceTransportPoint u b F⟫_ℝ := by
  rw [← (tripleIncidenceTransportIsometry u F hi hu).inner_map_map,
    tripleIncidenceTransportIsometry_conormal,tripleIncidenceTransportIsometry_point,
    real_inner_comm,tripleIncidence_normal_distance_pairing u b F hi hu i]

/-- The exact signed coefficient of the three actual incidences is paid
by its genuine conical normal fiber. No incidence count or angle gap
enters this pointwise estimate. -/
theorem tripleIncidence_signed_coefficient_fourth_bound {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖) (x : EuclideanSpace ℝ (Fin r))
    (hz : ‖tripleIncidenceTransportPoint u b F‖≤R x) :
    abs (∑ i,tripleIncidenceAngle u F i*
      (tripleIncidenceShift u b F i/tripleIncidenceScale u F i))*
        RectangleCLT.Companion.SignedSurface.gaussianKernel (tripleIncidenceTransportPoint u b F)≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ y in
        trihedralGeneratedCone (tripleIncidenceTransportBasis u F hi hu)∩
          Metric.ball (0:EuclideanSpace ℝ (Fin 3)) (1/(4*R x)),
        R (x+tripleIncidenceTransportIsometry u F hi hu y)^4*
          RectangleCLT.Companion.SignedSurface.gaussianKernel
            (tripleIncidenceTransportPoint u b F+y)) := by
  have hb := adaptive_trihedral_boundary_fourth_bound
    (tripleIncidenceTransportBasis u F hi hu) (tripleIncidenceTransportBasis_norm u F hi hu)
    (tripleIncidenceTransportIsometry u F hi hu) R hRm hR hRadd x
    (tripleIncidenceTransportPoint u b F) hz
  simp_rw [trihedralResidualUnitNormal_eq_inward _
    (tripleIncidenceTransportBasis_norm u F hi hu),tripleIncidenceTransportBasis_angle,
    ← tripleIncidence_shift_scale_eq_conormal_pairing u b F hi hu] at hb
  exact hb

theorem hardGaussianRidgeThirdIncidenceGroup_eq_trihedral_vector {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (hreg : TripleIncidenceRegularity u b F) :
    hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=
      tripleIncidenceCommonMass u b F*⟪tripleIncidenceTransportPoint u b F,
        ∑ i,trihedralEdgeAngle (tripleIncidenceTransportBasis u F hi hu) i •
          trihedralInwardNormal (tripleIncidenceTransportBasis u F hi hu) i⟫_ℝ := by
  rw [hardGaussianRidgeThirdIncidenceGroup_eq_common_vector u b F hi hu hreg,
    ← tripleIncidenceTransportIsometry_weighted_conormals u F hi hu,
    ← tripleIncidenceTransportIsometry_point u b F hi hu,
    (tripleIncidenceTransportIsometry u F hi hu).inner_map_map]

/-- The actual three signed ridge incidences, with every additional hard
inequality retained in their common mass, have the actual spherical
normal-cone vector coefficient. -/
theorem hardGaussianRidgeThirdIncidenceGroup_eq_spherical_vector {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (hreg : TripleIncidenceRegularity u b F) :
    hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=
      tripleIncidenceCommonMass u b F*⟪tripleIncidenceTransportPoint u b F,
        (2 : ℝ) • ∫ ω in supplementalHSphericalSection
          (trihedralGeneratedCone (tripleIncidenceTransportBasis u F hi hu)),
          ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ := by
  rw [hardGaussianRidgeThirdIncidenceGroup_eq_trihedral_vector u b F hi hu hreg,
    trihedral_spherical_balance _ (tripleIncidenceTransportBasis_norm u F hi hu)]

end
end RectangleCLTArxivV1
