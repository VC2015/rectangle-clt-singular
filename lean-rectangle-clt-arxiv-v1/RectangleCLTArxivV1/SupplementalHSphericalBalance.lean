import RectangleCLTArxivV1.SupplementalHSphericalPolar
import RectangleCLTArxivV1.SupplementalHGaussianBoundary
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! Spherical balance for actual three-dimensional polyhedral cones.
Each edge weight is its actual polar angular measure in an orthogonal
facet chart. The signed boundary identity is derived from hard Gaussian
threshold differentiation, rather than assumed as a divergence formula. -/

namespace RectangleCLTArxivV1
open MeasureTheory Set Metric RectangleCLT RectangleCLT.Companion.SignedSurface
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem supplementalH_vectorNormSq_equiv {r : ℕ} (x : EuclideanSpace ℝ (Fin r)) :
    vectorNormSq (WithLp.equiv 2 (Vector r) x) = ‖x‖^2 := by
  rw [PiLp.norm_sq_eq_of_L2]
  simp only [vectorNormSq, Real.norm_eq_abs, sq_abs]
  rfl

theorem supplementalH_normalSectionChart_smul {n : ℕ}
    (j : Fin (n+1)) (u : Vector (n+1)) (r : ℝ) (y : Vector n) :
    normalSectionChart j u 0 (r • y) = r • normalSectionChart j u 0 y := by
  unfold normalSectionChart
  rw [← gaussianRotation_smul]
  congr 1
  ext k
  by_cases hk : k=j
  · subst k
    simp
  · obtain ⟨l,rfl⟩ := Fin.exists_succAbove_eq hk
    simp

theorem supplementalH_thresholdCone_dilation {m r : ℕ}
    (u : Fin m → Vector r) (t : ℝ) (ht : 0<t) (x : Vector r) :
    t • x ∈ gaussianFiniteThresholdEvent Finset.univ u 0 ↔
      x ∈ gaussianFiniteThresholdEvent Finset.univ u 0 := by
  have hd (j : Fin m) : faceDot (u j) (t • x)=t*faceDot (u j) x := by
    simp only [faceDot, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  simp only [gaussianFiniteThresholdEvent, mem_setOf_eq, Pi.zero_apply, hd]
  constructor
  · intro h j hj
    exact (mul_le_mul_left ht).mp (by simpa only [mul_zero] using h j hj)
  · intro h j hj
    simpa only [mul_zero] using (mul_le_mul_left ht).mpr (h j hj)

/-- The actual Euclidean cone, with its three-dimensional Euclidean metric. -/
def supplementalHPolyhedralCone {m : ℕ} (u : Fin m → Vector 3) :
    Set (EuclideanSpace ℝ (Fin 3)) :=
  (EuclideanSpace.measurableEquiv (Fin 3)) ⁻¹'
    gaussianFiniteThresholdEvent Finset.univ u 0

/-- The actual planar facet cone in an orthogonal tangent chart. -/
def supplementalHFacetCone {m : ℕ} (u : Fin m → Vector 3) (j : Fin m) :
    Set (EuclideanSpace ℝ (Fin 2)) :=
  (fun y => normalSectionChart (0 : Fin 3) (u j) 0
    (EuclideanSpace.measurableEquiv (Fin 2) y)) ⁻¹'
      gaussianFiniteThresholdEvent Finset.univ u 0

/-- The geometric edge weight is the angular length of the actual planar
facet section. This definition retains redundant or empty faces correctly. -/
def supplementalHFacetAngle {m : ℕ} (u : Fin m → Vector 3) (j : Fin m) : ℝ :=
  (volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere.real
    (supplementalHSphericalSection (supplementalHFacetCone u j))

theorem supplementalHPolyhedralCone_measurable {m : ℕ} (u : Fin m → Vector 3) :
    MeasurableSet (supplementalHPolyhedralCone u) :=
  (measurableSet_gaussianFiniteThresholdEvent _ _ _).preimage
    (EuclideanSpace.measurableEquiv _).measurable

theorem supplementalHPolyhedralCone_dilation {m : ℕ} (u : Fin m → Vector 3)
    (t : ℝ) (ht : 0<t) (x : EuclideanSpace ℝ (Fin 3)) :
    t • x ∈ supplementalHPolyhedralCone u ↔ x ∈ supplementalHPolyhedralCone u := by
  change WithLp.equiv 2 (Vector 3) (t • x) ∈
    gaussianFiniteThresholdEvent Finset.univ u 0 ↔
    WithLp.equiv 2 (Vector 3) x ∈ gaussianFiniteThresholdEvent Finset.univ u 0
  rw [WithLp.equiv_smul]
  exact supplementalH_thresholdCone_dilation u t ht _

theorem supplementalHFacetCone_measurable {m : ℕ} (u : Fin m → Vector 3) (j : Fin m) :
    MeasurableSet (supplementalHFacetCone u j) :=
  (measurableSet_gaussianFiniteThresholdEvent _ _ _).preimage
    ((measurable_normalSectionChart _ _ _).comp (EuclideanSpace.measurableEquiv _).measurable)

theorem supplementalHFacetCone_dilation {m : ℕ} (u : Fin m → Vector 3)
    (j : Fin m) (t : ℝ) (ht : 0<t) (y : EuclideanSpace ℝ (Fin 2)) :
    t • y ∈ supplementalHFacetCone u j ↔ y ∈ supplementalHFacetCone u j := by
  change normalSectionChart (0 : Fin 3) (u j) 0
    (WithLp.equiv 2 (Vector 2) (t • y)) ∈ gaussianFiniteThresholdEvent Finset.univ u 0 ↔
    normalSectionChart (0 : Fin 3) (u j) 0 (WithLp.equiv 2 (Vector 2) y) ∈
      gaussianFiniteThresholdEvent Finset.univ u 0
  rw [WithLp.equiv_smul, supplementalH_normalSectionChart_smul]
  exact supplementalH_thresholdCone_dilation u t ht _

/-- The actual unnormalized Gaussian surface mass equals the actual edge
angle. No inverse angle or minimum-gap condition occurs. -/
theorem supplementalH_facetKernel_eq_angle {m : ℕ} (u : Fin m → Vector 3) (j : Fin m) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u 0, gaussianKernel g
      ∂affineSurfaceVolume (0 : Fin 3) (u j) 0) = supplementalHFacetAngle u j := by
  let P := gaussianFiniteThresholdEvent Finset.univ u 0
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent _ _ _
  have hk : Measurable (gaussianKernel : Vector 3 → ℝ) := by
    unfold RectangleCLT.gaussianKernel vectorNormSq
    fun_prop
  rw [affineSurfaceVolume, setIntegral_map hP hk.aestronglyMeasurable
    (measurable_normalSectionChart _ _ _).aemeasurable]
  rw [← (EuclideanSpace.volume_preserving_measurableEquiv (Fin 2)).setIntegral_preimage_emb
    (EuclideanSpace.measurableEquiv (Fin 2)).measurableEmbedding]
  have he (y : EuclideanSpace ℝ (Fin 2)) :
      gaussianKernel (normalSectionChart (0 : Fin 3) (u j) 0
        (EuclideanSpace.measurableEquiv (Fin 2) y)) = Real.exp (-‖y‖^2/2) := by
    rw [RectangleCLT.gaussianKernel, vectorNormSq_normalSectionChart]
    simp only [zero_pow (by decide : (2 : ℕ)≠0), zero_add]
    change Real.exp (-vectorNormSq (WithLp.equiv 2 (Vector 2) y)/2) = _
    rw [supplementalH_vectorNormSq_equiv]
  simp_rw [he]
  exact supplementalH_planar_cone_gaussian_mass volume (by simp)
    (supplementalHFacetCone u j) (supplementalHFacetCone_measurable u j)
    (fun t ht y => supplementalHFacetCone_dilation u j t ht y)

/-- The spherical vector integral expressed in ordinary coordinates is
the corresponding unnormalized Gaussian cone moment divided by two. -/
theorem supplementalH_cone_coordinate_moment {m : ℕ} (u : Fin m → Vector 3) (k : Fin 3) :
    (∫ g in gaussianFiniteThresholdEvent Finset.univ u 0, gaussianKernel g*g k) =
      2*(∫ ω in supplementalHSphericalSection (supplementalHPolyhedralCone u),
        ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) k := by
  let C := supplementalHPolyhedralCone u
  have hi := supplementalH_gaussian_firstMoment_integrable
    (volume : Measure (EuclideanSpace ℝ (Fin 3))) (by simp)
  let L : EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ := PiLp.proj 2 (fun _ : Fin 3 => ℝ) k
  have hL := L.integral_comp_comm (hi.integrableOn (s := C))
  have hp := supplementalH_cone_gaussian_firstMoment volume (by simp) C
    (supplementalHPolyhedralCone_measurable u)
    (fun t ht x => supplementalHPolyhedralCone_dilation u t ht x)
  rw [hp, map_smul] at hL
  have he : (∫ x in C, Real.exp (-‖x‖^2/2)*x k) =
      (∫ g in gaussianFiniteThresholdEvent Finset.univ u 0, gaussianKernel g*g k) := by
    have hh := (EuclideanSpace.volume_preserving_measurableEquiv (Fin 3)).setIntegral_preimage_emb
      (EuclideanSpace.measurableEquiv (Fin 3)).measurableEmbedding
      (fun g : Vector 3 => gaussianKernel g*g k)
      (gaussianFiniteThresholdEvent Finset.univ u 0)
    convert hh using 1
    apply setIntegral_congr_fun (supplementalHPolyhedralCone_measurable u)
    intro x _
    change Real.exp (-‖x‖^2/2)*x k =
      Real.exp (-vectorNormSq (WithLp.equiv 2 (Vector 3) x)/2)*x k
    rw [supplementalH_vectorNormSq_equiv]
  change (∫ x in C, Real.exp (-‖x‖^2/2)*x k) =
    2*(∫ ω in supplementalHSphericalSection C, ω.1
      ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere) k at hL
  rw [he] at hL
  exact hL

/-- Spherical balance with outward normals. The minus sign is determined
by the actual cone inequalities `uⱼ⋅x≤0`. The number of facets is arbitrary. -/
theorem supplementalH_spherical_balance_outward {m : ℕ} (u : Fin m → Vector 3)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    (∑ j, supplementalHFacetAngle u j • (WithLp.equiv 2 (Vector 3)).symm (u j)) =
      -(2 : ℝ) • ∫ ω in supplementalHSphericalSection (supplementalHPolyhedralCone u),
        ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  apply PiLp.ext
  intro k
  have hh := gaussian_hard_polyhedron_firstMoment_kernel u 0 hu hp (Pi.single k 1)
  have hl (g : Vector 3) : faceDot (Pi.single k 1) g=g k := by
    simp [faceDot, Pi.single_apply, ite_mul]
  have hr (j : Fin m) : faceDot (u j) (Pi.single k 1)=u j k := by
    simp [faceDot, Pi.single_apply, mul_ite]
  simp only [Pi.zero_apply] at hh
  simp_rw [hl, hr] at hh
  simp_rw [supplementalH_facetKernel_eq_angle] at hh
  rw [supplementalH_cone_coordinate_moment u k] at hh
  have hs : (∑ j, supplementalHFacetAngle u j •
      (WithLp.equiv 2 (Vector 3)).symm (u j)) k =
      ∑ j, u j k*supplementalHFacetAngle u j := by
    change (PiLp.proj 2 (𝕜 := ℝ) (fun _ : Fin 3 => ℝ) k)
      (∑ j, supplementalHFacetAngle u j • (WithLp.equiv 2 (Vector 3)).symm (u j)) = _
    rw [map_sum]
    simp only [map_smul, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro j _
    change supplementalHFacetAngle u j*u j k=u j k*supplementalHFacetAngle u j
    ring
  rw [hs]
  change _ = -(2 : ℝ)*_
  linarith

/-- With inward normals the balance has the positive orientation. -/
theorem supplementalH_spherical_balance_inward {m : ℕ} (u : Fin m → Vector 3)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    (∑ j, supplementalHFacetAngle u j • -((WithLp.equiv 2 (Vector 3)).symm (u j))) =
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection (supplementalHPolyhedralCone u),
        ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere := by
  simp_rw [smul_neg, Finset.sum_neg_distrib]
  rw [supplementalH_spherical_balance_outward u hu hp, neg_smul, neg_neg]

/-- The signed angle-weighted sum is controlled by twice the actual
spherical area, uniformly in the number of facets. -/
theorem supplementalH_spherical_balance_norm_le {m : ℕ} (u : Fin m → Vector 3)
    (hu : ∀ j, vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    ‖∑ j, supplementalHFacetAngle u j • (WithLp.equiv 2 (Vector 3)).symm (u j)‖ ≤
      2*(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere.real
        (supplementalHSphericalSection (supplementalHPolyhedralCone u)) := by
  rw [supplementalH_spherical_balance_outward u hu hp, norm_smul]
  norm_num only [Real.norm_eq_abs, abs_neg,
    abs_of_nonneg (by norm_num : (0 : ℝ)≤2)]
  exact mul_le_mul_of_nonneg_left
    (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num : (0 : ℝ)≤2)

end
end RectangleCLTArxivV1
