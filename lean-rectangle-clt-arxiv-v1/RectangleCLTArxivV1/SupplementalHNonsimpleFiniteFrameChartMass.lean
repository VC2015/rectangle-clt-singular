import RectangleCLTArxivV1.SupplementalHNonsimpleFaceChartProduct
import RectangleCLTArxivV1.SupplementalHNonsimpleFiniteFrameChartGeometry
import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass

/-! The Gaussian mass of an actual finite-codimension face is its ambient
Gaussian density integrated over a genuine orthonormal tangent chart.
The surface convention is Euclidean orthonormal chart volume. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
variable {n m q : ℕ}

theorem nonsimpleFiniteFrameSection_measurable
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (a : Vector q) :
    Measurable (fun g : Vector (n+q) => WithLp.equiv 2 (Vector (n+q))
      (gaussianFrameSectionPoint v a ((WithLp.equiv 2 (Vector (n+q))).symm g))) := by
  have hc : Continuous (gaussianFrameSectionPoint v a) := by
    unfold gaussianFrameSectionPoint gaussianFrameProjection
    fun_prop
  exact (EuclideanSpace.measurableEquiv (Fin (n+q))).measurable.comp
    (hc.measurable.comp (EuclideanSpace.measurableEquiv (Fin (n+q))).symm.measurable)

/-- The actual projected ambient Gaussian law is exactly the Gaussian
law on the proper tangent coordinates. -/
theorem nonsimpleFiniteFrameSection_chart_gaussian_map
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) :
    (standardGaussian (n+q)).map (fun g => WithLp.equiv 2 (Vector (n+q))
      (gaussianFrameSectionPoint v a ((WithLp.equiv 2 (Vector (n+q))).symm g))) =
      (standardGaussian n).map (nonsimpleFiniteFrameChart v hv a) := by
  apply nonsimpleChart_gaussian_map_of_rotated_prefix
    (nonsimpleFiniteFrameChartBasis v hv).repr.symm _ _
    (nonsimpleFiniteFrameSection_measurable v a) (nonsimpleFiniteFrameChart_measurable v hv a)
  intro g
  exact nonsimpleFiniteFrameChart_rotated_section v hv a g

theorem nonsimpleFiniteFrameChart_density
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (y : Vector n) :
    standardGaussianDensity (n+q) (nonsimpleFiniteFrameChart v hv a y) =
      standardGaussianDensity n y * standardGaussianDensity q a := by
  unfold nonsimpleFiniteFrameChart
  rw [nonsimpleChartDensity_rotation,nonsimpleChartDensity_append]

/-- Exact ambient Gaussian density integral on a proper tangent chart.
Every original inequality in `s` is retained in the section event. -/
theorem gaussianFrameHardMass_eq_finiteTangentChart_integral
    (s : Finset (Fin m)) (u : Fin m → Vector (n+q)) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) :
    gaussianFrameHardMass s u b v a =
      ∫ y : Vector n, (gaussianFiniteThresholdEvent s u b).indicator
        (standardGaussianDensity (n+q)) (nonsimpleFiniteFrameChart v hv a y) := by
  let P := gaussianFiniteThresholdEvent s u b
  let C := nonsimpleFiniteFrameChart v hv a
  have hP : MeasurableSet P := measurableSet_gaussianFiniteThresholdEvent s u b
  have hC : Measurable C := nonsimpleFiniteFrameChart_measurable v hv a
  have hp := congrArg (fun μ : Measure (Vector (n+q)) => (μ P).toReal)
    (nonsimpleFiniteFrameSection_chart_gaussian_map v hv a)
  dsimp only at hp
  rw [Measure.map_apply (nonsimpleFiniteFrameSection_measurable v a) hP,
    Measure.map_apply hC hP] at hp
  unfold gaussianFrameHardMass
  change standardGaussianDensity q a *
    ((standardGaussian (n+q)) ((fun g => WithLp.equiv 2 (Vector (n+q))
      (gaussianFrameSectionPoint v a ((WithLp.equiv 2 (Vector (n+q))).symm g))) ⁻¹' P)).toReal = _
  rw [hp]
  change standardGaussianDensity q a * (standardGaussian n).real (C ⁻¹' P)=_
  rw [←integral_indicator_one (hC hP),standardGaussian_integral_density_mul,
    ←integral_const_mul]
  apply integral_congr_ae
  filter_upwards [] with y
  change standardGaussianDensity q a *
    (standardGaussianDensity n y * (C ⁻¹' P).indicator (fun _ => (1:ℝ)) y)=
      P.indicator (standardGaussianDensity (n+q)) (C y)
  by_cases hy : C y ∈ P
  · simp only [Set.indicator_of_mem hy,
      Set.indicator_of_mem (show y ∈ C ⁻¹' P from hy),mul_one]
    exact (mul_comm _ _).trans (nonsimpleFiniteFrameChart_density v hv a y).symm
  · simp only [Set.indicator_of_not_mem hy,
      Set.indicator_of_not_mem (show y ∉ C ⁻¹' P from hy),mul_zero]

theorem nonsimpleFiniteFrameChart_density_integrable
    (s : Finset (Fin m)) (u : Fin m → Vector (n+q)) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) :
    Integrable (fun y : Vector n => (gaussianFiniteThresholdEvent s u b).indicator
      (standardGaussianDensity (n+q)) (nonsimpleFiniteFrameChart v hv a y)) := by
  let P := gaussianFiniteThresholdEvent s u b
  let C := nonsimpleFiniteFrameChart v hv a
  have hP : MeasurableSet (C ⁻¹' P) :=
    (nonsimpleFiniteFrameChart_measurable v hv a) (measurableSet_gaussianFiniteThresholdEvent s u b)
  have hi := (standardGaussian_integrable_density_mul_iff
    ((C ⁻¹' P).indicator (fun _ => (1:ℝ)))).mp
      ((integrable_const (1:ℝ)).indicator hP)
  have hc := hi.const_mul (standardGaussianDensity q a)
  apply hc.congr
  filter_upwards [] with y
  change standardGaussianDensity q a *
    (standardGaussianDensity n y * (C ⁻¹' P).indicator (fun _ => (1:ℝ)) y)=
      P.indicator (standardGaussianDensity (n+q)) (C y)
  by_cases hy : C y ∈ P
  · simp only [Set.indicator_of_mem hy,
      Set.indicator_of_mem (show y ∈ C ⁻¹' P from hy),mul_one]
    exact (mul_comm _ _).trans (nonsimpleFiniteFrameChart_density v hv a y).symm
  · simp only [Set.indicator_of_not_mem hy,
      Set.indicator_of_not_mem (show y ∉ C ⁻¹' P from hy),mul_zero]

theorem nonsimpleFiniteFrameChart_supporting_level
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin (n+q))) (hv : Orthonormal ℝ v)
    (a : Vector q) (j : Fin m)
    (hj : (WithLp.equiv 2 (Vector (n+q))).symm (u j) ∈ Submodule.span ℝ (Set.range v))
    (hlevel : ⟪(WithLp.equiv 2 (Vector (n+q))).symm (u j), ∑ i,a i • v i⟫_ℝ=b j)
    (y : Vector n) : faceDot (u j) (nonsimpleFiniteFrameChart v hv a y)=b j := by
  have hs := nonsimpleFiniteFrameChart_rotated_section v hv a (Fin.append y a)
  simp only [Fin.append_left] at hs
  rw [←hs]
  exact gaussianFrameSectionPoint_supporting_level u b v hv a j hj hlevel _

/-- Canonical orthonormal tangent coordinates for the affine support of
an actual finite-codimension face, including nonsimple faces. -/
def nonsimpleActualFiniteFaceChart (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) : Vector n → Vector (n+q) :=
  nonsimpleFiniteFrameChart (nonsimpleFaceFrame (nonsimpleNativeNormals u) b H)
    (nonsimpleFaceFrame_orthonormal _ _ H)
    (fun i => ⟪nonsimpleFaceFrame (nonsimpleNativeNormals u) b H i,
      nonsimpleFaceRepresentative (nonsimpleNativeNormals u) b H⟫_ℝ)

theorem nonsimpleActualFiniteFaceChart_measurable (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    Measurable (nonsimpleActualFiniteFaceChart u b H) :=
  nonsimpleFiniteFrameChart_measurable _ _ _

def nonsimpleActualFiniteFaceEuclideanChart (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (y : EuclideanSpace ℝ (Fin n)) : EuclideanSpace ℝ (Fin (n+q)) :=
  (WithLp.equiv 2 (Vector (n+q))).symm
    (nonsimpleActualFiniteFaceChart u b H (WithLp.equiv 2 (Vector n) y))

theorem nonsimpleActualFiniteFaceEuclideanChart_isometry
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    Isometry (nonsimpleActualFiniteFaceEuclideanChart u b H) :=
  nonsimpleFiniteFrameEuclideanChart_isometry _ _ _

theorem nonsimpleActualFiniteFaceEuclideanChart_covers_closedFace
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (x : EuclideanSpace ℝ (Fin (n+q)))
    (hx : x ∈ nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1) :
    x ∈ Set.range (nonsimpleActualFiniteFaceEuclideanChart u b H) := by
  change x ∈ Set.range (nonsimpleFiniteFrameEuclideanChart _ _ _)
  rw [nonsimpleFiniteFrameEuclideanChart_range]
  intro i
  let S := nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1
  let v := nonsimpleFaceFrame (nonsimpleNativeNormals u) b H
  have hi : v i ∈ S := by
    change nonsimpleFaceFrame (nonsimpleNativeNormals u) b H i ∈
      nonsimpleFaceNormalSpace (nonsimpleNativeNormals u) H.1
    rw [←nonsimpleFaceFrame_span]
    exact Submodule.subset_span ⟨i,rfl⟩
  have hp := nonsimpleFaceNormalPoint_eq_of_closedFace (nonsimpleNativeNormals u) b H x hx
  calc
    ⟪v i,x⟫_ℝ = ⟪v i,(S.orthogonalProjection x : EuclideanSpace ℝ (Fin (n+q)))⟫_ℝ :=
      (Submodule.inner_orthogonalProjection_eq_of_mem_left (K := S) ⟨v i,hi⟩ x).symm
    _ = ⟪v i,nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H⟫_ℝ := by rw [hp]
    _ = ⟪v i,nonsimpleFaceRepresentative (nonsimpleNativeNormals u) b H⟫_ℝ :=
      Submodule.inner_orthogonalProjection_eq_of_mem_left (K := S) ⟨v i,hi⟩ _

theorem nonsimpleActualFiniteFaceChart_active_level (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q)
    (j : Fin m) (hj : j ∈ H.1) (y : Vector n) :
    faceDot (u j) (nonsimpleActualFiniteFaceChart u b H y)=b j := by
  apply nonsimpleFiniteFrameChart_supporting_level u b _ _ _ j
  · change nonsimpleNativeNormals u j ∈ _
    rw [nonsimpleFaceFrame_span]
    exact nonsimple_normal_mem _ _ _ hj
  · change ⟪nonsimpleNativeNormals u j,_⟫_ℝ=b j
    rw [←nonsimpleFaceNormalPoint_eq_frameProjection]
    exact nonsimpleFaceNormalPoint_levels _ _ H j hj

theorem nonsimpleActualFiniteFaceChart_mem_closedFace_iff
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) (y : Vector n) :
    (WithLp.equiv 2 (Vector (n+q))).symm (nonsimpleActualFiniteFaceChart u b H y) ∈
      nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1 ↔
      nonsimpleActualFiniteFaceChart u b H y ∈ gaussianFiniteThresholdEvent Finset.univ u b := by
  constructor
  · intro hx
    intro j _
    simpa only [nonsimpleNativeNormals,←faceDot_eq_euclidean_inner] using hx.1 j
  · intro hx
    refine ⟨?_,?_⟩
    · intro j
      simpa only [nonsimpleNativeNormals,←faceDot_eq_euclidean_inner] using hx j (Finset.mem_univ j)
    · intro j hj
      simpa only [nonsimpleNativeNormals,←faceDot_eq_euclidean_inner] using
        nonsimpleActualFiniteFaceChart_active_level u b H j hj y

/-- The canonical `rho_H` is precisely the ambient Gaussian density
surface integral in a proper orthonormal tangent chart, with the actual
closed face as its integration domain. -/
theorem nonsimpleActualGaussianMass_eq_closedFace_finiteChart_integral
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    nonsimpleActualGaussianMass u b H =
      ∫ y : Vector n, (nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1).indicator
        (fun x => standardGaussianDensity (n+q) (WithLp.equiv 2 (Vector (n+q)) x))
        ((WithLp.equiv 2 (Vector (n+q))).symm (nonsimpleActualFiniteFaceChart u b H y)) := by
  unfold nonsimpleActualGaussianMass nonsimpleFaceGaussianMass
  rw [gaussianFrameHardMass_eq_finiteTangentChart_integral _ _ _ _
    (nonsimpleFaceFrame_orthonormal _ _ H)]
  apply integral_congr_ae
  filter_upwards [] with y
  change (gaussianFiniteThresholdEvent Finset.univ u b).indicator _
    (nonsimpleActualFiniteFaceChart u b H y)=_
  by_cases hy : nonsimpleActualFiniteFaceChart u b H y ∈ gaussianFiniteThresholdEvent Finset.univ u b
  · rw [Set.indicator_of_mem hy,
      Set.indicator_of_mem ((nonsimpleActualFiniteFaceChart_mem_closedFace_iff u b H y).mpr hy)]
    rfl
  · rw [Set.indicator_of_not_mem hy,Set.indicator_of_not_mem
      (fun hh => hy ((nonsimpleActualFiniteFaceChart_mem_closedFace_iff u b H y).mp hh))]

theorem nonsimpleActualFiniteFaceChart_surface_integrable
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    Integrable (fun y : Vector n =>
      (nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1).indicator
        (fun x => standardGaussianDensity (n+q) (WithLp.equiv 2 (Vector (n+q)) x))
        ((WithLp.equiv 2 (Vector (n+q))).symm (nonsimpleActualFiniteFaceChart u b H y))) := by
  apply (nonsimpleFiniteFrameChart_density_integrable Finset.univ u b
    (nonsimpleFaceFrame (nonsimpleNativeNormals u) b H)
    (nonsimpleFaceFrame_orthonormal _ _ H) _).congr
  filter_upwards [] with y
  change (gaussianFiniteThresholdEvent Finset.univ u b).indicator _
    (nonsimpleActualFiniteFaceChart u b H y)=_
  by_cases hy : nonsimpleActualFiniteFaceChart u b H y ∈ gaussianFiniteThresholdEvent Finset.univ u b
  · rw [Set.indicator_of_mem hy,
      Set.indicator_of_mem ((nonsimpleActualFiniteFaceChart_mem_closedFace_iff u b H y).mpr hy)]
    rfl
  · rw [Set.indicator_of_not_mem hy,Set.indicator_of_not_mem
      (fun hh => hy ((nonsimpleActualFiniteFaceChart_mem_closedFace_iff u b H y).mp hh))]

theorem nonsimpleActualFiniteFaceEuclideanChart_surface_integrable
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    Integrable (fun y : EuclideanSpace ℝ (Fin n) =>
      (nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1).indicator
        (fun x => standardGaussianDensity (n+q) (WithLp.equiv 2 (Vector (n+q)) x))
        (nonsimpleActualFiniteFaceEuclideanChart u b H y)) :=
  ((EuclideanSpace.volume_preserving_measurableEquiv (Fin n)).integrable_comp_emb
    (EuclideanSpace.measurableEquiv (Fin n)).measurableEmbedding).mpr
      (nonsimpleActualFiniteFaceChart_surface_integrable u b H)

/-- The same surface integral in Euclidean tangent coordinates. Its
chart is an affine isometry onto the support plane and covers the whole
actual closed face. No Hausdorff-measure normalization is introduced. -/
theorem nonsimpleActualGaussianMass_eq_finite_surface_integral
    (u : Fin m → Vector (n+q)) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b q) :
    nonsimpleActualGaussianMass u b H =
      ∫ y : EuclideanSpace ℝ (Fin n),
        (nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1).indicator
          (fun x => standardGaussianDensity (n+q) (WithLp.equiv 2 (Vector (n+q)) x))
          (nonsimpleActualFiniteFaceEuclideanChart u b H y) := by
  rw [nonsimpleActualGaussianMass_eq_closedFace_finiteChart_integral]
  exact ((EuclideanSpace.volume_preserving_measurableEquiv (Fin n)).integral_comp'
    (fun y : Vector n =>
      (nonsimpleClosedFace (nonsimpleNativeNormals u) b H.1).indicator
        (fun x => standardGaussianDensity (n+q) (WithLp.equiv 2 (Vector (n+q)) x))
        ((WithLp.equiv 2 (Vector (n+q))).symm (nonsimpleActualFiniteFaceChart u b H y)))).symm

/-- In particular, the printed ridge mass `rho_E` is the actual
ambient Gaussian density integral over its orthonormal tangent chart. -/
theorem nonsimpleActualGaussianMass_ridge_surface_integral
    (u : Fin m → Vector (n+2)) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) :
    nonsimpleActualGaussianMass u b R =
      ∫ y : EuclideanSpace ℝ (Fin n),
        (nonsimpleClosedFace (nonsimpleNativeNormals u) b R.1).indicator
          (fun x => standardGaussianDensity (n+2) (WithLp.equiv 2 (Vector (n+2)) x))
          (nonsimpleActualFiniteFaceEuclideanChart u b R y) :=
  nonsimpleActualGaussianMass_eq_finite_surface_integral u b R

end
end RectangleCLTArxivV1
