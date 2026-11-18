import RectangleCLTArxivV1.SupplementalHTrihedralResidualConormal
import RectangleCLTArxivV1.SupplementalHTripleFiber

/-! The actual third-normal residual contributions are grouped through
trihedral spherical balance before their absolute value is taken. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Exact signed grouping of the three actual normalized residual
conormals, with ordinary endpoint angles on the actual normal cone. -/
theorem trihedral_residual_boundary_pairing (e : Basis (Fin 3) ℝ E3)
    (hunit : ∀ i, ‖e i‖=1) (z : E3) :
    (∑ i, trihedralEdgeAngle e i*⟪trihedralResidualUnitNormal e i,z⟫_ℝ)=
      ⟪z,(2:ℝ) • ∫ ω in supplementalHSphericalSection (trihedralGeneratedCone e),
        ω.1 ∂(volume : Measure E3).toSphere⟫_ℝ := by
  rw [←trihedral_spherical_balance e hunit,inner_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [trihedralResidualUnitNormal_eq_inward e hunit i,inner_smul_right]
  congr 1
  exact real_inner_comm _ _

/-- The full actual signed trihedral third-boundary coefficient is paid
by one conical R4 normal fiber, without an edge-count factor. -/
theorem adaptive_trihedral_boundary_fourth_bound
    {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (e : Basis (Fin 3) ℝ E3) (hunit : ∀ i, ‖e i‖=1)
    (L : E3 →ₗᵢ[ℝ] F) (R : F → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖) (x : F) (z : E3) (hz : ‖z‖≤R x) :
    abs (∑ i, trihedralEdgeAngle e i*⟪trihedralResidualUnitNormal e i,z⟫_ℝ)*gaussianKernel z≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ y in trihedralGeneratedCone e∩Metric.ball (0:E3) (1/(4*R x)),
        R (x+L y)^4*gaussianKernel (z+y)) := by
  have hC : MeasurableSet (trihedralGeneratedCone e) := by
    rw [←supplementalHPolyhedralCone_trihedral e]
    exact supplementalHPolyhedralCone_measurable _
  have hcone : ∀ t : ℝ, 0<t → ∀ y : E3, t • y∈trihedralGeneratedCone e ↔ y∈trihedralGeneratedCone e := by
    intro t ht y
    rw [←supplementalHPolyhedralCone_trihedral e]
    exact supplementalHPolyhedralCone_dilation _ t ht y
  rw [trihedral_residual_boundary_pairing e hunit z]
  exact adaptive_cone_spherical_vector_fourth_bound volume (by simp) (trihedralGeneratedCone e) hC hcone
    L R hRm hR hRadd x z hz

end
end RectangleCLTArxivV1
