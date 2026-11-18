import RectangleCLTArxivV1.SupplementalHNonsimpleActualMass
import RectangleCLTArxivV1.SupplementalHNonsimpleGreenSum
import RectangleCLTArxivV1.SupplementalHNonsimpleFaceConormal

/-! The literal actual-face quantities on the right of the printed
Gauss--Green identity. A ridge angle is independent of the order of its
two facets; codimension-three sums use complete active faces once. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section

def nonsimpleActualRidgeAngle {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) : ℝ :=
  (1/2 : ℝ) * ∑ p ∈ nonsimpleOrderedFacetPairs R.1,
    Real.arccos (faceDot (u p.1) (u p.2))

theorem nonsimpleActualRidgeAngle_eq_pair {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
    (j k : Fin m) (hjk : j ≠ k) (hR : R.1 = {j,k}) :
    nonsimpleActualRidgeAngle u b R = Real.arccos (faceDot (u j) (u k)) := by
  have hp : (j,k) ≠ (k,j) := by
    intro h
    exact hjk (congrArg Prod.fst h)
  unfold nonsimpleActualRidgeAngle
  rw [hR,nonsimpleOrderedFacetPairs_pair j k hjk,Finset.sum_pair hp]
  simp only [Prod.fst,Prod.snd]
  rw [faceDot_comm (u k) (u j)]
  ring

theorem nonsimpleActualRidgeAngle_nonneg {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) :
    0 ≤ nonsimpleActualRidgeAngle u b R := by
  unfold nonsimpleActualRidgeAngle
  exact mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => Real.arccos_nonneg _))

def nonsimpleActualRidgeLeading {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2) : ℝ :=
  nonsimpleActualRidgeAngle u b R *
    (‖nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b R‖^2-2) *
    nonsimpleActualGaussianMass u b R

/-- Outside a genuine ridge/face incidence the conormal is zero; on
an incidence it is the actual outward conormal within the ridge. -/
def nonsimpleActualIncidenceConormal {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3) : EuclideanSpace ℝ (Fin r) := by
  classical
  exact if h : R.1 ⊆ H.1 then nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H ⟨R,h⟩ else 0

theorem nonsimpleActualIncidenceConormal_of_incident {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3) (h : R.1 ⊆ H.1) :
    nonsimpleActualIncidenceConormal u b R H =
      nonsimpleIncidentConormal (nonsimpleNativeNormals u) b H ⟨R,h⟩ := by
  simp only [nonsimpleActualIncidenceConormal,h, dite_true]

theorem nonsimpleActualIncidenceConormal_of_not_incident {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3) (h : ¬R.1 ⊆ H.1) :
    nonsimpleActualIncidenceConormal u b R H = 0 := by
  simp only [nonsimpleActualIncidenceConormal,h, dite_false]

def nonsimpleActualConormalSum {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3) : EuclideanSpace ℝ (Fin r) :=
  ∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
    nonsimpleActualRidgeAngle u b R • nonsimpleActualIncidenceConormal u b R H

def nonsimpleActualThirdBoundary {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
    ⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
      nonsimpleActualConormalSum u b H⟫_ℝ * nonsimpleActualGaussianMass u b H

/-- The actual codimension-three boundary sum is the sum of the
individual ridge incidences. Signed terms are combined first. -/
theorem nonsimpleActualThirdBoundary_eq_ridge_incidence_sum {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) :
    nonsimpleActualThirdBoundary u b =
      ∑ R : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2,
        ∑ H : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3,
          nonsimpleActualRidgeAngle u b R *
            (⟪nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b H,
              nonsimpleActualIncidenceConormal u b R H⟫_ℝ * nonsimpleActualGaussianMass u b H) := by
  classical
  have h := nonsimple_signed_incidence_grouping (fun (_ : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 2)
    (_ : NonsimpleFaceIndex (nonsimpleNativeNormals u) b 3) => True)
    (nonsimpleActualRidgeAngle u b) (nonsimpleActualGaussianMass u b)
    (nonsimpleFaceNormalPoint (nonsimpleNativeNormals u) b) (nonsimpleActualIncidenceConormal u b)
  simpa [nonsimpleActualThirdBoundary,nonsimpleActualConormalSum] using h.symm

end
end RectangleCLTArxivV1
