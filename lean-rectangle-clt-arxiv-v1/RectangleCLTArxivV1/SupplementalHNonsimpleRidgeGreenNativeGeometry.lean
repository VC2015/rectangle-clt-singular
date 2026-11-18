import RectangleCLTArxivV1.SupplementalHActualFacetGeometry
import RectangleCLTArxivV1.SupplementalHPairSectionTrace
import RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry

/-! Actual native pair-frame geometry at fixed supporting levels. The
ordinary residual no-zero-boundary condition follows from genuine original
facet witnesses, including dependent families and nonsimple thresholds. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Supporting levels in the original pair give exactly the native
bisector and difference coordinates, by the two original-normal expansions. -/
theorem thresholdPair_frame_levels_of_support {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (x : Vector r)
    (hp : projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0)
    (hm : projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0)
    (hxj : faceDot (u j) x = b j) (hxl : faceDot (u l) x = b l) :
    faceDot (thresholdPairBisector u j l) x = thresholdPairFirstLevel u b j l ∧
      faceDot (thresholdPairDifference u j l) x = thresholdPairSecondLevel u b j l := by
  have hleft := congrArg (fun v : Vector r => faceDot v x)
    (thresholdPair_left_expansion u j l hp hm)
  dsimp only at hleft
  rw [hxj, faceDot_affine_combination] at hleft
  have hright := congrArg (fun v : Vector r => faceDot v x)
    (thresholdPair_right_expansion u j l hp hm)
  dsimp only at hright
  rw [hxl, threshold_faceDot_sub_left, threshold_faceDot_smul_left,
    threshold_faceDot_smul_left] at hright
  constructor
  · unfold thresholdPairFirstLevel
    apply (eq_div_iff (norm_ne_zero_iff.mpr hp)).mpr
    linear_combination -hleft - hright
  · unfold thresholdPairSecondLevel
    apply (eq_div_iff (norm_ne_zero_iff.mpr hm)).mpr
    linear_combination -hleft + hright

/-- The bisector is the actual inverse-length normalized original sum. -/
private theorem native_pair_bisector_expansion {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    thresholdPairBisector u j l =
      ‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖⁻¹ •
        (u j + u l) := by
  funext k
  rfl

private theorem native_pair_difference_expansion {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m) :
    thresholdPairDifference u j l =
      ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖⁻¹ •
        (u j - u l) := by
  funext k
  rfl

/-- A vanishing residual normal and level would be a consistent affine
dependency of three distinct original actual facets, which is impossible.
Only original unit norms are used to establish pair-frame orthogonality. -/
theorem actualFacet_pairResidual_nonzero_or_level {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b)
    (hu : ∀ i, vectorNormSq (u i) = 1) (j l : Fin m) (hjl : j ≠ l)
    (k : Fin m) (hk : k ∈ (Finset.univ.erase j).erase l) :
    hardPairResidualNormals u (thresholdPairBisector u j l)
        (thresholdPairDifference u j l) k ≠ 0 ∨
      hardPairResidualLevels u b (thresholdPairBisector u j l)
        (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k ≠ 0 := by
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let p := ‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖
  let q := ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖
  let A := faceDot (u k) e
  let B := faceDot (u k) f
  let a := A * p⁻¹ + B * q⁻¹
  let c := A * p⁻¹ - B * q⁻¹
  have hef : faceDot e f = 0 := thresholdPair_frame_orthogonal u j l (hu j) (hu l)
  by_cases hz : hardPairResidualNormals u e f k = 0
  · right
    intro hb
    have hdot : faceDot (gaussianNormalProjection e (u k)) f = B := by
      rw [gaussianNormalProjection, threshold_faceDot_sub_left,
        threshold_faceDot_smul_left, hef, mul_zero, sub_zero]
    have hnormal_frame : u k = A • e + B • f := by
      change gaussianNormalProjection e (u k) -
        faceDot (gaussianNormalProjection e (u k)) f • f = 0 at hz
      rw [hdot] at hz
      change u k - A • e - B • f = 0 at hz
      calc
        u k = (u k - A • e - B • f) + (A • e + B • f) := by module
        _ = A • e + B • f := by rw [hz, zero_add]
    have hnormal : u k = a • u j + c • u l := by
      rw [hnormal_frame]
      dsimp only [e, f]
      rw [native_pair_bisector_expansion, native_pair_difference_expansion]
      dsimp only [a, c, p, q]
      module
    have hkj : k ≠ j := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    have hkl : k ≠ l := (Finset.mem_erase.mp hk).1
    apply actualFacet_triple_affine_inconsistent u b hinterior hwitness j l k hjl hkj hkl a c hnormal
    change b k - thresholdPairFirstLevel u b j l * A -
      thresholdPairSecondLevel u b j l * B = 0 at hb
    unfold thresholdPairFirstLevel thresholdPairSecondLevel at hb
    dsimp only [a, c, p, q]
    simp only [div_eq_mul_inv] at hb
    linear_combination hb
  · exact Or.inl hz

/-- Distinct actual facets with a common supporting point have a genuine
bisector/difference frame. No unit normalization is needed for this fact. -/
theorem actualFacet_pair_support_nonparallel {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b)
    (j l : Fin m) (hjl : j ≠ l) (x : Vector r)
    (hxj : faceDot (u j) x = b j) (hxl : faceDot (u l) x = b l) :
    projectionEuclideanVector (u j) + projectionEuclideanVector (u l) ≠ 0 ∧
      projectionEuclideanVector (u j) - projectionEuclideanVector (u l) ≠ 0 := by
  have hbad (a : ℝ) (hn : u l = a • u j) : False := by
    apply actualFacet_pair_affine_inconsistent u b hinterior hwitness j l (Ne.symm hjl) a hn
    rw [← hxl, hn, threshold_faceDot_smul_left, hxj]
  constructor
  · intro hz
    apply hbad (-1)
    funext k
    have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) hz
    change u j k + u l k = 0 at hk
    change u l k = (-1) * u j k
    linarith
  · intro hz
    apply hbad 1
    funext k
    have hk := congrArg (fun z : EuclideanSpace ℝ (Fin r) => z k) hz
    change u j k - u l k = 0 at hk
    change u l k = 1 * u j k
    linarith

end
end RectangleCLTArxivV1
