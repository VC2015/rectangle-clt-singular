import RectangleCLTArxivV1.SupplementalHRidgeTripleGrouping
import RectangleCLTArxivV1.SupplementalHTripleMass

/-! Exact raw ridge atoms and their actual codimension-three mass.
Degenerate atoms vanish by genuine zero-normal derivative proofs. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem hardGaussianRidgeThirdAtom_eq_boundaryDensity {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l k : Fin m)
    (hp : hardGaussianRidgeNonparallel u j l) (hk : k∈(Finset.univ.erase j).erase l) :
    hardGaussianRidgeThirdAtom u b j l k=
      Real.arccos (faceDot (u j) (u l))*
      (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k*
      hardGaussianPairThirdBoundaryDensity ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k) := by
  classical
  simp only [hardGaussianRidgeThirdAtom,hp,hk,if_pos]
  unfold hardGaussianRidgeNormalWeight hardGaussianPairThirdBoundaryDensity
  ring

theorem hardGaussianRidgeThirdAtom_zero_of_repeated {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l k : Fin m)
    (h : j=l ∨ k=j ∨ k=l) : hardGaussianRidgeThirdAtom u b j l k=0 := by
  classical
  rcases h with h | h | h
  · subst l
    simp [hardGaussianRidgeThirdAtom,hardGaussianRidgeNonparallel]
  · subst k
    simp [hardGaussianRidgeThirdAtom]
  · subst k
    simp [hardGaussianRidgeThirdAtom]

/-- A dependent selected third normal has genuinely zero raw boundary
atom whenever its actual double residual vanishes at nonzero slack. -/
theorem hardGaussianRidgeThirdAtom_zero_of_zero_residual {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l k : Fin m)
    (hz : hardPairResidualNormal (thresholdPairBisector u j l)
      (thresholdPairDifference u j l) (u k)=0)
    (hreg : LocalFiniteThresholdRegularity ((Finset.univ.erase j).erase l)
      (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
      (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))) :
    hardGaussianRidgeThirdAtom u b j l k=0 := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · by_cases hk : k∈(Finset.univ.erase j).erase l
    · rw [hardGaussianRidgeThirdAtom_eq_boundaryDensity u b j l k hp hk,
        hardGaussianPairThirdBoundaryDensity_zero_of_zero_residual _ u b _ _ _ _ k hk hz hreg,
        mul_zero,mul_zero]
    · simp [hardGaussianRidgeThirdAtom,hp,hk]
  · simp [hardGaussianRidgeThirdAtom,hp]

/-- The actual ridge atom is its geometric angle times genuine normal
distance times the actual common codimension-three Gaussian hard mass. -/
theorem hardGaussianRidgeThirdAtom_eq_mass {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l k : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : hardGaussianRidgeNonparallel u j l) (hk : k∈(Finset.univ.erase j).erase l)
    (hz : hardPairResidualNormal (thresholdPairBisector u j l) (thresholdPairDifference u j l) (u k)≠0)
    (hreg : LocalFiniteThresholdRegularity ((Finset.univ.erase j).erase l)
      (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
      (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))) :
    let e := thresholdPairBisector u j l
    let f := thresholdPairDifference u j l
    let a := thresholdPairFirstLevel u b j l
    let c := thresholdPairSecondLevel u b j l
    let d := hardPairResidualLevels u b e f a c k/hardPairThirdScale u e f k
    hardGaussianRidgeThirdAtom u b j l k=
      Real.arccos (faceDot (u j) (u l))*d*
        gaussianFrameHardMass (((Finset.univ.erase j).erase l).erase k) u b
          (nativeTripleFrame e f (hardPairThirdDirection u e f k)) (nativeTripleLevels a c d) := by
  rw [hardGaussianRidgeThirdAtom_eq_boundaryDensity u b j l k hp hk,
    hardGaussianPairThirdBoundaryDensity_weight_eq_mass _ u b _ _
      (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
      (thresholdPair_frame_orthogonal u j l hu hv) _ _ k hk hz hreg]
  dsimp only
  ring

end
end RectangleCLTArxivV1
