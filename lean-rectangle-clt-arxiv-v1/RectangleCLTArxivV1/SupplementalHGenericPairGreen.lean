import RectangleCLTArxivV1.SupplementalHAffineResidualRegularity
import RectangleCLTArxivV1.SupplementalHPairSectionTrace
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea

/-! The ordinary local residual regularity required by the genuine
ridge Green formula holds almost everywhere for arbitrary fixed normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def hardPairAffineCoefficients {m r : ℕ} (u : Fin m → Vector r) (j l k : Fin m) : Fin 2 → ℝ :=
  ![faceDot (u k) (thresholdPairBisector u j l)/
      ‖projectionEuclideanVector (u j)+projectionEuclideanVector (u l)‖+
    faceDot (u k) (thresholdPairDifference u j l)/
      ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖,
    faceDot (u k) (thresholdPairBisector u j l)/
      ‖projectionEuclideanVector (u j)+projectionEuclideanVector (u l)‖-
    faceDot (u k) (thresholdPairDifference u j l)/
      ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖]

theorem hardPairResidualLevels_eq_affineResidualThresholds {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)=
      affineResidualThresholds ![j,l] (fun k => hardPairAffineCoefficients u j l k) b := by
  ext k
  simp only [hardPairResidualLevels,affineResidualThresholds,Fin.sum_univ_two,
    Matrix.cons_val_zero,Matrix.cons_val_one,hardPairAffineCoefficients,
    thresholdPairFirstLevel,thresholdPairSecondLevel]
  ring

/-- Every actual double-residual ridge event is locally regular at
almost every threshold, without any rank assumption on all normals. -/
theorem ae_pairResidualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume, ∀ j l,
      LocalFiniteThresholdRegularity ((Finset.univ.erase j).erase l)
        (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
        (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) := by
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro l
  have hout : ∀ k∈(Finset.univ.erase j).erase l, ∀ i : Fin 2, k≠(![j,l] : Fin 2 → Fin m) i := by
    intro k hk i
    fin_cases i
    · exact (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    · exact (Finset.mem_erase.mp hk).1
  have h := ae_affineResidualThresholdRegularity ((Finset.univ.erase j).erase l)
    (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
    ![j,l] (fun k => hardPairAffineCoefficients u j l k) hout
  simpa only [hardPairResidualLevels_eq_affineResidualThresholds] using h

end
end RectangleCLTArxivV1
