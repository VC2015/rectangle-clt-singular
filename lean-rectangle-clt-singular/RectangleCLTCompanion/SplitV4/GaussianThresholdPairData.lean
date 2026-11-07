import RectangleCLTCompanion.SplitV4.GaussianThresholdTubes

/-! Shared actual bisector-frame data for the hard paired Gaussian tubes. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def thresholdPairBisector {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) : Vector r :=
  fun k => SignedSurface.bisector (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) k

def thresholdPairDifference {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) : Vector r :=
  fun k => SignedSurface.differenceDirection (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) k

def thresholdPairFirstLevel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  (b j + b l) / ‖projectionEuclideanVector (u j) + projectionEuclideanVector (u l)‖

def thresholdPairSecondLevel {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  (b j - b l) / ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖

def gaussianPairSectionPoint {r : ℕ} (e f : Vector r) (a c : ℝ) (g : Vector r) : Vector r :=
  SignedSurface.gaussianSectionPoint e a (SignedSurface.gaussianSectionPoint f c g)

def gaussianPairBase {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (g : Vector r) : Vector r :=
  gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g

theorem measurable_gaussianPairSectionPoint {r : ℕ} (e f : Vector r) (a c : ℝ) :
    Measurable (gaussianPairSectionPoint e f a c) :=
  (SignedSurface.measurable_gaussianSectionPoint e a).comp
    (SignedSurface.measurable_gaussianSectionPoint f c)

theorem measurable_gaussianPairBase {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    Measurable (gaussianPairBase u b j l) := measurable_gaussianPairSectionPoint _ _ _ _

def gaussianPairEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    Set (Vector r) :=
  {g | (∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l g) < b k) ∧
    (faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l,
      faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l) ∈
      SignedSurface.ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g)))}

theorem measurableSet_gaussianPairEvent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    MeasurableSet (gaussianPairEvent u b j l) := by
  have hx := measurable_gaussianPairBase u b j l
  have ha : Measurable (fun g => faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l) :=
    (measurable_thresholdDot _).sub_const _
  have hc : Measurable (fun g => faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l) :=
    (measurable_thresholdDot _).sub_const _
  have hε : Measurable (fun g => 1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) :=
    measurable_const.div (measurable_const.mul ((measurable_thresholdProjectionRadius u).comp hx))
  change MeasurableSet ({g | ∀ k, k ≠ j → k ≠ l → faceDot (u k) (gaussianPairBase u b j l g) < b k} ∩
    {g | ((1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) / 4 ≤
        faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l ∧
      faceDot (thresholdPairBisector u j l) g - thresholdPairFirstLevel u b j l ≤
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) / 2) ∧
      (-(1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) *
          ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 8 ≤
        faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l ∧
      faceDot (thresholdPairDifference u j l) g - thresholdPairSecondLevel u b j l ≤
        (1 / (4 * thresholdProjectionRadius u (gaussianPairBase u b j l g))) *
          ‖projectionEuclideanVector (u j) - projectionEuclideanVector (u l)‖ / 8)})
  simp only [Set.setOf_forall, Set.setOf_and]
  refine (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hx) measurable_const)))).inter ?_
  exact ((measurableSet_le (hε.div_const _) ha).inter
    (measurableSet_le ha (hε.div_const _))).inter
      ((measurableSet_le ((hε.neg.mul_const _).div_const _) hc).inter
        (measurableSet_le hc ((hε.mul_const _).div_const _)))

end
end RectangleCLT.Companion.SplitV4
