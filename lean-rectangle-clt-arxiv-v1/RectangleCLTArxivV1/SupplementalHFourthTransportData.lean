import RectangleCLTArxivV1.SupplementalHFourthFiberBounds
import RectangleCLTArxivV1.SupplementalHResidualPairMass
import RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes

/-! Actual adaptive facet and ridge events for an arbitrary common radius.
The same radius is evaluated at the base and at the ambient output. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false

def fourthTransportRadius {r : ℕ} (R : EuclideanSpace ℝ (Fin r) → ℝ) (x : Vector r) : ℝ :=
  R (projectionEuclideanVector x)

theorem continuous_fourthTransportRadius {r : ℕ} (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (hR : Continuous R) : Continuous (fourthTransportRadius R) :=
  hR.comp (PiLp.continuous_equiv_symm 2 _)

def fourthFacetEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (j : Fin m) : Set (Vector r) :=
  {g | (∀ l, l≠j → faceDot (u l) (gaussianFacetBase u b j g)<b l) ∧
    0<faceDot (u j) g-b j ∧
    faceDot (u j) g-b j≤1/(4*fourthTransportRadius R (gaussianFacetBase u b j g))}

def fourthPairEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (j l : Fin m) : Set (Vector r) :=
  {g | (∀ k, k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)<b k) ∧
    (faceDot (thresholdPairBisector u j l) g-thresholdPairFirstLevel u b j l,
      faceDot (thresholdPairDifference u j l) g-thresholdPairSecondLevel u b j l)∈
      ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R (gaussianPairBase u b j l g)))}

theorem measurableSet_fourthFacetEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R) (j : Fin m) :
    MeasurableSet (fourthFacetEvent u b R j) := by
  have hx := measurable_gaussianSectionPoint (u j) (b j)
  have ht : Measurable (fun g => faceDot (u j) g-b j) := (measurable_thresholdDot _).sub_const _
  have hr : Measurable (fun g => 1/(4*fourthTransportRadius R (gaussianFacetBase u b j g))) :=
    measurable_const.div (measurable_const.mul ((continuous_fourthTransportRadius R hR).measurable.comp hx))
  unfold fourthFacetEvent
  simp only [setOf_and,setOf_forall]
  exact (MeasurableSet.iInter (fun l => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hx) measurable_const))).inter
      ((measurableSet_lt measurable_const ht).inter (measurableSet_le ht hr))

theorem measurableSet_fourthPairEvent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R) (j l : Fin m) :
    MeasurableSet (fourthPairEvent u b R j l) := by
  have hx := measurable_gaussianPairBase u b j l
  have ha : Measurable (fun g => faceDot (thresholdPairBisector u j l) g-thresholdPairFirstLevel u b j l) :=
    (measurable_thresholdDot _).sub_const _
  have hc : Measurable (fun g => faceDot (thresholdPairDifference u j l) g-thresholdPairSecondLevel u b j l) :=
    (measurable_thresholdDot _).sub_const _
  have hε : Measurable (fun g => 1/(4*fourthTransportRadius R (gaussianPairBase u b j l g))) :=
    measurable_const.div (measurable_const.mul ((continuous_fourthTransportRadius R hR).measurable.comp hx))
  change MeasurableSet ({g | ∀ k, k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l g)<b k} ∩
    {g | ((1/(4*fourthTransportRadius R (gaussianPairBase u b j l g)))/4≤
        faceDot (thresholdPairBisector u j l) g-thresholdPairFirstLevel u b j l ∧
      faceDot (thresholdPairBisector u j l) g-thresholdPairFirstLevel u b j l≤
        (1/(4*fourthTransportRadius R (gaussianPairBase u b j l g)))/2) ∧
      (-(1/(4*fourthTransportRadius R (gaussianPairBase u b j l g)))*
          ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖/8≤
        faceDot (thresholdPairDifference u j l) g-thresholdPairSecondLevel u b j l ∧
      faceDot (thresholdPairDifference u j l) g-thresholdPairSecondLevel u b j l≤
        (1/(4*fourthTransportRadius R (gaussianPairBase u b j l g)))*
          ‖projectionEuclideanVector (u j)-projectionEuclideanVector (u l)‖/8)})
  simp only [setOf_forall,setOf_and]
  refine (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hx) measurable_const)))).inter ?_
  exact ((measurableSet_le (hε.div_const _) ha).inter (measurableSet_le ha (hε.div_const _))).inter
    ((measurableSet_le ((hε.neg.mul_const _).div_const _) hc).inter
      (measurableSet_le hc ((hε.mul_const _).div_const _)))

theorem fourthFacetEvent_section {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (j : Fin m) (hu : vectorNormSq (u j)=1)
    (z : Vector r) (t : ℝ) : gaussianSectionPoint (u j) t z∈fourthFacetEvent u b R j ↔
      (∀ l, l≠j → faceDot (u l) (gaussianFacetBase u b j z)<b l) ∧
      0<t-b j ∧ t-b j≤1/(4*fourthTransportRadius R (gaussianFacetBase u b j z)) := by
  simp only [fourthFacetEvent,mem_setOf_eq,gaussianFacetBase,gaussianSectionPoint_comp (u j) hu,
    gaussianSectionPoint_on_hyperplane (u j) t hu]

/-- Ordinary local slack is sufficient to replace inactive closed faces
by strict ones; zero projected normals are included. -/
theorem gaussianThresholdSectionProbability_eq_strict_of_slack {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m) (t : ℝ)
    (hreg : ∀ l∈Finset.univ.erase j, gaussianNormalProjection (u j) (u l)≠0 ∨
      b l-t*faceDot (u l) (u j)≠0) :
    gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) t=
      (standardGaussian r).real {z | ∀ l, l≠j → faceDot (u l) (gaussianSectionPoint (u j) t z)<b l} := by
  classical
  have hn := gaussianFiniteThreshold_ae_no_boundary_of_slack (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l)) (fun l => b l-t*faceDot (u l) (u j)) hreg
  rw [gaussianThresholdSectionProbability_eq_section]
  apply congrArg ENNReal.toReal
  apply measure_congr
  filter_upwards [hn] with z hz
  simp only [mem_setOf_eq,Finset.mem_erase,Finset.mem_univ,and_true]
  apply propext
  apply forall_congr'
  intro l
  by_cases hlj : l=j
  · simp [hlj]
  · have hne := hz l (Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩)
    rw [gaussianSectionPoint_faceDot]
    constructor <;> intro h hlj'
    · have hle := h hlj'
      exact lt_of_le_of_ne hle (by intro he; apply hne; linarith)
    · exact (h hlj').le

end
end RectangleCLTArxivV1
