import RectangleCLTArxivV1.SupplementalHPositiveEdgeFiber
import RectangleCLTArxivV1.SupplementalHFourthTransportSlack

/-! Positive ridge transport for the actual two-normal Gaussian sections. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem positiveRidge_coefficient_le_event_strict {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (q : ℕ) (A C : ℝ) (hC : 0≤C)
    (hRq : Integrable (fun g => fourthTransportRadius R g^q) (standardGaussian (n+1)))
    (hfiber : ∀ z, A*gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
      C*(∫ st in ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R (gaussianPairBase u b j l z))),
        fourthTransportRadius R (gaussianPairBase u b j l z+st.1 • thresholdPairBisector u j l+
          st.2 • thresholdPairDifference u j l)^q*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume)) :
    (A*gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l))*
      (standardGaussian (n+1)).real {z | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k} ≤
      C*(∫ g,(fourthPairEvent u b R j l).indicator
        (fun g => fourthTransportRadius R g^q) g ∂standardGaussian (n+1)) := by
  let F := (fourthPairEvent u b R j l).indicator (fun g => fourthTransportRadius R g^q)
  have hF : Measurable F := ((continuous_fourthTransportRadius R hRm).measurable.pow_const q).indicator
    (measurableSet_fourthPairEvent u b R hRm j l)
  have hFi : Integrable F (standardGaussian (n+1)) := hRq.indicator (measurableSet_fourthPairEvent u b R hRm j l)
  have hF0 (g) : 0≤F g := indicator_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) q) g
  let e := thresholdPairBisector u j l
  let f := thresholdPairDifference u j l
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  have he : vectorNormSq e=1 := thresholdPairBisector_unit u j l hp
  have hf : vectorNormSq f=1 := thresholdPairDifference_unit u j l hm
  have hef : faceDot e f=0 := thresholdPair_frame_orthogonal u j l hu hv
  have hprod := (integrable_gaussianPairSectionMap_iff e f he hf F hF).mpr hFi
  let V : Set (Vector (n+1)) := {z | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k}
  have hV : MeasurableSet V := by
    unfold V
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp (measurable_gaussianPairBase u b j l)) measurable_const)))
  let d := A *gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c
  have hpoint : ∀ᵐ z ∂standardGaussian (n+1),V.indicator (fun _ => d) z≤
      C*(∫ st,F (gaussianPairSectionPoint e f st.1 st.2 z) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hzV : z∈V
    · rw [indicator_of_mem hzV]
      have hb := hfiber z
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply normalPair_integral_dominates_translated_fiber
        (fun st => F (gaussianPairSectionPoint e f st.1 st.2 z))
        (fun st => fourthTransportRadius R (gaussianPairBase u b j l z+st.1 • e+st.2 • f)^q)
        hz (fun _ => hF0 _) (a,c)
        (ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
          (1/(4*fourthTransportRadius R (gaussianPairBase u b j l z))))
        (isCompact_Icc.prod isCompact_Icc).measurableSet
      intro st hst
      have hmem := (fourthPairEvent_section u b R j l hu hv hp hm z st.1 st.2).mpr ⟨hzV,hst⟩
      dsimp only [Prod.fst_add,Prod.snd_add,F]
      rw [indicator_of_mem hmem,gaussianPairSectionPoint_add_parameters e f hef]
      rfl
    · rw [indicator_of_not_mem hzV]
      exact mul_nonneg hC (integral_nonneg (fun _ => hF0 _))
  have hh := integral_mono_ae ((integrable_const d).indicator hV) (hprod.integral_prod_right.const_mul C) hpoint
  rw [integral_indicator_const _ hV,smul_eq_mul,mul_comm,integral_const_mul] at hh
  apply hh.trans_eq
  congr 1
  rw [← integral_prod_symm _ hprod]
  exact integral_gaussianPairSectionMap e f he hf F hF


theorem positiveRidge_coefficient_le_event {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (hjl : j≠l) (hreg : ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (q : ℕ) (A C : ℝ) (hC : 0≤C)
    (hRq : Integrable (fun g => fourthTransportRadius R g^q) (standardGaussian (n+1)))
    (hfiber : ∀ z, A*gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
      C*(∫ st in ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R (gaussianPairBase u b j l z))),
        fourthTransportRadius R (gaussianPairBase u b j l z+st.1 • thresholdPairBisector u j l+
          st.2 • thresholdPairDifference u j l)^q*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume)) :
    A*Real.sqrt (1-faceDot (u j) (u l)^2)*hardGaussianRidgeDensity u b j l ≤
      C*(∫ g,(fourthPairEvent u b R j l).indicator
        (fun g => fourthTransportRadius R g^q) g ∂standardGaussian (n+1)) := by
  have hσ : 0<gaussianThresholdResidualScale u j l := by
    rw [thresholdPair_residualScale_eq u j l hu hv hp hm]
    exact mul_pos (mul_pos (by norm_num) (div_pos (norm_pos_iff.mpr hp) (by norm_num)))
      (div_pos (norm_pos_iff.mpr hm) (by norm_num))
  rw [gaussianThresholdResidualScale_eq_sqrt_of_unit u j l hu hv] at hσ
  have he : A *
        Real.sqrt (1-faceDot (u j) (u l)^2)*hardGaussianRidgeDensity u b j l=
      (A *
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l))*
        (standardGaussian (n+1)).real {z | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k} := by
    rw [hardGaussianRidgeDensity_eq_strict_of_slack u b j l hjl hu hv hp hm hreg]
    field_simp [hσ.ne']
    ring
  rw [he]
  exact positiveRidge_coefficient_le_event_strict u b j l hu hv hp hm R hRm hR q A C hC hRq hfiber

end
end RectangleCLTArxivV1
