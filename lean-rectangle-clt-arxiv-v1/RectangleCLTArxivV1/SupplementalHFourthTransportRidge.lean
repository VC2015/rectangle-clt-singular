import RectangleCLTArxivV1.SupplementalHFourthTransportData

/-! Actual fourth-radius two-normal Gaussian transport. The paired Green
coefficient is retained before taking its absolute value. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def fourthRidgeNormalPoint {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) :
    EuclideanSpace ℝ (Fin r) :=
  thresholdPairFirstLevel u b j l • projectionEuclideanVector (thresholdPairBisector u j l)+
    thresholdPairSecondLevel u b j l • projectionEuclideanVector (thresholdPairDifference u j l)

theorem fourthRidge_fiber_coefficient_bound {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (x : Vector r)
    (hz : ‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R x) :
    |supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
      (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)≤
    (8192*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle
      (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^4*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume) := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := bisector U V
  let f := differenceDirection U V
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  let X := projectionEuclideanVector x
  have hU : ‖U‖=1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖=1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖=1 := norm_bisector _ _ hp
  have hf : ‖f‖=1 := norm_differenceDirection _ _ hm
  have hef : ⟪e,f⟫_ℝ=0 := inner_bisector_differenceDirection _ _ (hU.trans hV.symm)
  have hpoint : fourthRidgeNormalPoint u b j l=a • e+c • f := by
    rw [fourthRidgeNormalPoint,thresholdPairBisector_euclidean,thresholdPairDifference_euclidean]
  have hnorm (s t : ℝ) : ‖s • e+t • f‖^2=s^2+t^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,he,hf,mul_one,sq_abs,inner_smul_left,
      inner_smul_right,conj_trivial,hef,mul_zero,zero_mul,add_zero]
  have hh := adaptive_weighted_ridge_pair_fourth_bound R hRm hR hRadd X U V
    (fourthRidgeNormalPoint u b j l) hU hV hp hm hz
  let d := (Real.sqrt (2*Real.pi))⁻¹^2
  have hd : 0≤d := by dsimp [d]; positivity
  have hpdf (s t : ℝ) : gaussianPDFReal 0 1 s*gaussianPDFReal 0 1 t=d*RectangleCLT.Companion.SignedSurface.gaussianKernel (s • e+t • f) := by
    rw [RectangleCLT.Companion.SignedSurface.gaussianKernel,hnorm]
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,d]
    rw [mul_mul_mul_comm,← Real.exp_add]
    congr 1
    · exact (pow_two _).symm
    · congr 1
      ring
  have hint : (∫ st in ridgeRectangle U V (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^4*
        gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2) ∂(volume : Measure ℝ).prod volume)=
      d*(∫ st in ridgeRectangle U V (1/(4*R X)),
        R (X+ridgeDisplacement U V st)^4*RectangleCLT.Companion.SignedSurface.gaussianKernel (fourthRidgeNormalPoint u b j l+ridgeDisplacement U V st)
          ∂(volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun st => by
      dsimp only
      have hplane : fourthRidgeNormalPoint u b j l+ridgeDisplacement U V st=(a+st.1) • e+(c+st.2) • f := by
        rw [hpoint]
        dsimp only [ridgeDisplacement,e,f]
        module
      rw [hplane]
      have hr : fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)=
          R (X+ridgeDisplacement U V st) := by
        congr 1
        ext k
        change (x k+st.1*e k)+st.2*f k=x k+(st.1*e k+st.2*f k)
        ring
      rw [hr,show R (X+ridgeDisplacement U V st)^4*gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2)=
        R (X+ridgeDisplacement U V st)^4*(gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2)) by ring,hpdf]
      ring)
  change _≤(8192*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle U V (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^4*
        gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2) ∂(volume : Measure ℝ).prod volume)
  rw [hint,show |supplementalHWeightedRidgeCoefficient U V (fourthRidgeNormalPoint u b j l)| *
    gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c=
    |supplementalHWeightedRidgeCoefficient U V (fourthRidgeNormalPoint u b j l)| *
      (gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c) by ring,hpdf]
  rw [← hpoint]
  convert mul_le_mul_of_nonneg_left hh hd using 1 <;> ring

theorem fourthPairEvent_section {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (z : Vector r) (s t : ℝ) :
    gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
      (thresholdPairFirstLevel u b j l+s) (thresholdPairSecondLevel u b j l+t) z∈fourthPairEvent u b R j l ↔
      (∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k) ∧
        (s,t)∈ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
          (1/(4*fourthTransportRadius R (gaussianPairBase u b j l z))) := by
  have he := thresholdPairBisector_unit u j l hp
  have hf := thresholdPairDifference_unit u j l hm
  have hef := thresholdPair_frame_orthogonal u j l hu hv
  have hl := gaussianPairSectionPoint_levels (thresholdPairBisector u j l) (thresholdPairDifference u j l)
    (thresholdPairFirstLevel u b j l+s) (thresholdPairSecondLevel u b j l+t) z he hf hef
  simp only [fourthPairEvent,mem_setOf_eq,gaussianPairBase,gaussianPairSectionPoint_comp _ _ he hf hef,
    hl.1,hl.2,add_sub_cancel_left]

/-- True two-normal Gaussian Fubini transport of the paired weighted
coefficient. The remaining hard faces are the original full family. -/
theorem hard_ridge_coefficient_le_fourth_event_strict {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hbound : ∀ z,‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R (gaussianPairBase u b j l z))
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1))) :
    (|supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
      (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l))*
      (standardGaussian (n+1)).real {z | ∀ k,k≠j → k≠l → faceDot (u k) (gaussianPairBase u b j l z)<b k}≤
    (8192*Real.exp ((3:ℝ)/2))*(∫ g,(fourthPairEvent u b R j l).indicator
      (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
  let C := 8192*Real.exp ((3:ℝ)/2)
  have hC : 0≤C := by dsimp [C]; positivity
  let F := (fourthPairEvent u b R j l).indicator (fun g => fourthTransportRadius R g^4)
  have hF : Measurable F := ((continuous_fourthTransportRadius R hRm).measurable.pow_const 4).indicator
    (measurableSet_fourthPairEvent u b R hRm j l)
  have hFi : Integrable F (standardGaussian (n+1)) := hR4.indicator (measurableSet_fourthPairEvent u b R hRm j l)
  have hF0 (g) : 0≤F g := indicator_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g
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
  let d := |supplementalHWeightedRidgeCoefficient (projectionEuclideanVector (u j))
      (projectionEuclideanVector (u l)) (fourthRidgeNormalPoint u b j l)| *gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c
  have hpoint : ∀ᵐ z ∂standardGaussian (n+1),V.indicator (fun _ => d) z≤
      C*(∫ st,F (gaussianPairSectionPoint e f st.1 st.2 z) ∂(gaussianReal 0 1).prod (gaussianReal 0 1)) := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hzV : z∈V
    · rw [indicator_of_mem hzV]
      have hb := fourthRidge_fiber_coefficient_bound u b j l hu hv hp hm R hRm hR hRadd
        (gaussianPairBase u b j l z) (hbound z)
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply normalPair_integral_dominates_translated_fiber
        (fun st => F (gaussianPairSectionPoint e f st.1 st.2 z))
        (fun st => fourthTransportRadius R (gaussianPairBase u b j l z+st.1 • e+st.2 • f)^4)
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

end
end RectangleCLTArxivV1
