import RectangleCLTArxivV1.SupplementalHFourthTransportData

/-! Genuine Gaussian normal transport of the actual fourth-radius facet
fiber. The inactive faces may be dependent and parallel. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem fourthFacet_fiber_coefficient_bound {r : ℕ}
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (u x : Vector r) (hu : vectorNormSq u=1) (b : ℝ) (hx : faceDot u x=b)
    (hbound : |b|≤fourthTransportRadius R x) :
    abs (|b| *(b^2-1))*gaussianPDFReal 0 1 b≤
      (128*Real.exp ((3:ℝ)/2))*(∫ t in Icc (0:ℝ) (1/(4*fourthTransportRadius R x)),
        fourthTransportRadius R (x+t • u)^4*gaussianPDFReal 0 1 (b+t)) := by
  let v := projectionEuclideanVector u
  let X := projectionEuclideanVector x
  have hv : ‖v‖=1 := thresholdEuclideanNormal_unit _ hu
  have hz : |⟪b • v,v⟫_ℝ|≤R X := by
    simpa only [inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq,hv,one_pow,mul_one] using hbound
  have hh := adaptive_weighted_facet_fourth_bound R hRm hR hRadd X v (b • v) hv hz
  have hinner : ⟪b • v,v⟫_ℝ=b := by simp only [inner_smul_left,conj_trivial,real_inner_self_eq_norm_sq,hv,one_pow,mul_one]
  rw [hinner] at hh
  let c := (Real.sqrt (2*Real.pi))⁻¹
  have hc : 0≤c := by dsimp [c]; positivity
  have hpdf (t : ℝ) : gaussianPDFReal 0 1 t=c*RectangleCLT.Companion.SignedSurface.gaussianKernel (t • v) := by
    simp only [RectangleCLT.Companion.SignedSurface.gaussianKernel,norm_smul,Real.norm_eq_abs,hv,mul_one,sq_abs]
    simp only [gaussianPDFReal,c,NNReal.coe_one,mul_one,sub_zero]
  have hint : (∫ t in Icc (0:ℝ) (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+t • u)^4*gaussianPDFReal 0 1 (b+t))=
      c*(∫ t in Icc (0:ℝ) (1/(4*R X)), R (X+t • v)^4*RectangleCLT.Companion.SignedSurface.gaussianKernel (b • v+t • v)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun t => by
      dsimp only
      rw [hpdf,← add_smul]
      change R (X+t • v)^4*(c*RectangleCLT.Companion.SignedSurface.gaussianKernel ((b+t) • v))=
        c*(R (X+t • v)^4*RectangleCLT.Companion.SignedSurface.gaussianKernel ((b+t) • v))
      ring)
  rw [hint,hpdf]
  convert mul_le_mul_of_nonneg_left hh hc using 1 <;> ring

/-- Actual weighted facet Green coefficient paid by its actual fourth-radius
adaptive event mass. No surface or Gaussian fiber bound is assumed. -/
theorem hard_facet_coefficient_le_fourth_event {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hreg : ResidualThresholdRegularity u b j)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x, 1≤R x)
    (hRadd : ∀ x d, R (x+d)≤R x+‖d‖)
    (hface : ∀ x, |faceDot (u j) x|≤fourthTransportRadius R x)
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian (n+1))) :
    abs (|b j| *(b j^2-1))*gaussianThresholdFirst u b j≤
      (128*Real.exp ((3:ℝ)/2))*(∫ g, (fourthFacetEvent u b R j).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian (n+1)) := by
  let C := 128*Real.exp ((3:ℝ)/2)
  have hC : 0≤C := by dsimp [C]; positivity
  let F := (fourthFacetEvent u b R j).indicator (fun g => fourthTransportRadius R g^4)
  have hF : Measurable F := ((continuous_fourthTransportRadius R hRm).measurable.pow_const 4).indicator
    (measurableSet_fourthFacetEvent u b R hRm j)
  have hFi : Integrable F (standardGaussian (n+1)) := hR4.indicator (measurableSet_fourthFacetEvent u b R hRm j)
  have hF0 (g) : 0≤F g := indicator_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g
  have hprod := (integrable_gaussianNormalSectionMap_iff (u j) hu F hF).mpr hFi
  let V : Set (Vector (n+1)) := {z | ∀ l, l≠j → faceDot (u l) (gaussianFacetBase u b j z)<b l}
  have hV : MeasurableSet V := by
    unfold V
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun l => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp (measurable_gaussianSectionPoint _ _)) measurable_const))
  let c := abs (|b j| *(b j^2-1))*gaussianPDFReal 0 1 (b j)
  have hpoint : ∀ᵐ z ∂standardGaussian (n+1), V.indicator (fun _ => c) z≤
      C*(∫ t, F (gaussianSectionPoint (u j) t z) ∂gaussianReal 0 1) := by
    filter_upwards [hprod.prod_left_ae] with z hz
    by_cases hv : z∈V
    · rw [indicator_of_mem hv]
      have hbase : faceDot (u j) (gaussianFacetBase u b j z)=b j :=
        gaussianSectionPoint_on_hyperplane (u j) (b j) hu z
      have hbound : |b j|≤fourthTransportRadius R (gaussianFacetBase u b j z) := by
        simpa only [hbase] using hface (gaussianFacetBase u b j z)
      have hb := fourthFacet_fiber_coefficient_bound R hRm hR hRadd (u j)
        (gaussianFacetBase u b j z) hu (b j) hbase hbound
      apply hb.trans
      apply mul_le_mul_of_nonneg_left _ hC
      apply normal_integral_dominates_translated_fiber
        (fun t => F (gaussianSectionPoint (u j) t z))
        (fun t => fourthTransportRadius R (gaussianFacetBase u b j z+t • u j)^4)
        hz (fun _ => hF0 _) (b j) (1/(4*fourthTransportRadius R (gaussianFacetBase u b j z)))
      intro t ht
      have he : gaussianSectionPoint (u j) (b j+t) z∈fourthFacetEvent u b R j := by
        rw [fourthFacetEvent_section u b R j hu]
        exact ⟨hv,by simpa only [add_sub_cancel_left] using ht⟩
      dsimp only [F]
      rw [indicator_of_mem he,gaussianSectionPoint_add_parameter]
      rfl
    · rw [indicator_of_not_mem hv]
      exact mul_nonneg hC (integral_nonneg (fun _ => hF0 _))
  have hmineq := integral_mono_ae ((integrable_const c).indicator hV)
    (hprod.integral_prod_right.const_mul C) hpoint
  have hmass : (∫ z, V.indicator (fun _ => c) z ∂standardGaussian (n+1))=
      abs (|b j| *(b j^2-1))*gaussianThresholdFirst u b j := by
    rw [integral_indicator_const _ hV,gaussianThresholdFirst_eq_section_of_slack u b j hu
      (fun l hl => (hreg l (Finset.mem_erase.mpr ⟨hl,Finset.mem_univ _⟩)).1),
      gaussianThresholdSectionProbability_eq_strict_of_slack u b j (b j)
        (fun l hl => (hreg l hl).1)]
    change (standardGaussian (n+1)).real V*c=_
    dsimp only [c,V,gaussianFacetBase]
    ring
  rw [hmass,integral_const_mul] at hmineq
  apply hmineq.trans_eq
  congr 1
  rw [← integral_prod_symm _ hprod]
  exact integral_gaussianNormalSectionMap (u j) hu F hF

end
end RectangleCLTArxivV1
