import RectangleCLTCompanion.SplitV4.Printed.EndpointConcentration

/-! The printed Lemma 2 route: actual clock width, random-radius
concentration and Jensen at both endpoints, triangle, then supremum. -/
open MeasureTheory Set
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem endpoint_error_le_average_radius_comp
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (C δ L : ℝ)
    (hLayer : ∀ r, 0 ≤ r → μ.real {ω | W ω ∈ s.boundaryLayer r} ≤ C*(r+δ)*Real.sqrt L) :
    |μ.real {ω | s.Inside (W ω)}-(∫ ω, s.F (W ω) ∂μ)| ≤
      C*((∫ e, randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p)+δ)*Real.sqrt L := by
  letI : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  have hc := endpoint_error_le_average_radius hp s (μ.map W) C δ L (by
    intro r hr
    simpa only [Measure.real, Measure.map_apply hW (s.measurableSet_boundaryLayer r)] using hLayer r hr)
  rw [integral_map hW.aemeasurable s.continuous_F.aestronglyMeasurable] at hc
  simpa only [Measure.real, Measure.map_apply hW s.measurableSet_Inside] using hc

theorem lemma2_printed_endpoint_bounds
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hb : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hs : s.faces=Finset.univ) :
    |μ.real {ω | s.Inside (sumVector ξ ω)}-(∫ ω, s.F (sumVector ξ ω) ∂μ)| ≤
        512*((∫ e, randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p)+δ)*Real.sqrt (dimensionLog p) ∧
    |(gaussianLaw A).real {x | s.Inside x}-(∫ x, s.F x ∂gaussianLaw A)| ≤
        512*(∫ e, randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p)*Real.sqrt (dimensionLog p) := by
  constructor
  · exact endpoint_error_le_average_radius_comp hp s μ (sumVector ξ) hb.measurable_sum 512 δ
      (dimensionLog p) (fun _ hr => bounded_boundary_layer_le μ ξ hb hp hunit s hs hr)
  · have hd (j) : (A*A.transpose) j j=1 := by rw [hA,hunit]
    simpa only [add_zero] using endpoint_error_le_average_radius hp s (gaussianLaw A) 512 0
      (dimensionLog p) (fun _ hr => by simpa only [add_zero] using gaussian_boundary_layer_le hp A hd s hs hr)

/-- The final printed transition, including all measurable rectangles.
The universal numerical constant is inessential; the route retains the
actual expected width until after both endpoint inequalities. -/
theorem smoothingLemma2_printed
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ : ℝ}
    (hb : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (h : ℝ) (hh : 0<h) (hband : δ≤h) :
    rectangleDistance μ (sumVector ξ) A ≤ smoothingDiscrepancy μ (sumVector ξ) A h hh+
      4608*h*Real.sqrt (dimensionLog p)*dimensionLog p := by
  have hL := log_exp_mul_nat_ge_one hp
  change 1≤dimensionLog p at hL
  have hR := integral_randomThresholdRadius_le_log hp hh.le
  have hδ : δ≤h*dimensionLog p := hband.trans (by nlinarith)
  have hboxes (lo hi : Vector p) : rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
      smoothingDiscrepancy μ (sumVector ξ) A h hh+4608*h*Real.sqrt (dimensionLog p)*dimensionLog p := by
    let s := FaceSmoother.closedBox lo hi h hh
    have he := lemma2_printed_endpoint_bounds μ ξ hb hp hunit A hA s rfl
    have hgap := closedBoxSmoothingGap_le_smoothingDiscrepancy μ (sumVector ξ) hb.measurable_sum A h hh (lo,hi)
    have hinside : {x | s.Inside x}=(Rect.closedBox lo hi).carrier := by
      ext x; exact FaceSmoother.closedBox_Inside lo hi h hh x
    have hinsideW : {ω | s.Inside (sumVector ξ ω)}=(sumVector ξ) ⁻¹' (Rect.closedBox lo hi).carrier := by
      ext ω; exact FaceSmoother.closedBox_Inside lo hi h hh (sumVector ξ ω)
    rw [hinsideW] at he
    rw [hinside] at he
    change |μ.real ((sumVector ξ) ⁻¹' (Rect.closedBox lo hi).carrier)-
      (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
    have ht := abs_add_three (μ.real ((sumVector ξ) ⁻¹' (Rect.closedBox lo hi).carrier)-∫ ω,s.F (sumVector ξ ω) ∂μ)
      ((∫ ω,s.F (sumVector ξ ω) ∂μ)-∫ x,s.F x ∂gaussianLaw A)
      ((∫ x,s.F x ∂gaussianLaw A)-(gaussianLaw A).real (Rect.closedBox lo hi).carrier)
    have hrate := mul_le_mul_of_nonneg_right hR (Real.sqrt_nonneg (dimensionLog p))
    have hdrate := mul_le_mul_of_nonneg_right hδ (Real.sqrt_nonneg (dimensionLog p))
    change |(∫ ω,s.F (sumVector ξ ω) ∂μ)-(∫ x,s.F x ∂gaussianLaw A)| ≤ _ at hgap
    have hsum : (μ.real ((sumVector ξ) ⁻¹' (Rect.closedBox lo hi).carrier)-∫ ω,s.F (sumVector ξ ω) ∂μ)+
        ((∫ ω,s.F (sumVector ξ ω) ∂μ)-∫ x,s.F x ∂gaussianLaw A)+
        ((∫ x,s.F x ∂gaussianLaw A)-(gaussianLaw A).real (Rect.closedBox lo hi).carrier)=
        μ.real ((sumVector ξ) ⁻¹' (Rect.closedBox lo hi).carrier)-(gaussianLaw A).real (Rect.closedBox lo hi).carrier := by ring
    rw [hsum,abs_sub_comm (∫ x,s.F x ∂gaussianLaw A)] at ht
    have hhR : (∫ e,randomThresholdRadius p s.bandwidth e ∂exponentialRectangleLaw p)=
      (∫ e,randomThresholdRadius p h e ∂exponentialRectangleLaw p) := rfl
    rw [hhR] at he
    nlinarith [he.1,he.2,ht]
  apply rectangleDistance_le
  intro R
  exact rectangleError_le_of_closedBox hp μ (sumVector ξ) hb.measurable_sum A hboxes R

end
end RectangleCLT.Companion.SplitV4.Printed
