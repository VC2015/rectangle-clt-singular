import RectangleCLTArxivV1.ExceptionalSeededComparison
import RectangleCLTArxivV1.SupplementalGTimeMeasurability

/-! The literal time integral of the actual normalized fourth remainder.
Its L1 is proved from the bounded original array before applying the
separated/exceptional majorant; no time-integrability premise is supplied. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped Interval
noncomputable section
set_option autoImplicit false

theorem exceptional_normalized_remainder_abs_intervalIntegrable
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : 16*δ≤s.bandwidth) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    IntervalIntegrable (fun t => |normalizedSeededFourthRemainder s μ ξ A ε hε t|) volume 0 1 := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hL : 0<L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0<ε := mul_pos hL (sq_pos_of_pos s.bandwidth_pos)
  exact cap_seededFourthRemainder_abs_intervalIntegrable h A A hA hA hunit hp
    (seededRescaledSmoother s ε hε.le) 0 s.bandwidth_pos
    (seededRescaledSmoother_bandwidth_ge s hε.le) hband hε

/-- The printed integrated R4 bound, with the actual source remainder
and the literal original-coordinate exceptional budget. -/
theorem exceptional_normalized_remainder_integral_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ≤s.bandwidth)
    {c C C₀ κ : ℝ} (hc : 0<c) (hc1 : c≤1) (hC : 1≤C) (hC₀ : 0<C₀) (hκ : 0<κ)
    (hgapband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth) (hsmallband : 16*δ≤s.bandwidth)
    (hconcentration : ∀ t ∈ Ioo (0:ℝ) 1,IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ∀ t ∈ Ioo (0:ℝ) 1,ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    (∫ t in (0:ℝ)..1,|normalizedSeededFourthRemainder s μ ξ A ε hε t|)≤
      2*exceptionalComparisonConstant C₀ C*δ^2*κ*L*exceptionalCutoffLog c/s.bandwidth+
      exceptionalComparisonConstant C₀ C*δ^2*
        exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2 := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  let D := exceptionalComparisonConstant C₀ C
  let B := δ^2*κ*L/s.bandwidth
  let E := δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2
  have hδ : 0<δ := h.delta_pos hp hunit
  have hL : 0<L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0<ε := mul_pos hL (sq_pos_of_pos s.bandwidth_pos)
  have hD : 0<D := exceptionalComparisonConstant_pos hC₀
  have hh := s.bandwidth_pos
  have hB : 0<B := by dsimp only [B]; positivity
  let M := fun t => positiveGapMajorant B ε D c (t+ε)+D*E
  have hM : ContinuousOn M (Icc (0:ℝ) 1) :=
    ((positiveGapMajorant_continuousOn (b := 1+ε) hε).comp
      (continuousOn_id.add continuousOn_const)
      (fun t ht => ⟨by simpa using add_le_add_right ht.1 ε,
        by simpa using add_le_add_right ht.2 ε⟩)).add continuousOn_const
  have hi := exceptional_normalized_remainder_abs_intervalIntegrable h hp hunit A hA s hsmallband
  have hpnt (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) :
      |normalizedSeededFourthRemainder s μ ξ A ε hε.le t|≤M t := by
    have hb := exceptional_normalized_remainder_majorant_of_matrix_suppliers μ ξ h hp hunit A hA s hband
      hc hc1 hC hC₀ hκ ht hgapband hsmallband (hconcentration t ht) (hmatrix t ht)
    convert hb using 1 <;> dsimp only [M,E] <;> ring
  have hb := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0:ℝ)≤1)
    hi (hM.intervalIntegrable_of_Icc (by norm_num)) hpnt
  have hint := exceptional_integral_majorant_bound (E := E) hε hB hD.le hc hc1
  exact (hb.trans hint).trans_eq (by dsimp only [B,D,E,L]; ring)

end
end RectangleCLTArxivV1
