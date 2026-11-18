import RectangleCLTArxivV1.HFourthSeededRemainder
import RectangleCLTArxivV1.GapComparison
import RectangleCLTArxivV1.SeededIntrinsic

/-! Actual normalized interpolation and gap-log time comparison. The
geometric cubic/pair matrix suppliers are explicit; direct restoration,
the derivative identity, all copy kernels and time integration are proved. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def GapNormalizedMatrixEstimates
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (c C κ t : ℝ) : Prop :=
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  HFourthSeededMatrixEstimates (seededRescaledSmoother s ε hε) μ ξ A 0 ε t c C (κ*L*Real.sqrt L)

def positiveGapComparisonConstant (C₀ C : ℝ) : ℝ :=
  max (intrinsicSeededDerivativeConstant C₀) (936*C^3)

theorem positiveGapComparisonConstant_pos {C₀ C : ℝ} (hC₀ : 0 < C₀) :
    0 < positiveGapComparisonConstant C₀ C :=
  (intrinsicSeededDerivativeConstant_pos hC₀).trans_le (le_max_left _ _)

theorem positiveGap_normalized_remainder_late_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) {c C κ t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hκ : 0 ≤ κ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (hmatrix : GapNormalizedMatrixEstimates hp s μ ξ A c C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
      936*C^3*δ^2*(κ*L*Real.sqrt L)/(exceptionalCutoffDet c*((t+ε)*Real.sqrt (t+ε))) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL.le (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  have hb : restorationBandwidthConstant C*(4*δ) ≤ f.bandwidth :=
    hband.trans (seededRescaledSmoother_bandwidth_ge s hε)
  exact hFourth_seeded_remainder_late_bound_of_matrix_suppliers h A A hA hA hunit f 0
    hc hc1 hgap hC (by positivity) hε ⟨ht.1.le,ht.2.le⟩ (add_pos_of_pos_of_nonneg ht.1 hε) hb hmatrix

/-- The actual normalized R4 has the early/late minimum majorant. Its
late bound is derived from matrix sums, not supplied as a remainder premise. -/
theorem positiveGap_normalized_remainder_majorant_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    {c C C₀ κ t : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hC₀ : 0 < C₀) (hκ : 0 < κ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hgapband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (hconcentration : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : GapNormalizedMatrixEstimates hp s μ ξ A c C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
      positiveGapMajorant (δ^2*κ*L/s.bandwidth) ε (positiveGapComparisonConstant C₀ C) c (t+ε) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL.le (sq_nonneg _)
  have hV : 0 < t+ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  let D := positiveGapComparisonConstant C₀ C
  let B := δ^2*κ*L/s.bandwidth
  have hdir := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
    hp hunit A hA s hband hC₀ hκ ht hconcentration).2
  change |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
    intrinsicSeededDerivativeConstant C₀*δ^2*(L*κ)/(s.bandwidth*(t+ε)) at hdir
  have hlate := positiveGap_normalized_remainder_late_of_matrix_suppliers μ ξ h hp hunit A hA s
    hc hc1 hgap hC hκ.le ht hgapband hmatrix
  have hratio : B*Real.sqrt ε/exceptionalCutoffDet c=δ^2*(κ*L*Real.sqrt L)/exceptionalCutoffDet c := by
    dsimp only [B,ε]
    rw [Real.sqrt_mul hL.le,Real.sqrt_sq hh.le]
    field_simp
    ring
  have hdir' : |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤ D*(B/(t+ε)) := by
    apply hdir.trans
    calc
      _ = intrinsicSeededDerivativeConstant C₀*(B/(t+ε)) := by
        dsimp only [B]
        field_simp [hh.ne',hV.ne']
        ring
      _ ≤ D*(B/(t+ε)) := mul_le_mul_of_nonneg_right (le_max_left _ _) (by dsimp only [B]; positivity)
  have hlate' : |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
      D*((B*Real.sqrt ε/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε))) := by
    apply hlate.trans
    rw [hratio]
    calc
      _ = (936*C^3)*((δ^2*(κ*L*Real.sqrt L)/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε))) := by
        field_simp [hd.ne',hV.ne',(Real.sqrt_pos.mpr hV).ne']
        ring
      _ ≤ D*((δ^2*(κ*L*Real.sqrt L)/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε))) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  change |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤ positiveGapMajorant B ε D c (t+ε)
  unfold positiveGapMajorant
  rw [mul_min_of_nonneg _ _ (positiveGapComparisonConstant_pos hC₀).le]
  exact le_min hdir' hlate'

/-- Actual normalized expectation increment with logarithmic gap cost.
Only the two upstream matrix estimates and the actual base concentration
remain explicit; the literal derivative and its integration are proved. -/
theorem positiveGap_normalized_time_comparison_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    {c C C₀ κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : ∀ j k : Fin p, j≠k → c ≤ 1-|covariance μ (sumVector ξ) j k|)
    (hC : 1 ≤ C) (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hgapband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth)
    (hconcentration : ∀ t ∈ Ioo (0:ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ∀ t ∈ Ioo (0:ℝ) 1, GapNormalizedMatrixEstimates hp s μ ξ A c C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    |normalizedSeededExpectation s μ ξ A ε 1-normalizedSeededExpectation s μ ξ A ε 0| ≤
      (2*positiveGapComparisonConstant C₀ C)*(κ*L)*(δ+δ^2*positiveGapGain c/s.bandwidth) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 < ε := mul_pos hL (sq_pos_of_pos hh)
  let f := seededRescaledSmoother s ε hε.le
  let P := normalizedSeededExpectation s μ ξ A ε
  let D := fun t => -(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t+
    normalizedSeededFourthRemainder s μ ξ A ε hε.le t
  let K := positiveGapComparisonConstant C₀ C
  let B := δ^2*κ*L/s.bandwidth
  let M := fun t => positiveGapMajorant B ε K c (t+ε)
  let a := intrinsicSeededDerivativeConstant C₀*δ*(L*κ)
  have hCi := intrinsicSeededDerivativeConstant_pos hC₀
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hK : 0 < K := positiveGapComparisonConstant_pos hC₀
  have hB : 0 < B := by dsimp only [B]; positivity
  have hP : ContinuousOn P (Icc (0:ℝ) 1) :=
    (continuousOn_seeded_test_expectation f μ ξ h.measurable A ε 0).congr
      (fun t ht => normalizedSeededExpectation_eq_seeded_test s μ ξ h.measurable A hε.le ht)
  have hD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt P (D t) t :=
    hasDerivAt_normalizedSeededExpectation s μ ξ h (relativeMomentBounds_of_envelope h) A hA hε.le ht
  have hM : ContinuousOn M (Icc (0:ℝ) 1) :=
    (positiveGapMajorant_continuousOn (b := 1+ε) hε).comp
      (continuousOn_id.add continuousOn_const)
      (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hbound (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : |D t| ≤ a+M t := by
    have hx := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
      hp hunit A hA s hband hC₀ hκ ht (hconcentration t ht)).1
    have hfrac : a*t/(t+ε) ≤ a := (div_le_iff₀ (by linarith [ht.1] : 0<t+ε)).2
      (by nlinarith [mul_nonneg ha hε.le])
    have hcub : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a := by
      have hhx : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a*t/(t+ε) := by
        simpa only [abs_mul,abs_neg,a] using hx
      exact hhx.trans hfrac
    have hfour := positiveGap_normalized_remainder_majorant_of_matrix_suppliers μ ξ h hp hunit A hA s hband
      hc hc1 hgap hC hC₀ hκ ht hgapband (hconcentration t ht) (hmatrix t ht)
    exact (abs_add _ _).trans (add_le_add hcub hfour)
  have ht := cap_time_increment_le hP hD hM hbound
  have hint := positiveGap_integral_majorant_bound hε hB hK.le hc hc1
  have haK : a ≤ K*(κ*L)*δ := by
    have he := mul_le_mul_of_nonneg_right
      (le_max_left (intrinsicSeededDerivativeConstant C₀) (936*C^3)) (show 0 ≤ δ*(L*κ) by positivity)
    convert he using 1 <;> dsimp only [a,K,positiveGapComparisonConstant] <;> ring
  apply ht.trans
  apply (add_le_add haK hint).trans
  have hfirst : K*(κ*L)*δ ≤ 2*K*(κ*L)*δ := by
    have hn : 0 ≤ K*(κ*L)*δ := by positivity
    nlinarith only [hn]
  calc
    K*(κ*L)*δ+2*K*B*positiveGapGain c ≤ 2*K*(κ*L)*δ+2*K*B*positiveGapGain c :=
      add_le_add_right hfirst _
    _ = _ := by dsimp only [B,K]; ring

end
end RectangleCLTArxivV1
