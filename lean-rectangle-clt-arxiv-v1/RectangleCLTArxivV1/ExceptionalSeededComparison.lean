import RectangleCLTArxivV1.ExceptionalSeededRemainder
import RectangleCLTArxivV1.ExceptionalComparison
import RectangleCLTArxivV1.GapSeededComparison

/-! Actual normalized interpolation for the exceptional correlation
budget. The only geometric premises are the genuine cubic/full-angle
matrix sums; source R4, time comparison and integration are proved. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def exceptionalComparisonConstant (C₀ C : ℝ) : ℝ :=
  max (positiveGapComparisonConstant C₀ C) (24*Real.sqrt 2*capSmallPairComplementaryConstant)

theorem exceptionalComparisonConstant_pos {C₀ C : ℝ} (hC₀ : 0<C₀) :
    0<exceptionalComparisonConstant C₀ C :=
  (positiveGapComparisonConstant_pos hC₀).trans_le (le_max_left _ _)

theorem exceptional_normalized_remainder_late_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) {c C κ t : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hC : 1≤C) (hκ : 0≤κ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth) (hsmallband : 16*δ≤s.bandwidth)
    (hmatrix : ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |normalizedSeededFourthRemainder s μ ξ A ε hε t|≤
      936*C^3*δ^2*(κ*L*Real.sqrt L)/(exceptionalCutoffDet c*((t+ε)*Real.sqrt (t+ε)))+
      (24*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
        exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2 := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hL : 0<L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0≤ε := mul_nonneg hL.le (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
  have hbf : s.bandwidth≤f.bandwidth := seededRescaledSmoother_bandwidth_ge s hε
  have hb := exceptional_seeded_remainder_late_of_matrix_suppliers h A A hA hA hunit hp f 0
    hc hc1 hC (by positivity) hε ⟨ht.1.le,ht.2.le⟩ (add_pos_of_pos_of_nonneg ht.1 hε)
    (hband.trans hbf) (hsmallband.trans hbf)
    (exceptional_seeded_matrix_estimates_of_angle h f A 0 ⟨ht.1.le,ht.2.le⟩ hc hc1 hmatrix)
  have hδ := h.delta_nonneg
  have hN : 0≤(24*Real.sqrt 2*capSmallPairComplementaryConstant)*δ^2*
      exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c := by
    unfold capSmallPairComplementaryConstant
    exact mul_nonneg (by positivity) (exceptionalCorrelationBudget_nonneg _ _)
  have he := div_le_div_of_nonneg_left hN (sq_pos_of_pos s.bandwidth_pos)
    (pow_le_pow_left₀ s.bandwidth_pos.le hbf 2)
  exact hb.trans (add_le_add_left (by simpa only [hA] using he) _)

/-- The actual R4 has the early/late crossing minimum plus a separate
constant exceptional cost; no global coordinate gap is assumed. -/
theorem exceptional_normalized_remainder_majorant_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1≤p)
    (hunit : ∀ j,covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ≤s.bandwidth)
    {c C C₀ κ t : ℝ} (hc : 0<c) (hc1 : c≤1)
    (hC : 1≤C) (hC₀ : 0<C₀) (hκ : 0<κ) (ht : t ∈ Ioo (0:ℝ) 1)
    (hgapband : restorationBandwidthConstant C*(4*δ)≤s.bandwidth) (hsmallband : 16*δ≤s.bandwidth)
    (hconcentration : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0≤ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |normalizedSeededFourthRemainder s μ ξ A ε hε t|≤
      positiveGapMajorant (δ^2*κ*L/s.bandwidth) ε (exceptionalComparisonConstant C₀ C) c (t+ε)+
      exceptionalComparisonConstant C₀ C*δ^2*
        exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2 := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0<L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0≤ε := mul_nonneg hL.le (sq_nonneg _)
  have hV : 0<t+ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hd := (exceptionalCutoffDet_bounds hc hc1).1
  let D := exceptionalComparisonConstant C₀ C
  let B := δ^2*κ*L/s.bandwidth
  let E := δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2
  have hE : 0≤E := div_nonneg (mul_nonneg (sq_nonneg _) (exceptionalCorrelationBudget_nonneg _ _)) (sq_nonneg _)
  have hdir := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
    hp hunit A hA s hband hC₀ hκ ht hconcentration).2
  have hlate := exceptional_normalized_remainder_late_of_matrix_suppliers μ ξ h hp hunit A hA s
    hc hc1 hC hκ.le ht hgapband hsmallband hmatrix
  have hratio : B*Real.sqrt ε/exceptionalCutoffDet c=δ^2*(κ*L*Real.sqrt L)/exceptionalCutoffDet c := by
    dsimp only [B,ε]
    rw [Real.sqrt_mul hL.le,Real.sqrt_sq hh.le]
    field_simp
    ring
  have hD0 : intrinsicSeededDerivativeConstant C₀≤D :=
    (le_max_left _ _).trans (le_max_left _ _)
  have hD1 : 936*C^3≤D := (le_max_right _ _).trans (le_max_left _ _)
  have hearly : |normalizedSeededFourthRemainder s μ ξ A ε hε t|≤D*(B/(t+ε)) := by
    apply hdir.trans
    calc
      _=intrinsicSeededDerivativeConstant C₀*(B/(t+ε)) := by
        dsimp only [B]; field_simp [hh.ne',hV.ne']; ring
      _≤D*(B/(t+ε)) := mul_le_mul_of_nonneg_right hD0 (by dsimp only [B]; positivity)
  have hlate' : |normalizedSeededFourthRemainder s μ ξ A ε hε t|≤
      D*((B*Real.sqrt ε/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε)))+D*E := by
    apply hlate.trans
    rw [hratio]
    have hfirst := mul_le_mul_of_nonneg_right hD1
      (show 0≤(δ^2*(κ*L*Real.sqrt L)/exceptionalCutoffDet c)/((t+ε)*Real.sqrt (t+ε)) by positivity)
    have hsecond := mul_le_mul_of_nonneg_right
      (show 24*Real.sqrt 2*capSmallPairComplementaryConstant≤D from le_max_right _ _) hE
    convert add_le_add hfirst hsecond using 1 <;> dsimp only [E] <;>
      field_simp [hd.ne',hV.ne',(Real.sqrt_pos.mpr hV).ne',hh.ne'] <;> ring
  have hm := exceptional_early_late_additive_bound (exceptionalComparisonConstant_pos hC₀).le hE hearly hlate'
  simpa only [D,E,B,L,ε,positiveGapMajorant,mul_assoc,div_eq_mul_inv] using hm


theorem exceptional_normalized_time_comparison_of_matrix_suppliers
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j=1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose=covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    {c C C₀ κ : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (hC : 1 ≤ C) (hC₀ : 0 < C₀) (hκ : 0 < κ)
    (hgapband : restorationBandwidthConstant C*(4*δ) ≤ s.bandwidth) (hsmallband : 16*δ≤s.bandwidth)
    (hconcentration : ∀ t ∈ Ioo (0:ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ)
    (hmatrix : ∀ t ∈ Ioo (0:ℝ) 1, ExceptionalNormalizedMatrixEstimates hp s μ ξ A C κ t) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    |normalizedSeededExpectation s μ ξ A ε 1-normalizedSeededExpectation s μ ξ A ε 0| ≤
      (2*exceptionalComparisonConstant C₀ C)*((κ*L)*(δ+δ^2*exceptionalCutoffLog c/s.bandwidth)+
        δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 < ε := mul_pos hL (sq_pos_of_pos hh)
  let f := seededRescaledSmoother s ε hε.le
  let P := normalizedSeededExpectation s μ ξ A ε
  let D := fun t => -(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t+
    normalizedSeededFourthRemainder s μ ξ A ε hε.le t
  let K := exceptionalComparisonConstant C₀ C
  let B := δ^2*κ*L/s.bandwidth
  let E := δ^2*exceptionalCorrelationBudget (covariance μ (sumVector ξ)) c/s.bandwidth^2
  have hE : 0≤E := div_nonneg (mul_nonneg (sq_nonneg _) (exceptionalCorrelationBudget_nonneg _ _)) (sq_nonneg _)
  let M := fun t => positiveGapMajorant B ε K c (t+ε)+K*E
  let a := intrinsicSeededDerivativeConstant C₀*δ*(L*κ)
  have hCi := intrinsicSeededDerivativeConstant_pos hC₀
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hK : 0 < K := exceptionalComparisonConstant_pos hC₀
  have hB : 0 < B := by dsimp only [B]; positivity
  have hP : ContinuousOn P (Icc (0:ℝ) 1) :=
    (continuousOn_seeded_test_expectation f μ ξ h.measurable A ε 0).congr
      (fun t ht => normalizedSeededExpectation_eq_seeded_test s μ ξ h.measurable A hε.le ht)
  have hD (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : HasDerivAt P (D t) t :=
    hasDerivAt_normalizedSeededExpectation s μ ξ h (relativeMomentBounds_of_envelope h) A hA hε.le ht
  have hM : ContinuousOn M (Icc (0:ℝ) 1) :=
    (positiveGapMajorant_continuousOn (b := 1+ε) hε).comp
      (continuousOn_id.add continuousOn_const)
      (fun t ht => ⟨by simpa using add_le_add_right ht.1 ε,
        by simpa using add_le_add_right ht.2 ε⟩) |>.add continuousOn_const
  have hbound (t : ℝ) (ht : t ∈ Ioo (0:ℝ) 1) : |D t| ≤ a+M t := by
    have hx := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
      hp hunit A hA s hband hC₀ hκ ht (hconcentration t ht)).1
    have hfrac : a*t/(t+ε) ≤ a := (div_le_iff₀ (by linarith [ht.1] : 0<t+ε)).2
      (by nlinarith [mul_nonneg ha hε.le])
    have hcub : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a := by
      have hhx : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a*t/(t+ε) := by
        simpa only [abs_mul,abs_neg,a] using hx
      exact hhx.trans hfrac
    have hfour := exceptional_normalized_remainder_majorant_of_matrix_suppliers μ ξ h hp hunit A hA s hband
      hc hc1 hC hC₀ hκ ht hgapband hsmallband (hconcentration t ht) (hmatrix t ht)
    apply (abs_add _ _).trans (add_le_add hcub ?_)
    convert hfour using 1 <;> dsimp only [M,E] <;> ring
  have ht := cap_time_increment_le hP hD hM hbound
  have hint := exceptional_integral_majorant_bound (E := E) hε hB hK.le hc hc1
  have haK : a ≤ K*(κ*L)*δ := by
    have hCK : intrinsicSeededDerivativeConstant C₀≤K :=
      (le_max_left _ _).trans (le_max_left _ _)
    have he := mul_le_mul_of_nonneg_right
      hCK (show 0 ≤ δ*(L*κ) by positivity)
    convert he using 1 <;> dsimp only [a] <;> ring
  apply ht.trans
  apply (add_le_add haK hint).trans
  have hfirst : 0≤K*(κ*L)*δ := by positivity
  have hsecond : 0≤K*E := mul_nonneg hK.le hE
  dsimp only [B,K,E,L] at hfirst hsecond ⊢
  ring_nf at hfirst hsecond ⊢
  nlinarith only [hfirst,hsecond]

end
end RectangleCLTArxivV1
