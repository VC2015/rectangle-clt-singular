import RectangleCLTArxivV1.SupplementalGCapMain
import RectangleCLTArxivV1.SupplementalGMinimalFactor

/-! The exact normalized fourth remainder in the printed path-summary.
For epsilon=L*h^2, its test is rescaled by sqrt(1+epsilon), while the
right-hand cost retains the original h. The raw and normalized versions
are deliberately stated separately. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The printed path-summary R4 uses the rescaled test on the raw path. -/
theorem cap_normalizedSeededFourthRemainder_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    (∫ t in (0 : ℝ)..1, |normalizedSeededFourthRemainder s μ ξ A ε hε t|) ≤
      38*capSeededComparisonConstant C₀*(δ^2*κ*L/s.bandwidth)*
        min (1+Real.log (1/ε)) L := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hε : 0 < ε := mul_pos hLp (sq_pos_of_pos hh)
  let C := capSeededComparisonConstant C₀
  let Ah := δ^2*κ*L/s.bandwidth
  let Sh := (2*(p : ℝ))*(p : ℝ)*δ^2
  let Bh := (2*(p : ℝ))^2*Real.sqrt (p : ℝ)*δ^2/s.bandwidth
  let M := fun t => capMinimumMajorant Ah Sh Bh C (t+ε)
  let f := seededRescaledSmoother s ε hε.le
  have hR := cap_seededFourthRemainder_rank_abs_intervalIntegrable h hp hunit A hA f 0 hh
    (seededRescaledSmoother_bandwidth_ge s hε.le) hband16 hε
  have hM : ContinuousOn M (Icc (0 : ℝ) 1) := by
    exact (capMinimumMajorant_continuousOn (b:=1+ε) hε).comp
      (continuousOn_id.add continuousOn_const) (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |normalizedSeededFourthRemainder s μ ξ A ε hε.le t| ≤ M t :=
    cap_normalizedSeededFourthRemainder_majorant μ ξ h hp hunit A hA s hband hband16 hC₀ hκp ht (hc t ht)
  have hmono := intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num : (0 : ℝ)≤1)
    hR (hM.intervalIntegrable_of_Icc (by norm_num)) hpoint
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : 0 < (p : ℝ) := zero_lt_one.trans_le hpR
  have hlogp : Real.log (p : ℝ) ≤ L := by
    dsimp only [L,dimensionLog]
    rw [Real.log_mul (Real.exp_ne_zero _) hpPos.ne',Real.log_exp]
    linarith
  have hlogS : max (Real.log (Sh/(Ah*Real.sqrt ε))) 0 ≤ 4*L := by
    dsimp only [Sh,Ah,ε]
    rw [cap_seed_single_ratio hδ hκp hLp hh]
    exact cap_single_ratio_log_le hpR hpR le_rfl hκ hL hlogp
  have hlogB : max (Real.log (Bh/Ah)) 0 ≤ 6*L := by
    dsimp only [Bh,Ah]
    rw [cap_seed_pair_ratio hδ hκp hLp hh]
    exact cap_pair_ratio_log_le hpR hpR le_rfl hκ hL hlogp
  have hi := cap_integral_majorant_bound hε hsmall
    (show 0<Ah by dsimp only [Ah]; positivity)
    (show 0<Sh by dsimp only [Sh]; positivity)
    (show 0<Bh by dsimp only [Bh]; positivity)
    (capSeededComparisonConstant_pos hC₀).le hL hlogS hlogB
  exact hmono.trans hi

/-- Actual bounded data supply the concentration of the normalized path's
raw seeded base. The original bandwidth is retained in the exact rate. -/
theorem cap_normalizedSeededFourthRemainder_bounded_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth) (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    let κ := intrinsicBoundaryCoefficient μ ξ A
    (∫ t in (0 : ℝ)..1, |normalizedSeededFourthRemainder s μ ξ A ε hε t|) ≤
      capBoundedIntegratedRemainderConstant*(δ^2*κ*L/s.bandwidth)*
        min (1+Real.log (1/ε)) L := by
  have hε : 0 ≤ dimensionLog p*s.bandwidth^2 :=
    mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  exact cap_normalizedSeededFourthRemainder_integral_bound μ ξ h hδ hp hunit A hA s hband hband16
    intrinsicBoundaryConstant_pos (one_le_intrinsicBoundaryCoefficient μ ξ A hp) hsmall
    (fun t ht => intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA 0 hε ht.1.le ht.2.le)

universe u

/-- The exact printed Proposition G.1, using the normalized R4 defined in
the main path-summary. One fixed constant precedes all models and thresholds. -/
theorem proposition_G1_dimension_log_cap_normalized :
    ∃ C : ℝ, 0 < C ∧ ∀ (Ω : Type u) [MeasurableSpace Ω]
      (μ : Measure Ω) [IsProbabilityMeasure μ] (p n : ℕ)
      (ξ : Fin n → Ω → Vector p) (δ : ℝ),
      BoundedIndependentHypotheses μ ξ δ → ∀ hp : 1 ≤ p,
      (∀ j, covariance μ (sumVector ξ) j j=1) →
      ∀ A : Matrix (Fin p) (Fin p) ℝ, A*A.transpose=covariance μ (sumVector ξ) →
      (rectangleDistance μ (sumVector ξ) A ≤ C*
        min 1 (δ*gaussianMaximumMean A*dimensionLog p*Real.sqrt (dimensionCapGain δ (dimensionLog p)))) ∧
      (∀ s : FaceSmoother p, dimensionCapBandwidthConstant*δ ≤ s.bandwidth →
        dimensionLog p*s.bandwidth^2 ≤ 1/4 →
        let ε := dimensionLog p*s.bandwidth^2
        let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
        (∫ t in (0 : ℝ)..1, |normalizedSeededFourthRemainder s μ ξ A ε hε t|) ≤
          C*(δ^2*intrinsicBoundaryCoefficient μ ξ A*dimensionLog p/s.bandwidth)*
            min (1+Real.log (1/ε)) (dimensionLog p)) := by
  refine ⟨dimensionCapUniversalConstant,dimensionCapUniversalConstant_pos,?_⟩
  intro Ω _ μ _ p n ξ δ h hp hunit A hA
  have hδ : 0 < δ := h.delta_pos hp hunit
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hκ := one_le_intrinsicBoundaryCoefficient μ ξ A hp
  constructor
  · have hr : 0 ≤ dimensionCapRate (gaussianMaximumMean A) δ (dimensionLog p) := by
      unfold dimensionCapRate
      have hg := gaussianMaximumMean_nonneg A
      positivity
    exact (dimensionCapCLT μ ξ h hp hunit A hA).trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (le_min zero_le_one hr))
  · intro s hband hsmall
    have hb : relativeDerivativeBandwidth*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right (le_max_right _ _) hδ.le).trans hband
    have hb16 : 16*δ ≤ s.bandwidth :=
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hδ.le).trans hband
    have hraw := cap_normalizedSeededFourthRemainder_bounded_integral_bound μ ξ h hδ hp hunit A hA s
      (relative_derivative_bandwidth_conditions hδ.le hb).2 hb16 hsmall
    have hε : 0 < dimensionLog p*s.bandwidth^2 :=
      mul_pos (zero_lt_one.trans_le hL) (sq_pos_of_pos s.bandwidth_pos)
    have hG := dimensionCap_time_gain_ge_one hε (by linarith) hL
    have hfactor : 0 ≤ (δ^2*intrinsicBoundaryCoefficient μ ξ A*dimensionLog p/s.bandwidth)*
        min (1+Real.log (1/(dimensionLog p*s.bandwidth^2))) (dimensionLog p) :=
      mul_nonneg (div_nonneg (mul_nonneg (mul_nonneg (sq_nonneg δ) (zero_le_one.trans hκ))
        (zero_le_one.trans hL)) s.bandwidth_pos.le) (zero_le_one.trans hG)
    apply hraw.trans
    have hfin := mul_le_mul_of_nonneg_right
      (le_max_right dimensionCapCoreConstant capBoundedIntegratedRemainderConstant) hfactor
    simpa only [mul_assoc,dimensionCapUniversalConstant] using hfin

end
end RectangleCLTArxivV1
