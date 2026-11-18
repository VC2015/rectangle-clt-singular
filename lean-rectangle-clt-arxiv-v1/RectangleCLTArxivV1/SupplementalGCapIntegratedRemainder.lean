import RectangleCLTArxivV1.SupplementalGCapSeededComparison
import RectangleCLTArxivV1.SupplementalGTimeMeasurability
import RectangleCLTArxivV1.SeededIntrinsicConcentration

/-! The literal raw fourth-remainder integral in the dimension-cap proposition.
Both actual remainder estimates and its actual time integrability are proved;
the final bounded endpoint also supplies its actual seeded concentration. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- The original, unrescaled seeded R4 has the same actual cap majorant. -/
theorem cap_seededFourthRemainder_majorant
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth)
    {C₀ κ t : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A x (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    |seededFourthRemainder s μ ξ A x ε t| ≤
      capMinimumMajorant (δ^2*κ*L/s.bandwidth) ((2*(p : ℝ))*(p : ℝ)*δ^2)
        ((2*(p : ℝ))^2*Real.sqrt (p : ℝ)*δ^2/s.bandwidth)
        (capSeededComparisonConstant C₀) (t+ε) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL.le (sq_nonneg _)
  let C := capSeededComparisonConstant C₀
  let V := t+ε
  let Ah := δ^2*κ*L/s.bandwidth
  let Sh := (2*(p : ℝ))*(p : ℝ)*δ^2
  let Bh := (2*(p : ℝ))^2*Real.sqrt (p : ℝ)*δ^2/s.bandwidth
  have hV : 0 < V := add_pos_of_pos_of_nonneg ht.1 hε
  have hC : 0 ≤ C := (capSeededComparisonConstant_pos hC₀).le
  have hAh : 0 ≤ Ah := by dsimp only [Ah]; positivity
  have hSh : 0 ≤ Sh := by dsimp only [Sh]; positivity
  have hBh : 0 ≤ Bh := by dsimp only [Bh]; positivity
  have hd := intrinsic_seeded_fourth_remainder_bound μ ξ h (relativeMomentBounds_of_envelope h)
    hp hunit A hA s x hh le_rfl ht hband hC₀ hκ hc
  have hdir : |seededFourthRemainder s μ ξ A x ε t| ≤ C*(Ah/V) := by
    apply hd.trans
    calc
      _ = intrinsicSeededDerivativeConstant C₀*(Ah/V) := by
        change intrinsicSeededDerivativeConstant C₀*δ^2*(L*κ)/(s.bandwidth*V) = _
        dsimp only [Ah]
        rw [div_div]
        ring
      _ ≤ C*(Ah/V) := mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg hAh hV.le)
  have hfaces : (s.faces.card : ℝ) ≤ 2*(p : ℝ) := by
    have hf := Finset.card_le_card (s.faces.subset_univ)
    have hf' : s.faces.card ≤ 2*p := by
      simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using hf
    exact_mod_cast hf'
  have hcomp0 := cap_seededFourthRemainder_complementary_bound h A A hA hA hunit hp s x
    s.bandwidth_pos le_rfl hband16 hε ht
  have hsum : (s.faces.card : ℝ)*(p : ℝ)*δ^2/(V*Real.sqrt V)+
      (s.faces.card : ℝ)^2*Real.sqrt (p : ℝ)*δ^2/(s.bandwidth*Real.sqrt V) ≤
      Sh/(V*Real.sqrt V)+Bh/Real.sqrt V := by
    dsimp only [Sh,Bh]
    rw [div_div]
    apply add_le_add <;> gcongr
  have hcomp : |seededFourthRemainder s μ ξ A x ε t| ≤
      C*(Sh/(V*Real.sqrt V)+Bh/Real.sqrt V) := by
    apply hcomp0.trans
    calc
      _ ≤ capSeededComplementaryConstant*(Sh/(V*Real.sqrt V)+Bh/Real.sqrt V) :=
        mul_le_mul_of_nonneg_left hsum capSeededComplementaryConstant_nonneg
      _ ≤ C*(Sh/(V*Real.sqrt V)+Bh/Real.sqrt V) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  have hsplit := cap_abs_le_split_min (div_nonneg hAh hV.le)
    (div_nonneg hSh (mul_nonneg hV.le (Real.sqrt_nonneg _)))
    (div_nonneg hBh (Real.sqrt_nonneg _)) hC hdir hcomp
  change |seededFourthRemainder s μ ξ A x ε t| ≤ capMinimumMajorant Ah Sh Bh C V
  exact le_min (by convert hdir using 1; ring) hsplit

/-- Integrate the absolute value of the literal R4. Its time integrability
is proved from the actual data and complementary estimate, not assumed. -/
theorem cap_seededFourthRemainder_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth)
    {C₀ κ : ℝ} (hC₀ : 0 < C₀) (hκ : 1 ≤ κ)
    (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4)
    (hc : ∀ t ∈ Ioo (0 : ℝ) 1, IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A x (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    (∫ t in (0 : ℝ)..1, |seededFourthRemainder s μ ξ A x ε t|) ≤
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
  have hR := cap_seededFourthRemainder_abs_intervalIntegrable h A A hA hA hunit hp s x hh le_rfl hband16 hε
  have hM : ContinuousOn M (Icc (0 : ℝ) 1) := by
    exact (capMinimumMajorant_continuousOn (b:=1+ε) hε).comp
      (continuousOn_id.add continuousOn_const) (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hpoint (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |seededFourthRemainder s μ ξ A x ε t| ≤ M t :=
    cap_seededFourthRemainder_majorant μ ξ h hp hunit A hA s x hband hband16 hC₀ hκp ht (hc t ht)
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

def capBoundedIntegratedRemainderConstant : ℝ :=
  38*capSeededComparisonConstant intrinsicBoundaryConstant

theorem capBoundedIntegratedRemainderConstant_pos : 0 < capBoundedIntegratedRemainderConstant :=
  mul_pos (by norm_num) (capSeededComparisonConstant_pos intrinsicBoundaryConstant_pos)

/-- The actual bounded-array integral endpoint with one fixed universal
constant, uniformly over every smoother and translation. The actual
intrinsic seeded concentration is supplied by its proved theorem. -/
theorem cap_seededFourthRemainder_bounded_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hδ : 0 < δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (x : Vector p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth) (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let κ := intrinsicBoundaryCoefficient μ ξ A
    (∫ t in (0 : ℝ)..1, |seededFourthRemainder s μ ξ A x ε t|) ≤
      capBoundedIntegratedRemainderConstant*(δ^2*κ*L/s.bandwidth)*
        min (1+Real.log (1/ε)) L := by
  have hε : 0 ≤ dimensionLog p*s.bandwidth^2 :=
    mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
  exact cap_seededFourthRemainder_integral_bound μ ξ h hδ hp hunit A hA s x hband hband16
    intrinsicBoundaryConstant_pos (one_le_intrinsicBoundaryCoefficient μ ξ A hp) hsmall
    (fun t ht => intrinsicRectangleConcentration_seededSplitBase h hp hunit A hA x hε ht.1.le ht.2.le)

end
end RectangleCLTArxivV1
