import RectangleCLTArxivV1.SupplementalGCapComparison

/-! Actual normalized seeded fourth remainder and time comparison with the
supplemental dimension-logarithm cap. Only the actual concentration supplier
is retained as an input; the direct and complementary fourth estimates,
normalized derivative identity and time integration are proved. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def capSeededComparisonConstant (C₀ : ℝ) : ℝ :=
  max (intrinsicSeededDerivativeConstant C₀) capSeededComplementaryConstant

def capSeededTimeComparisonConstant (C₀ : ℝ) : ℝ := 38*capSeededComparisonConstant C₀

theorem capSeededComparisonConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < capSeededComparisonConstant C₀ :=
  (intrinsicSeededDerivativeConstant_pos hC₀).trans_le (le_max_left _ _)

theorem capSeededTimeComparisonConstant_pos {C₀ : ℝ} (hC₀ : 0 < C₀) :
    0 < capSeededTimeComparisonConstant C₀ :=
  mul_pos (by norm_num) (capSeededComparisonConstant_pos hC₀)

/-- The literal normalized R4 is controlled by the minimum of its actual
intrinsic and complementary bounds. The latter uses the square covariance
factor as a rectangular factor of dimension p. -/
theorem cap_normalizedSeededFourthRemainder_majorant
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (s : FaceSmoother p) (hband : seededRestorationBandwidth*δ ≤ s.bandwidth)
    (hband16 : 16*δ ≤ s.bandwidth)
    {C₀ κ t : ℝ} (hC₀ : 0 < C₀) (hκ : 0 < κ) (ht : t ∈ Ioo (0 : ℝ) 1)
    (hc : IntrinsicRectangleConcentration
      (seededSplitBaseDistribution μ ξ A 0 (dimensionLog p*s.bandwidth^2) t) C₀ δ κ) :
    let L := dimensionLog p
    let ε := L*s.bandwidth^2
    let hε : 0 ≤ ε := mul_nonneg (zero_le_one.trans (log_exp_mul_nat_ge_one hp)) (sq_nonneg _)
    |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
      capMinimumMajorant (δ^2*κ*L/s.bandwidth) ((2*(p : ℝ))*(p : ℝ)*δ^2)
        ((2*(p : ℝ))^2*Real.sqrt (p : ℝ)*δ^2/s.bandwidth)
        (capSeededComparisonConstant C₀) (t+ε) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  have hε : 0 ≤ ε := mul_nonneg hL.le (sq_nonneg _)
  let f := seededRescaledSmoother s ε hε
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
  have hd := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
    hp hunit A hA s hband hC₀ hκ ht hc).2
  have hdir : |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤ C*(Ah/V) := by
    apply hd.trans
    calc
      _ = intrinsicSeededDerivativeConstant C₀*(Ah/V) := by
        change intrinsicSeededDerivativeConstant C₀*δ^2*(L*κ)/(s.bandwidth*V) = _
        dsimp only [Ah]
        rw [div_div]
        ring
      _ ≤ C*(Ah/V) := mul_le_mul_of_nonneg_right (le_max_left _ _) (div_nonneg hAh hV.le)
  have hfaces : (f.faces.card : ℝ) ≤ 2*(p : ℝ) := by
    have hf := Finset.card_le_card (f.faces.subset_univ)
    have hf' : f.faces.card ≤ 2*p := by
      simpa only [Finset.card_univ,Fintype.card_prod,Fintype.card_fin,Fintype.card_bool,mul_comm] using hf
    exact_mod_cast hf'
  have hcomp0 := cap_seededFourthRemainder_complementary_bound h A A hA hA hunit hp f 0
    s.bandwidth_pos (seededRescaledSmoother_bandwidth_ge s hε) hband16 hε ht
  have hsum : (f.faces.card : ℝ)*(p : ℝ)*δ^2/(V*Real.sqrt V)+
      (f.faces.card : ℝ)^2*Real.sqrt (p : ℝ)*δ^2/(s.bandwidth*Real.sqrt V) ≤
      Sh/(V*Real.sqrt V)+Bh/Real.sqrt V := by
    dsimp only [Sh,Bh]
    rw [div_div]
    apply add_le_add <;> gcongr
  have hcomp : |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤
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
  change |normalizedSeededFourthRemainder s μ ξ A ε hε t| ≤ capMinimumMajorant Ah Sh Bh C V
  exact le_min (by convert hdir using 1; ring) hsplit

/-- The actual normalized seeded time gap has the capped fourth cost.
The concentration hypothesis concerns the actual seeded base law; no
remainder, derivative or CLT comparison bound is assumed. -/
theorem cap_normalizedSeeded_time_comparison_bound
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
    |normalizedSeededExpectation s μ ξ A ε 1-normalizedSeededExpectation s μ ξ A ε 0| ≤
      capSeededTimeComparisonConstant C₀*(κ*L)*
        (δ+δ^2/s.bandwidth*min (1+Real.log (1/ε)) L) := by
  let L := dimensionLog p
  let ε := L*s.bandwidth^2
  have hh := s.bandwidth_pos
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hκp : 0 < κ := zero_lt_one.trans_le hκ
  have hε : 0 < ε := mul_pos hLp (sq_pos_of_pos s.bandwidth_pos)
  let f := seededRescaledSmoother s ε hε.le
  let P := normalizedSeededExpectation s μ ξ A ε
  let D := fun t => -(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t+
    normalizedSeededFourthRemainder s μ ξ A ε hε.le t
  let C := capSeededComparisonConstant C₀
  let Ah := δ^2*κ*L/s.bandwidth
  let Sh := (2*(p : ℝ))*(p : ℝ)*δ^2
  let Bh := (2*(p : ℝ))^2*Real.sqrt (p : ℝ)*δ^2/s.bandwidth
  let M := fun t => capMinimumMajorant Ah Sh Bh C (t+ε)
  let a := intrinsicSeededDerivativeConstant C₀*δ*(L*κ)
  have hCi := intrinsicSeededDerivativeConstant_pos hC₀
  have ha : 0 ≤ a := by dsimp only [a]; positivity
  have hP : ContinuousOn P (Icc (0 : ℝ) 1) :=
    (continuousOn_seeded_test_expectation f μ ξ h.measurable A ε 0).congr
      (fun t ht => normalizedSeededExpectation_eq_seeded_test s μ ξ h.measurable A hε.le ht)
  have hD (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : HasDerivAt P (D t) t :=
    hasDerivAt_normalizedSeededExpectation s μ ξ h (relativeMomentBounds_of_envelope h) A hA hε.le ht
  have hM : ContinuousOn M (Icc (0 : ℝ) 1) := by
    exact (capMinimumMajorant_continuousOn (b:=1+ε) hε).comp
      (continuousOn_id.add continuousOn_const) (fun t ht => ⟨by linarith [ht.1],by linarith [ht.2]⟩)
  have hb (t : ℝ) (ht : t ∈ Ioo (0 : ℝ) 1) : |D t| ≤ a+M t := by
    have hx := (intrinsic_seeded_derivative_bounds μ ξ h (relativeMomentBounds_of_envelope h)
      hp hunit A hA s hband hC₀ hκp ht (hc t ht)).1
    have hfrac : a*t/(t+ε) ≤ a := (div_le_iff₀ (by linarith [ht.1] : 0<t+ε)).2 (by nlinarith [mul_nonneg ha hε.le])
    have hcub : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a := by
      have hcx : |-(t/(3*(seededNormalization ε)^3))*normalizedSeededCubicTerm s μ ξ A ε t| ≤ a*t/(t+ε) := by
        simpa only [abs_mul,abs_neg,a] using hx
      exact hcx.trans hfrac
    have hfour := cap_normalizedSeededFourthRemainder_majorant μ ξ h hp hunit A hA s hband hband16 hC₀ hκp ht (hc t ht)
    exact (abs_add _ _).trans (add_le_add hcub hfour)
  have htime := cap_time_increment_le hP hD hM hb
  have hpR : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hpPos : 0 < (p : ℝ) := zero_lt_one.trans_le hpR
  have hlogp : Real.log (p : ℝ) ≤ L := by
    dsimp only [L,dimensionLog]
    rw [Real.log_mul (Real.exp_ne_zero _) hpPos.ne',Real.log_exp]
    linarith
  have hlogS : max (Real.log (Sh/(Ah*Real.sqrt ε))) 0 ≤ 4*L := by
    dsimp only [Sh,Ah,ε]
    rw [cap_seed_single_ratio hδ hκp hLp s.bandwidth_pos]
    exact cap_single_ratio_log_le hpR hpR le_rfl hκ hL hlogp
  have hlogB : max (Real.log (Bh/Ah)) 0 ≤ 6*L := by
    dsimp only [Bh,Ah]
    rw [cap_seed_pair_ratio hδ hκp hLp s.bandwidth_pos]
    exact cap_pair_ratio_log_le hpR hpR le_rfl hκ hL hlogp
  have hi := cap_integral_majorant_bound hε hsmall
    (show 0<Ah by dsimp only [Ah]; positivity)
    (show 0<Sh by dsimp only [Sh]; positivity)
    (show 0<Bh by dsimp only [Bh]; positivity)
    (capSeededComparisonConstant_pos hC₀).le hL hlogS hlogB
  have haC : a ≤ C*(κ*L)*δ := by
    have hh := mul_le_mul_of_nonneg_right (le_max_left (intrinsicSeededDerivativeConstant C₀)
      capSeededComplementaryConstant) (show 0 ≤ δ*(L*κ) by positivity)
    convert hh using 1 <;> dsimp only [a,C,capSeededComparisonConstant] <;> ring
  apply htime.trans
  apply (add_le_add haC hi).trans
  have hC : 0 ≤ C := (capSeededComparisonConstant_pos hC₀).le
  have hfirst : C*(κ*L)*δ ≤ 38*C*(κ*L)*δ := by
    have hz : 0 ≤ C*(κ*L)*δ := by positivity
    nlinarith only [hz]
  calc
    C*(κ*L)*δ+38*C*Ah*min (1+Real.log (1/ε)) L ≤
        38*C*(κ*L)*δ+38*C*Ah*min (1+Real.log (1/ε)) L := add_le_add_right hfirst _
    _ = _ := by dsimp only [Ah,C,capSeededTimeComparisonConstant]; ring

end
end RectangleCLTArxivV1
