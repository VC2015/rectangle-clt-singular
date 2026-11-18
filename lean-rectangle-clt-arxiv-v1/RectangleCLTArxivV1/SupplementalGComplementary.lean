import RectangleCLTArxivV1.SupplementalGFiniteClosure
import RectangleCLTArxivV1.SupplementalGSeededPairTransfer
import RectangleCLTArxivV1.SupplementalGSeededVariableLaw

/-! Actual complementary bounds for the calibrated fourth remainder.
The single/pair decomposition, both pair estimates, every copy/base law,
and the scalar-kernel connection are proved in the imported support files. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_seeded_pair_contribution_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f g : Face p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
      capComplementaryConstant*Real.sqrt (r : ℝ)*δ^2/(s.bandwidth*seededSplitGaussianScale ε t) := by
  let ρ := faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hu := capRectangularFactorNormal_unit A hdiag f
  have hv := capRectangularFactorNormal_unit A hdiag g
  have hσ : 0 < seededSplitGaussianScale ε t := seededSplitGaussianScale_pos hpos
  have hC := capComplementaryConstant_nonneg
  by_cases hρ : ρ^2 < 1
  · have hfg : f ≠ g := by
      intro he
      subst g
      have hself : faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A f)=1 := by
        simpa only [faceDot,vectorNormSq,pow_two] using hu
      change (faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A f))^2 < 1 at hρ
      rw [hself] at hρ
      norm_num at hρ
    have hν : 0 < Real.sqrt (1-ρ^2) := Real.sqrt_pos.mpr (by linarith)
    have hs : |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
        capSmallPairComplementaryConstant*δ^2*Real.sqrt (1-ρ^2)/s.bandwidth^2 := by
      rw [cap_seeded_pair_contribution_eq_second h A hA hunit s x f g hfg hε ht hpos freshY freshW freshShift]
      exact cap_seeded_small_angle_pattern_bound h A hA hunit s hband x f g hρ hε ht hθ freshY freshW freshShift
    have hl : |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
        capLargePairComplementaryConstant*δ^2*(r : ℝ)/(Real.sqrt (1-ρ^2)*(seededSplitGaussianScale ε t)^2) :=
      cap_seeded_pair_pattern_bound h A hA hunit s hband x f g hρ hε ht hθ hpos freshY freshW freshShift
    have hs' : |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
        capComplementaryConstant*δ^2*Real.sqrt (1-ρ^2)/s.bandwidth^2 := hs.trans (by
      gcongr
      exact capComplementaryConstant_ge_smallPair)
    have hl' : |capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
        capComplementaryConstant*(r : ℝ)*δ^2/(Real.sqrt (1-ρ^2)*(seededSplitGaussianScale ε t)^2) := by
      apply hl.trans
      calc
        _ ≤ capComplementaryConstant*δ^2*(r : ℝ)/(Real.sqrt (1-ρ^2)*(seededSplitGaussianScale ε t)^2) := by
          gcongr
          exact capComplementaryConstant_ge_largePair
        _ = _ := by ring
    exact cap_pair_geometric_mean capComplementaryConstant_nonneg (Nat.cast_nonneg r)
      s.bandwidth_pos hν hσ hs' hl'
  · have hρle : |ρ| ≤ 1 := abs_dotProduct_unit_le_one _ _ hu hv
    have hparallel : |ρ|=1 := by nlinarith [sq_abs ρ,abs_nonneg ρ]
    rw [cap_seeded_pair_parallel_zero h A hA hunit s x ε t θ f g hparallel freshY freshW freshShift,abs_zero]
    exact div_nonneg (mul_nonneg (mul_nonneg hC (Real.sqrt_nonneg _)) (sq_nonneg δ))
      (mul_nonneg s.bandwidth_pos.le hσ.le)

theorem cap_seeded_fourth_pattern_complementary_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |capSeededFourthPattern s μ ξ A x ε t θ freshY freshW freshShift| ≤ capComplementaryConstant*
      ((s.faces.card : ℝ)*(r : ℝ)*δ^2/(seededSplitGaussianScale ε t)^3+
        (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2/(s.bandwidth*seededSplitGaussianScale ε t)) := by
  have hσ : 0 < seededSplitGaussianScale ε t := seededSplitGaussianScale_pos hpos
  have hS := cap_seeded_single_sum_bound h A hA hunit hr s hband x hε ht hθ hpos freshY freshW freshShift
  have hS' : |∑ f, capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift| ≤
      (s.faces.card : ℝ)*(capComplementaryConstant*δ^2*(r : ℝ)/(seededSplitGaussianScale ε t)^3) := hS.trans (by
    gcongr
    exact capComplementaryConstant_ge_single)
  have hP : |∑ f, ∑ g, capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift| ≤
      (s.faces.card : ℝ)^2*(capComplementaryConstant*Real.sqrt (r : ℝ)*δ^2/(s.bandwidth*seededSplitGaussianScale ε t)) := by
    apply cap_sum_pair_faces_abs_le
    · intro f g hfg
      exact cap_seeded_pair_inactive s μ ξ A x ε t θ f g hfg freshY freshW freshShift
    · intro f _ g _
      exact cap_seeded_pair_contribution_bound h A hA hunit s hband x f g hε ht hθ hpos freshY freshW freshShift
  rw [cap_seeded_fourth_pattern_decomposition h A hA hunit s x ht hpos freshY freshW freshShift]
  apply (abs_add _ _).trans
  exact (add_le_add hS' hP).trans_eq (by ring)

/-- The original seeded fourth remainder has the complementary bound, before
rewriting the positive Gaussian half-scale into t+ε. -/
theorem cap_seededFourthRemainder_sigma_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |seededFourthRemainder s μ ξ C x ε t| ≤ 3*capComplementaryConstant*
      ((s.faces.card : ℝ)*(r : ℝ)*δ^2/(seededSplitGaussianScale ε t)^3+
        (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2/(s.bandwidth*seededSplitGaussianScale ε t)) := by
  have hpos : 0 < t+ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hσ : 0 < seededSplitGaussianScale ε t := seededSplitGaussianScale_pos hpos
  have hh := s.bandwidth_pos
  have hconst := capComplementaryConstant_nonneg
  let B := capComplementaryConstant*((s.faces.card : ℝ)*(r : ℝ)*δ^2/(seededSplitGaussianScale ε t)^3+
    (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2/(s.bandwidth*seededSplitGaussianScale ε t))
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  let F (a b c : Bool) (θ : ℝ) := capSeededFourthPattern s μ ξ A x ε t θ a b c
  have hb (θ : ℝ) (hθ : θ ∈ Set.Icc (0 : ℝ) 1) (a b c : Bool) : |F a b c θ| ≤ B :=
    cap_seeded_fourth_pattern_complementary_bound h A hA hunit hr s hband x hε
      ⟨ht.1.le,ht.2.le⟩ hθ hpos a b c
  have hIA : |∫ θ in (0 : ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ| ≤ B := by
    apply abs_unit_intervalIntegral_le_const
    intro θ hθ
    rw [abs_mul]
    exact (mul_le_mul (calibrated_fourth_kernel_abs_le_one ⟨ht.1.le,ht.2.le⟩ hθ)
      (hb θ hθ false false false) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIB : |∫ θ in (0 : ℝ)..1, (1-θ)*F true true true θ| ≤ B := by
    apply abs_unit_intervalIntegral_le_const
    intro θ hθ
    rw [abs_mul]
    have hθ' : |1-θ| ≤ 1 := by rw [abs_le]; constructor <;> linarith [hθ.1,hθ.2]
    exact (mul_le_mul hθ' (hb θ hθ true true true) (abs_nonneg _) zero_le_one).trans_eq (one_mul _)
  have hIC : |∫ θ in (0 : ℝ)..1, F false true true θ| ≤ B :=
    abs_unit_intervalIntegral_le_const (fun θ hθ => hb θ hθ false true true)
  have hbcoef : |(1-t)/2| ≤ 1 := by rw [abs_le]; constructor <;> linarith [ht.1,ht.2]
  have hccoef : |t*(1-t)/(3*(1+t))| ≤ 1 := by
    rw [abs_of_nonneg (div_nonneg (mul_nonneg ht.1.le (by linarith [ht.2])) (by linarith [ht.1]))]
    apply (div_le_one (by linarith [ht.1] : 0 < 3*(1+t))).mpr
    nlinarith [sq_nonneg t]
  rw [cap_seededFourthRemainder_eq_patterns s μ ξ h A C hA hC x ht.1.le ht.2.le hpos]
  change |((∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ)+
      (1-t)/2*(∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ))+
      (t*(1-t)/(3*(1+t)))*(∫ θ in (0:ℝ)..1, F false true true θ)| ≤ _
  calc
    _ ≤ |∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ| +
        |(1-t)/2| *|∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ| +
        |t*(1-t)/(3*(1+t))| *|∫ θ in (0:ℝ)..1, F false true true θ| := by
      simpa only [abs_mul] using
        (abs_add ((∫ θ in (0:ℝ)..1, seededFourthKernel (thinningScale t) (calibratedEta t) θ*F false false false θ)+
          (1-t)/2*(∫ θ in (0:ℝ)..1, (1-θ)*F true true true θ))
          ((t*(1-t)/(3*(1+t)))*(∫ θ in (0:ℝ)..1, F false true true θ))).trans
            (add_le_add_right (abs_add _ _) _)
    _ ≤ B+1*B+1*B := add_le_add
      (add_le_add hIA (mul_le_mul hbcoef hIB (abs_nonneg _) zero_le_one))
      (mul_le_mul hccoef hIC (abs_nonneg _) zero_le_one)
    _ = _ := by dsimp only [B]; ring

def capSeededComplementaryConstant : ℝ := 12*capComplementaryConstant

theorem capSeededComplementaryConstant_nonneg : 0 ≤ capSeededComplementaryConstant :=
  mul_nonneg (by norm_num) capComplementaryConstant_nonneg

theorem cap_seededScale_linear_rate {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (hpos : 0 < t+ε) : 1/seededSplitGaussianScale ε t ≤ 2/Real.sqrt (t+ε) := by
  have hb : 0 < seededSplitGaussianScale ε t := seededSplitGaussianScale_pos hpos
  have ha : 0 < Real.sqrt (t+ε) := Real.sqrt_pos.mpr hpos
  have hb2 := seededSplitGaussianScale_sq hε ht
  have ha2 := Real.sq_sqrt hpos.le
  apply (div_le_div_iff₀ hb ha).mpr
  simp only [one_mul]
  nlinarith [sq_nonneg (Real.sqrt (t+ε)-2*seededSplitGaussianScale ε t)]

/-- Supplemental complementary bound for the literal seededFourthRemainder.
The face count is the actual active count and r is the rectangular covariance
factor dimension. No concentration, operator-budget, or remainder premise occurs. -/
theorem cap_seededFourthRemainder_complementary_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (C : Matrix (Fin p) (Fin p) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ)) (hC : C*C.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (x : Vector p) {h₀ ε t : ℝ} (hh₀ : 0 < h₀)
    (hwidth : h₀ ≤ s.bandwidth) (hband : 16*δ ≤ h₀)
    (hε : 0 ≤ ε) (ht : t ∈ Set.Ioo (0 : ℝ) 1) :
    |seededFourthRemainder s μ ξ C x ε t| ≤ capSeededComplementaryConstant*
      ((s.faces.card : ℝ)*(r : ℝ)*δ^2/((t+ε)*Real.sqrt (t+ε))+
        (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2/(h₀*Real.sqrt (t+ε))) := by
  have hpos : 0 < t+ε := add_pos_of_pos_of_nonneg ht.1 hε
  have hσ : 0 < seededSplitGaussianScale ε t := seededSplitGaussianScale_pos hpos
  have hsqrt : 0 < Real.sqrt (t+ε) := Real.sqrt_pos.mpr hpos
  let U := (s.faces.card : ℝ)*(r : ℝ)*δ^2
  let V := (s.faces.card : ℝ)^2*Real.sqrt (r : ℝ)*δ^2
  have hU : 0 ≤ U := by dsimp only [U]; positivity
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  have h1 : U/(seededSplitGaussianScale ε t)^3 ≤ 4*(U/((t+ε)*Real.sqrt (t+ε))) := by
    calc
      _ = U*(1/(seededSplitGaussianScale ε t)^3) := by ring
      _ ≤ U*(4/((t+ε)*Real.sqrt (t+ε))) :=
        mul_le_mul_of_nonneg_left (cap_seededScale_cubic_rate hε ht.1.le hpos) hU
      _ = _ := by ring
  have h2 : V/(s.bandwidth*seededSplitGaussianScale ε t) ≤ 4*(V/(h₀*Real.sqrt (t+ε))) := by
    calc
      _ ≤ V/(h₀*seededSplitGaussianScale ε t) :=
        div_le_div_of_nonneg_left hV (mul_pos hh₀ hσ) (mul_le_mul_of_nonneg_right hwidth hσ.le)
      _ = (V/h₀)*(1/seededSplitGaussianScale ε t) := by ring
      _ ≤ (V/h₀)*(2/Real.sqrt (t+ε)) :=
        mul_le_mul_of_nonneg_left (cap_seededScale_linear_rate hε ht.1.le hpos) (div_nonneg hV hh₀.le)
      _ = 2*(V/(h₀*Real.sqrt (t+ε))) := by ring
      _ ≤ 4*(V/(h₀*Real.sqrt (t+ε))) :=
        mul_le_mul_of_nonneg_right (by norm_num : (2 : ℝ)≤4) (by positivity)
  have hsum : U/(seededSplitGaussianScale ε t)^3+V/(s.bandwidth*seededSplitGaussianScale ε t) ≤
      4*(U/((t+ε)*Real.sqrt (t+ε))+V/(h₀*Real.sqrt (t+ε))) := (add_le_add h1 h2).trans_eq (by ring)
  have hb := cap_seededFourthRemainder_sigma_bound h A C hA hC hunit hr s (hband.trans hwidth) x hε ht
  apply hb.trans
  have ht' := mul_le_mul_of_nonneg_left hsum (mul_nonneg (by norm_num : (0 : ℝ)≤3) capComplementaryConstant_nonneg)
  exact ht'.trans_eq (by dsimp only [U,V,capSeededComplementaryConstant]; ring)

end
end RectangleCLTArxivV1
