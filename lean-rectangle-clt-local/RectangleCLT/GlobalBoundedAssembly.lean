import RectangleCLT.Main
import RectangleCLT.GlobalCovariance
import RectangleCLT.CombinedOptimization
import RectangleCLT.GlobalDerivativeIntegration

/-! Assembly for the combined covariance alternatives. The generic bridges
in this file keep their concrete derivative-integral premise visible. The
full-dual averaged caps discharge that premise in `CombinedMain.lean`,
which proves the public combined CLT. -/

open MeasureTheory Set
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

theorem le_mul_combinedThirdCoefficient {D K b c a₃ : ℝ} (hK : 0 ≤ K)
    (hlocal : D ≤ K * (1 / (c * a₃)))
    (hglobal : 0 < b → D ≤ K * (1 / b ^ 2)) :
    D ≤ K * combinedThirdCoefficient b c a₃ := by
  unfold combinedThirdCoefficient
  split_ifs with hb
  · rw [mul_min_of_nonneg _ _ hK]
    exact le_min (hglobal hb) hlocal
  · exact hlocal

theorem combinedFourthCoefficient_sq {b c a₃ a₄ : ℝ}
    (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄) :
    combinedFourthCoefficient b c a₃ a₄ ^ 2 =
      if 0 < b then min (1 / b ^ 2) (1 / localFourthScale c a₃ a₄ ^ 2)
      else 1 / localFourthScale c a₃ a₄ ^ 2 := by
  have hd := localFourthScale_pos hc ha₃ ha₄
  unfold combinedFourthCoefficient
  split_ifs with hb
  · by_cases horder : 1 / b ≤ 1 / localFourthScale c a₃ a₄
    · rw [min_eq_left horder, min_eq_left]
      · simp only [div_pow, one_pow]
      · simpa only [div_pow, one_pow] using
          pow_le_pow_left₀ (one_div_nonneg.mpr hb.le) horder 2
    · have horder' := le_of_not_ge horder
      rw [min_eq_right horder', min_eq_right]
      · simp only [div_pow, one_pow]
      · simpa only [div_pow, one_pow] using
          pow_le_pow_left₀ (one_div_nonneg.mpr hd.le) horder' 2
  · simp only [div_pow, one_pow]

theorem le_mul_combinedFourthCoefficient_sq {D K b c a₃ a₄ : ℝ}
    (hK : 0 ≤ K) (hc : 0 < c) (ha₃ : 0 < a₃) (ha₄ : 0 < a₄)
    (hlocal : D ≤ K * (1 / localFourthScale c a₃ a₄ ^ 2))
    (hglobal : 0 < b → D ≤ K * (1 / b ^ 2)) :
    D ≤ K * combinedFourthCoefficient b c a₃ a₄ ^ 2 := by
  rw [combinedFourthCoefficient_sq hc ha₃ ha₄]
  split_ifs with hb
  · rw [mul_min_of_nonneg _ _ hK]
    exact le_min (hglobal hb) hlocal
  · exact hlocal

/-- The two literal derivative integrals sufficient for the combined master
bound. This is a proposition to be proved, and contains no probability
approximation conclusion. -/
def CombinedGaussianIntegralCaps (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ s : FaceSmoother p, 12 * δ ≤ s.bandwidth →
        s.bandwidth * Real.sqrt (dimensionLog p) ≤ 1 →
        let Q := covariance μ (sumVector ξ)
        ((∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
          C * dimensionLog p * Real.sqrt (dimensionLog p) *
            combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q)) ∧
        ((∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
          C * dimensionLog p * Real.sqrt (dimensionLog p) /
            s.bandwidth *
            combinedFourthCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q) ^ 2)

/-- The full-eigenvalue alternatives for the two actual derivative
integrals, restricted to positive full eigenvalue. -/
def FullGaussianIntegralCaps (C₃ C₄ : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      0 < fullEigenvalue (covariance μ (sumVector ξ)) →
      ∀ s : FaceSmoother p, 12 * δ ≤ s.bandwidth →
        s.bandwidth * Real.sqrt (dimensionLog p) ≤ 1 →
        let ν := fullEigenvalue (covariance μ (sumVector ξ))
        ((∫ t in (0 : ℝ)..1, t * s.sharpThirdAverage μ ξ A t) ≤
          C₃ * dimensionLog p * Real.sqrt (dimensionLog p) / ν) ∧
        ((∫ t in (0 : ℝ)..1, s.sharpFourthAverage μ ξ A δ t) ≤
          C₄ * dimensionLog p * Real.sqrt (dimensionLog p) / (ν * s.bandwidth))

def combinedIntegralAssemblyConstant (C₃ C₄ : ℝ) : ℝ :=
  2 * FaceSmoother.gaussianThirdConstant + 3 * gaussianFourthConstant + C₃ + C₄ + 1

theorem combinedIntegralAssemblyConstant_pos {C₃ C₄ : ℝ}
    (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄) :
    0 < combinedIntegralAssemblyConstant C₃ C₄ := by
  unfold combinedIntegralAssemblyConstant
  have h3 := FaceSmoother.gaussianThirdConstant_pos
  have h4 := gaussianFourthConstant_pos
  positivity

/-- Combine the proved local derivative integrals with supplied full
derivative integrals, choosing the alternative separately for each order.
The full-integral premise is explicit in this generic bridge. -/
theorem combinedGaussianIntegralCaps_of_full_integralCaps {C₃ C₄ : ℝ}
    (hC₃ : 0 ≤ C₃) (hC₄ : 0 ≤ C₄)
    (hfull : FullGaussianIntegralCaps.{u} C₃ C₄) :
    CombinedGaussianIntegralCaps.{u} (combinedIntegralAssemblyConstant C₃ C₄) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA s hband hsmall
  let Q := covariance μ (sumVector ξ)
  let L := dimensionLog p
  let K := combinedIntegralAssemblyConstant C₃ C₄
  have hK : 0 ≤ K := (combinedIntegralAssemblyConstant_pos hC₃ hC₄).le
  have hh := s.bandwidth_pos
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hc := hlocal.pairGap_pos hp
  have ha₃ := hlocal.a3_pos hp
  have ha₄ := hlocal.a4_pos
  have h3pos := FaceSmoother.gaussianThirdConstant_pos
  have h4pos := gaussianFourthConstant_pos
  have hK3local : 2 * FaceSmoother.gaussianThirdConstant ≤ K := by
    dsimp [K, combinedIntegralAssemblyConstant]
    linarith
  have hK4local : 3 * gaussianFourthConstant ≤ K := by
    dsimp [K, combinedIntegralAssemblyConstant]
    linarith
  have hK3full : C₃ ≤ K := by
    dsimp [K, combinedIntegralAssemblyConstant]
    linarith
  have hK4full : C₄ ≤ K := by
    dsimp [K, combinedIntegralAssemblyConstant]
    linarith
  have hsquare : fullCovarianceScale Q ^ 2 = fullEigenvalue Q :=
    fullCovarianceScale_sq (by omega) hlocal.posSemidef
  constructor
  · apply le_mul_combinedThirdCoefficient (K := K * L * Real.sqrt L) (by positivity)
    · have hb := s.integral_time_mul_sharpThirdAverage_le μ ξ hdata.measurable hp A hlocal hA
      calc
        _ ≤ (2 * FaceSmoother.gaussianThirdConstant) * L * Real.sqrt L /
            (pairGap Q * a3 Q) := by convert hb using 1 <;> ring
        _ ≤ K * L * Real.sqrt L / (pairGap Q * a3 Q) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK3local hL.le)
              (Real.sqrt_nonneg L)) (mul_pos hc ha₃).le
        _ = _ := by ring
    · intro hb
      have hν : 0 < fullEigenvalue Q := Real.sqrt_pos.mp hb
      have hglob := (hfull μ p n hp hn ξ δ A hdata hlocal hA hν s hband hsmall).1
      calc
        _ ≤ C₃ * L * Real.sqrt L / fullEigenvalue Q := hglob
        _ ≤ K * L * Real.sqrt L / fullEigenvalue Q :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK3full hL.le)
              (Real.sqrt_nonneg L)) hν.le
        _ = _ := by rw [← hsquare]; ring
  · apply le_mul_combinedFourthCoefficient_sq
      (K := K * L * Real.sqrt L / s.bandwidth) (by positivity) hc ha₃ ha₄
    · have hb := gaussianFourthIntegralCap_of_pointwise gaussianFourthConstant_ge_short
        gaussianFourthPointwiseCap μ p n hp hn ξ δ A hdata hlocal hA s hband hsmall
      rw [← localFourthScale_sq hc ha₃ ha₄] at hb
      calc
        _ ≤ (3 * gaussianFourthConstant) * L * Real.sqrt L /
            (s.bandwidth * localFourthScale (pairGap Q) (a3 Q) (a4 Q) ^ 2) := hb
        _ ≤ K * L * Real.sqrt L /
            (s.bandwidth * localFourthScale (pairGap Q) (a3 Q) (a4 Q) ^ 2) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK4local hL.le)
              (Real.sqrt_nonneg L)) (by positivity)
        _ = _ := by ring
    · intro hb
      have hν : 0 < fullEigenvalue Q := Real.sqrt_pos.mp hb
      have hglob := (hfull μ p n hp hn ξ δ A hdata hlocal hA hν s hband hsmall).2
      calc
        _ ≤ C₄ * L * Real.sqrt L / (fullEigenvalue Q * s.bandwidth) := hglob
        _ ≤ K * L * Real.sqrt L / (fullEigenvalue Q * s.bandwidth) :=
          div_le_div_of_nonneg_right
            (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hK4full hL.le)
              (Real.sqrt_nonneg L)) (mul_pos hν s.bandwidth_pos).le
        _ = _ := by rw [← hsquare]; ring

/-- The combined master proposition includes the singular case by omitting
the full-eigenvalue alternative in the coefficient definitions. -/
def CombinedMasterEstimate (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ (R : Rect p) (h : ℝ), 12 * δ ≤ h →
        let Q := covariance μ (sumVector ξ)
        rectangleError μ (sumVector ξ) A R ≤ C *
          (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) *
              combinedThirdCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) +
            gamma4 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) *
              combinedFourthCoefficient (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q) ^ 2 / h +
            Real.sqrt (dimensionLog p) / pairGap Q * h)

def combinedMasterAssemblyConstant (C : ℝ) : ℝ :=
  1 + 6 * C + (8 * Real.exp 4 + 4)

theorem combinedMasterAssemblyConstant_ge_one {C : ℝ} (hC : 0 ≤ C) :
    1 ≤ combinedMasterAssemblyConstant C := by
  unfold combinedMasterAssemblyConstant
  have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
  linarith

/-- Generic analytic assembly. Its derivative-integral premise remains
explicit until supplied by the actual full-dual and local estimates. -/
theorem combinedMasterEstimate_of_integralCaps {C : ℝ} (hC : 0 ≤ C)
    (hcap : CombinedGaussianIntegralCaps.{u} C) :
    CombinedMasterEstimate.{u} (combinedMasterAssemblyConstant C) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA R h hband
  let Q := covariance μ (sumVector ξ)
  let L := dimensionLog p
  let c := pairGap Q
  let b := fullCovarianceScale Q
  let β₃ := combinedThirdCoefficient b c (a3 Q)
  let β₄ := combinedFourthCoefficient b c (a3 Q) (a4 Q)
  have hc : 0 < c := hlocal.pairGap_pos hp
  have ha₃ := hlocal.a3_pos hp
  have ha₄ := hlocal.a4_pos
  have hδ : 0 < δ := hdata.delta_pos hp hlocal.unit_diagonal
  have hh : 0 < h := by linarith only [hband, hδ]
  have hL : 0 < L := lt_of_lt_of_le (by norm_num) (log_exp_mul_nat_ge_one hp)
  have hβ₃ : 0 ≤ β₃ := combinedThirdCoefficient_nonneg hc ha₃
  have hβ₄ : 0 ≤ β₄ := combinedFourthCoefficient_nonneg hc ha₃ ha₄
  have hγ₃ := gamma3_nonneg μ ξ
  have hγ₄ := gamma4_nonneg μ ξ
  let T₃ := gamma3 μ ξ * L * Real.sqrt L * β₃
  let T₄ := gamma4 μ ξ * L * Real.sqrt L * β₄ ^ 2 / h
  let T₀ := Real.sqrt L / c * h
  have hT₃ : 0 ≤ T₃ := by dsimp [T₃]; positivity
  have hT₄ : 0 ≤ T₄ := by dsimp [T₄]; positivity
  have hT₀ : 0 ≤ T₀ := by dsimp [T₀]; positivity
  change rectangleError μ (sumVector ξ) A R ≤
    combinedMasterAssemblyConstant C * (T₃ + T₄ + T₀)
  by_cases hsmall : h * Real.sqrt L ≤ 1
  · apply rectangleError_le_of_closedBox hp μ (sumVector ξ) hdata.measurable_sum A _ R
    intro lo hi
    let s := FaceSmoother.closedBox lo hi h hh
    obtain ⟨h3, h4⟩ := hcap μ p n hp hn ξ δ A hdata hlocal hA s hband hsmall
    have hgap := s.interpolation_smoother_gap_le_sharpTimeIntegrals μ ξ hdata A hA
    have hb : δ ≤ h := by linarith only [hband, hdata.delta_nonneg]
    have herr := hdata.closedBox_error_le_smoother_gap hp hlocal.unit_diagonal A hA hc lo hi hh hb
    have hI := add_le_add
      (mul_le_mul_of_nonneg_left h3 (div_nonneg (gamma3_nonneg μ ξ) (by norm_num : (0 : ℝ) ≤ 3)))
      (mul_le_mul_of_nonneg_left h4 (mul_nonneg (by norm_num : (0 : ℝ) ≤ 6) (gamma4_nonneg μ ξ)))
    have hraw := herr.trans (add_le_add_right (hgap.trans hI) _)
    have hraw' : rectangleError μ (sumVector ξ) A (Rect.closedBox lo hi) ≤
        (C / 3) * T₃ + (6 * C) * T₄ + (8 * Real.exp 4 + 4) * T₀ := by
      convert hraw using 1 <;>
        dsimp [s, FaceSmoother.closedBox, T₃, T₄, T₀, β₃, β₄, b, L, c, Q] <;> ring
    have hK3 : C / 3 ≤ combinedMasterAssemblyConstant C := by
      unfold combinedMasterAssemblyConstant
      have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
      linarith
    have hK4 : 6 * C ≤ combinedMasterAssemblyConstant C := by
      unfold combinedMasterAssemblyConstant
      have he : 0 ≤ (8 : ℝ) * Real.exp 4 + 4 := by positivity
      linarith
    have hK0 : 8 * Real.exp 4 + 4 ≤ combinedMasterAssemblyConstant C := by
      unfold combinedMasterAssemblyConstant
      linarith
    exact hraw'.trans ((add_le_add
      (add_le_add (mul_le_mul_of_nonneg_right hK3 hT₃)
        (mul_le_mul_of_nonneg_right hK4 hT₄))
      (mul_le_mul_of_nonneg_right hK0 hT₀)).trans_eq (by ring))
  · have hT₀one : 1 ≤ T₀ := by
      dsimp [T₀]
      rw [div_mul_eq_mul_div]
      apply (le_div_iff₀ hc).mpr
      have hc1 : c ≤ 1 := pairGap_le_one Q
      simp only [one_mul]
      linarith only [hc1, le_of_lt (lt_of_not_ge hsmall)]
    have hsum : 1 ≤ T₃ + T₄ + T₀ := by linarith only [hT₃, hT₄, hT₀one]
    exact (rectangleError_le_one μ (sumVector ξ) A R).trans
      (one_le_mul_of_one_le_of_one_le (combinedMasterAssemblyConstant_ge_one hC) hsum)

def CombinedRectangleCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ : ℝ) (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedIndependentHypotheses μ ξ δ →
      LocalCovarianceHypotheses (covariance μ (sumVector ξ)) →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p, let Q := covariance μ (sumVector ξ)
        rectangleError μ (sumVector ξ) A R ≤ C * min 1
          (combinedCoefficientRate δ (gamma3 μ ξ) (gamma4 μ ξ) (dimensionLog p)
            (fullCovarianceScale Q) (pairGap Q) (a3 Q) (a4 Q))

theorem combinedRectangleCLT_of_master {C : ℝ} (hC : 0 ≤ C)
    (hmaster : CombinedMasterEstimate.{u} C) :
    CombinedRectangleCLT.{u} (max 1 (13 * C)) := by
  intro Ω _ μ _ p n hp hn ξ δ A hdata hlocal hA R
  apply combined_rate_of_master
    (hdata.delta_pos hp hlocal.unit_diagonal)
    (gamma3_nonneg μ ξ) (gamma4_nonneg μ ξ) (log_exp_mul_nat_ge_one hp)
    (hlocal.pairGap_pos hp) (hlocal.a3_pos hp) hlocal.a4_pos hC
    (rectangleError_le_one μ (sumVector ξ) A R)
  exact hmaster μ p n hp hn ξ δ A hdata hlocal hA R

end

end RectangleCLT
