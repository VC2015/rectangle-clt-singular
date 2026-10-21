import RectangleCLTCompanion.RectangleDistance
import RectangleCLTCompanion.LowerProductArray
import RectangleCLTCompanion.LowerSkewScales
import RectangleCLT.CombinedMain

/-! The actual supremum distance for the lower construction. A proved
identity-covariance CLT bounds its ratio from above; hence the real liminf
in the lower-scale statement is not relying on an unbounded-real convention. -/

open MeasureTheory Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

def lowerConstructionDistance (B : ℝ) (n p : ℕ) : ℝ :=
  rectangleDistance (lowerArrayLaw B n p)
    (sumVector (lowerNormalizedRows (n := n) (p := p))) 1

theorem lowerConstructionDistance_nonneg (B : ℝ) (n p : ℕ) :
    0 ≤ lowerConstructionDistance B n p :=
  rectangleDistance_nonneg _ _ _

theorem lowerConstructionDistance_le_one (B : ℝ) (n p : ℕ) :
    lowerConstructionDistance B n p ≤ 1 :=
  rectangleDistance_le_one _ _ _

theorem lower_rectangleError_le_distance (B : ℝ) (n p : ℕ) (R : Rect p) :
    rectangleError (lowerArrayLaw B n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p))) 1 R ≤
        lowerConstructionDistance B n p :=
  rectangleError_le_rectangleDistance _ _ _ R

theorem fullEigenvalue_identity {p : ℕ} (hp : 1 ≤ p) :
    fullEigenvalue (1 : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  have hquad (v : Vector p) : matrixQuadratic (1 : Matrix (Fin p) (Fin p) ℝ) v =
      vectorNormSq v := by
    simp [matrixQuadratic, vectorNormSq, Matrix.one_apply, mul_ite, ite_mul, pow_two]
  apply le_antisymm
  · exact localEigenvalue_le_one (by omega) (by omega)
      (fun v => by rw [hquad]; exact vectorNormSq_nonneg v) (by intro j; simp)
  · apply le_fullEigenvalue (by omega)
    intro v
    rw [hquad, one_mul]

/-- The genuine identity-covariance CLT, applied uniformly over every
rectangle in the actual construction. -/
theorem lowerConstructionDistance_le {B : ℝ} (hB : 1 ≤ B)
    {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    lowerConstructionDistance B n p ≤
      (3 * combinedCLTConstant) *
        (B / Real.sqrt n * dimensionLog p * Real.sqrt (dimensionLog p)) := by
  let μ := lowerArrayLaw B n p
  let ξ := lowerNormalizedRows (n := n) (p := p)
  have hdata := lowerNormalizedRows_boundedIndependent hB n p
  have hcov : covariance μ (sumVector ξ) = 1 := lowerNormalizedRows_covariance hB hn
  have hunit : ∀ j, covariance μ (sumVector ξ) j j = 1 := by
    intro j
    rw [hcov]
    simp
  have hfull : fullEigenvalue (covariance μ (sumVector ξ)) = 1 := by
    rw [hcov]
    exact fullEigenvalue_identity hp
  apply rectangleDistance_le
  intro R
  have hh := aronowLopattoRectangleCLT μ hp hn ξ hdata hunit 1
    (by rw [hcov]; simp) (by rw [hfull]; norm_num) R
  rw [hfull, div_one] at hh
  have hC : 0 ≤ combinedCLTConstant := zero_le_one.trans combinedCLTConstant_ge_one
  exact hh.trans (mul_le_mul_of_nonneg_left (min_le_right 1 _)
    (by positivity : 0 ≤ 3 * combinedCLTConstant))

theorem lowerSkewRate_pos {B : ℝ} (hB : 0 < B) {p n : ℕ}
    (hp : 2 ≤ p) (hn : 1 ≤ n) : 0 < lowerSkewRate B p n := by
  unfold lowerSkewRate
  exact div_pos (mul_pos hB (Real.rpow_pos_of_pos
    (Real.log_pos (by exact_mod_cast hp)) _))
    (Real.sqrt_pos.mpr (by exact_mod_cast hn))

/-- The supremum error divided by the paper's skew scale is eventually
bounded above, without assuming that the scale has a limit. -/
theorem lowerConstructionDistance_ratio_eventually_le
    {B : ℕ → ℝ} {p : ℕ → ℕ} (hB : ∀ n, 2 ≤ B n)
    (hp : Tendsto p atTop atTop) :
    ∀ᶠ n in atTop,
      lowerConstructionDistance (B n) n (p n) / lowerSkewRate (B n) (p n) n ≤
        12 * combinedCLTConstant := by
  have hlog : Tendsto (fun n => Real.log (p n : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop.comp hp)
  filter_upwards [hlog.eventually (eventually_ge_atTop 1),
    hp.eventually (eventually_ge_atTop 2), eventually_ge_atTop 1] with n hlogn hpn hn
  have hlog0 : 0 ≤ Real.log (p n : ℝ) := zero_le_one.trans hlogn
  have hL : dimensionLog (p n) = 1 + Real.log (p n : ℝ) := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _)
      (by exact_mod_cast (Nat.ne_of_gt (show 0 < p n by omega))), Real.log_exp]
  have hLle : dimensionLog (p n) ≤ 2 * Real.log (p n : ℝ) := by rw [hL]; linarith
  have hsqrt : Real.sqrt (dimensionLog (p n)) ≤ 2 * Real.sqrt (Real.log (p n : ℝ)) := by
    apply (Real.sqrt_le_iff).mpr
    refine ⟨by positivity, ?_⟩
    nlinarith [Real.sq_sqrt hlog0]
  have hprod : dimensionLog (p n) * Real.sqrt (dimensionLog (p n)) ≤
      4 * (Real.log (p n : ℝ)) ^ (3 / 2 : ℝ) := by
    have hh := mul_le_mul hLle hsqrt (Real.sqrt_nonneg _) (by positivity : 0 ≤ 2 * Real.log (p n : ℝ))
    rw [lower_log_power_three_half hlog0]
    nlinarith only [hh]
  have hBn : 1 ≤ B n := by linarith only [hB n]
  have hN : 0 ≤ B n / Real.sqrt n := div_nonneg (by linarith only [hB n]) (Real.sqrt_nonneg _)
  have hC : 0 ≤ 3 * combinedCLTConstant := by
    have hh := combinedCLTConstant_ge_one
    positivity
  have hupper : lowerConstructionDistance (B n) n (p n) ≤
      (12 * combinedCLTConstant) * lowerSkewRate (B n) (p n) n := by
    apply (lowerConstructionDistance_le hBn hn (by omega)).trans
    have hh := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hprod hN) hC
    convert hh using 1 <;> (try simp only [lowerSkewRate]) <;> ring
  exact (div_le_iff₀ (lowerSkewRate_pos (by linarith only [hB n]) hpn hn)).mpr hupper

theorem lowerConstructionDistance_ratio_isBoundedUnder
    {B : ℕ → ℝ} {p : ℕ → ℕ} (hB : ∀ n, 2 ≤ B n)
    (hp : Tendsto p atTop atTop) :
    IsBoundedUnder (· ≤ ·) atTop
      (fun n => lowerConstructionDistance (B n) n (p n) / lowerSkewRate (B n) (p n) n) :=
  ⟨12 * combinedCLTConstant, lowerConstructionDistance_ratio_eventually_le hB hp⟩

end

end RectangleCLT.Companion
