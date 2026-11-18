import RectangleCLTArxivV1.SubexponentialIntrinsicTransfer
import RectangleCLTArxivV1.SubexponentialIntrinsicResidual
import RectangleCLTCompanion.SubexponentialReduction

/-! Genuine clipping and joint-Gaussian restoration with intrinsic width. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators Matrix

noncomputable section

theorem subexponential_clipping_reduction_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K B : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K)
    (hp : 1 ≤ p) (hn : 1 ≤ n)
    (hunit : ∀ j, covariance μ (normalizedObservationSum X) j j = 1)
    (A AT : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (hAT : AT * AT.transpose =
      covariance μ (sumVector (normalizedClippedRows μ X (K * (4 * dimensionLog n)))))
    (hcompare : ∀ S : Rect p,
      rectangleError μ (sumVector (normalizedClippedRows μ X (K * (4 * dimensionLog n)))) AT S ≤ B)
    (S : Rect p) :
    rectangleError μ (normalizedObservationSum X) A S ≤
      B + 2 *
        (printedResidualRadius n p K +
          gaussianCouplingRadius n p K (4 * dimensionLog n)) *
        gaussianMaximumMean A + 1 / (n : ℝ) := by
  classical
  let u := 4 * dimensionLog n
  have hu : 0 ≤ u := mul_nonneg (by norm_num)
    (zero_le_one.trans (log_exp_mul_nat_ge_one hn))
  let W := normalizedObservationSum X
  let WT := sumVector (normalizedClippedRows μ X (K * u))
  let V := sumVector (normalizedResidualRows μ X (K * u))
  let Q := jointSecondMoment μ WT V
  let τ := 2 * K * Real.exp (-u / 2)
  let s := Real.log (4 * (n : ℝ) * (p : ℝ))
  let r₁ := printedResidualRadius n p K
  let r₂ := gaussianCouplingRadius n p K u
  have hK : 0 < K := lt_of_lt_of_le zero_lt_one h.one_le_scale
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hn0 : (n : ℝ) ≠ 0 := ne_of_gt (by linarith)
  have hs : 0 < s := by
    apply Real.log_pos
    have hh := one_le_mul_of_one_le_of_one_le hnR hpR
    nlinarith
  have hτ : 0 < τ := by dsimp only [τ]; positivity
  have hL2 : ∀ a, MemLp (fun ω => jointValue WT V ω a) (2 : ENNReal) μ := by
    intro a
    cases a with
    | inl j => exact normalizedClippedSum_coordinate_memLp_two h hu j
    | inr j => exact normalizedResidualSum_coordinate_memLp_two h hu j
  have hmean : ∀ a, (∫ ω, jointValue WT V ω a ∂μ) = 0 := by
    intro a
    cases a with
    | inl j => exact normalizedClippedSum_coordinate_centered h hu j
    | inr j => exact normalizedResidualSum_coordinate_centered h hu j
  have hQ : Q.PosSemidef := jointSecondMoment_posSemidef hL2
  have hblock11 : covarianceBlock11 Q = covariance μ WT :=
    jointSecondMoment_block11 μ WT V hmean
  have hblock22 : covarianceBlock22 Q = covariance μ V :=
    jointSecondMoment_block22 μ WT V hmean
  have hdecompose (ω : Ω) : W ω = WT ω + V ω :=
    normalizedObservationSum_eq_clipped_add_residual h hu ω
  have hsum : W = WT + V := funext hdecompose
  have hrestore : restoredCovariance Q = covariance μ W := by
    rw [hsum]
    exact jointSecondMoment_restoredCovariance WT V hL2 hmean
  obtain ⟨L, R, hLL, hLR, hRL, hRR, hLlaw, hZlaw⟩ :=
    jointRestoration_gaussianCoupling_exists Q hQ AT A
      (hAT.trans hblock11.symm) (hA.trans hrestore.symm)
  let ν := standardGaussian (p + p)
  let Z := (L + R).mulVec
  let ZT := L.mulVec
  have hZ : Measurable Z := measurable_rectangular_mulVec (L + R)
  have hZT : Measurable ZT := measurable_rectangular_mulVec L
  have hW : Measurable W := by
    change Measurable (fun ω => (Real.sqrt (n : ℝ))⁻¹ • ∑ i, X i ω)
    exact measurable_const.smul (Finset.measurable_sum _ (fun i _ => h.measurable i))
  have hdiag : ∀ j, (A * A.transpose) j j = 1 := by
    rw [hA]
    exact hunit
  have hcomp : ∀ T : Rect p, |μ.real (WT ⁻¹' T.carrier) - ν.real (ZT ⁻¹' T.carrier)| ≤ B := by
    intro T
    rw [probability_eq_gaussian_of_map_eq ν ZT hZT AT hLlaw T]
    exact hcompare T
  have hbadW : μ.real {ω | r₁ < ‖W ω - WT ω‖} ≤ 1 / (2 * (n : ℝ)) := by
    have hd (ω : Ω) : W ω - WT ω = V ω := by rw [hdecompose]; abel
    simp_rw [hd]
    exact (normalized_residual_tail_printed h hn hp).trans
      (one_div_le_one_div_of_le (show 0 < 2*(n:ℝ) by positivity) (by nlinarith))
  have hτsq : τ ^ 2 = 4 * K ^ 2 * Real.exp (-u) := by
    have he : Real.exp (-u / 2) ^ 2 = Real.exp (-u) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring
    dsimp only [τ]
    rw [mul_pow, mul_pow, he]
    ring
  have hrows (j : Fin p) : (∑ k, R j k ^ 2) ≤ τ ^ 2 := by
    have hgram : (R * R.transpose) j j = covariance μ V j j := by
      rw [hRR, hblock22]
    calc
      _ = (R * R.transpose) j j := by
        simp only [Matrix.mul_apply, Matrix.transpose_apply, pow_two]
      _ = covariance μ V j j := hgram
      _ ≤ 4 * K ^ 2 * Real.exp (-u) :=
        normalizedResidualRows_sum_covariance_diagonal_le h hu hn j
      _ = τ ^ 2 := hτsq.symm
  have hbadZ : ν.real {z | r₂ < ‖ZT z - Z z‖} ≤ 1 / (2 * (n : ℝ)) := by
    have hd (z : Vector (p + p)) : ZT z - Z z = -(R.mulVec z) := by
      dsimp only [ZT, Z]
      rw [Matrix.add_mulVec]
      abel
    simp_rw [hd, norm_neg]
    exact standardGaussian_rectangular_norm_tail_log R hp hn hτ.le hrows
  have hr : 0 < r₁ + r₂ := by
    dsimp only [r₁, r₂, printedResidualRadius, subexponentialUnionLog, gaussianCouplingRadius]
    have hlogs : 0 < Real.log (4 * (n : ℝ) * (p : ℝ)) := hs
    positivity
  have htransfer := rectangleError_le_of_two_couplings_intrinsic hp μ ν W WT Z ZT
    hW hZ A hZlaw hdiag hr hcomp hbadW hbadZ S
  have heps : 1 / (2 * (n : ℝ)) + 1 / (2 * (n : ℝ)) = 1 / (n : ℝ) := by
    field_simp [hn0]
    ring
  simpa only [add_assoc, heps] using htransfer


end
end RectangleCLTArxivV1
