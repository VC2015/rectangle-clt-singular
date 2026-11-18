import RectangleCLTArxivV1.PairedCommonPointFourth
import RectangleCLTCompanion.SplitV4.GaussianRemainder

/-! Intrinsic averaging of the actual paired trapezoidal remainder.
The Gaussian average follows the common-point fourth contraction and the
segment integral is exchanged only under genuine bounded domination. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators Interval
noncomputable section
set_option maxHeartbeats 1000000

private theorem scaled_factor_diagonal {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {t : ℝ} (ht1 : t ≤ 1) (j : Fin p) :
    ((Real.sqrt (1 - t) • A) * (Real.sqrt (1 - t) • A).transpose) j j = 1 - t := by
  calc
    _ = (Real.sqrt (1 - t)) ^ 2 * (A * A.transpose) j j := by
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.smul_apply, smul_eq_mul,
        Finset.mul_sum]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    _ = _ := by rw [hdiag, mul_one, Real.sq_sqrt (sub_nonneg.mpr ht1)]

private theorem integral_scaledGaussian_product
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Matrix (Fin p) (Fin p) ℝ) (b : ℝ)
    (K : Vector p × Ω → ℝ) (hK : Measurable K) (C : ℝ) (hbound : ∀ z, ‖K z‖ ≤ C) :
    (∫ z : Vector p × Ω, K (b • z.1, z.2) ∂(gaussianLaw A).prod μ) =
      ∫ z, K z ∂(gaussianLaw (b • A)).prod μ := by
  have hiR : Integrable K ((gaussianLaw (b • A)).prod μ) :=
    (integrable_const C).mono' hK.aestronglyMeasurable (ae_of_all _ hbound)
  have hiL : Integrable (fun z : Vector p × Ω => K (b • z.1, z.2))
      ((gaussianLaw A).prod μ) := by
    apply (integrable_const C).mono'
      (hK.comp ((measurable_const.smul measurable_fst).prodMk measurable_snd)).aestronglyMeasurable
    exact ae_of_all _ (fun z => hbound (b • z.1, z.2))
  rw [integral_prod_symm _ hiL, integral_prod_symm _ hiR]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => FaceSmoother.integral_gaussianLaw_smul A b
    (fun g => K (g, ω)) (hK.comp (measurable_id.prodMk measurable_const)))

private theorem fourth_eval_bound {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (Y : Fin n → Ω → Vector p)
    (hYnorm : ∀ i ω, ‖Y i ω‖ ≤ s.bandwidth) (x : Vector p) (i : Fin n) (ω : Ω) :
    ‖(smootherC4Test s).fourthDiagonal x (Y i ω)‖ ≤
      (smootherC4Test s).bound * s.bandwidth ^ 4 :=
  ((smootherC4Test s).norm_fourthDiagonal_le x (Y i ω)).trans
    (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (norm_nonneg _) (hYnorm i ω) 4) (smootherC4Test s).bound_nonneg)

private theorem gaussian_fourth_segment_sum_abs_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (R : Ω → Vector p) (hR : Measurable R)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hYnorm : ∀ i ω, ‖Y i ω‖ ≤ s.bandwidth)
    (hQ : Integrable (fun ω => coordinateFourthBudget (fun i => Y i ω)) μ)
    {t r : ℝ} (_ht : 0 ≤ t) (ht1 : t < 1) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    (∫ z : Vector p × Ω, ∑ i,
      |(smootherC4Test s).fourthDiagonal
        ((Real.sqrt (1 - t) • z.1 + R z.2) + (Real.sqrt t * r) • Y i z.2) (Y i z.2)|
        ∂(gaussianLaw A).prod μ) ≤
      ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
        (gaussianMaximumMean A / Real.sqrt (1-t)) / s.bandwidth^3) *
          (∫ ω, coordinateFourthBudget (fun i => Y i ω) ∂μ) := by
  let Z : Fin n → Ω → Vector p := fun i ω => (Real.sqrt t * r) • Y i ω
  have hZ (i : Fin n) : Measurable (Z i) := measurable_const.smul (hY i)
  have hscale0 : 0 ≤ Real.sqrt t * r := mul_nonneg (Real.sqrt_nonneg _) hr.1
  have hscale1 : Real.sqrt t * r ≤ 1 :=
    (mul_le_mul_of_nonneg_left hr.2 (Real.sqrt_nonneg _)).trans
      (by simpa only [mul_one] using Real.sqrt_le_one.mpr ht1.le)
  have hz (i : Fin n) : ∀ᵐ ω ∂μ, ‖Z i ω‖ ≤ s.bandwidth := by
    apply ae_of_all
    intro ω
    change ‖(Real.sqrt t * r) • Y i ω‖ ≤ s.bandwidth
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hscale0]
    exact (mul_le_mul_of_nonneg_right hscale1 (norm_nonneg _)).trans
      (by simpa only [one_mul] using hYnorm i ω)
  let K : Vector p × Ω → ℝ := fun z => ∑ i,
    |diagonalFourth s ((z.1 + R z.2) + Z i z.2) (Y i z.2)|
  have hK : Measurable K := by
    apply Finset.measurable_sum
    intro i _
    exact ((continuous_diagonalFourth_joint s).measurable.comp
      (((measurable_fst.add (hR.comp measurable_snd)).add ((hZ i).comp measurable_snd)).prodMk
        ((hY i).comp measurable_snd))).abs
  have hbound (z : Vector p × Ω) :
      ‖K z‖ ≤ (n : ℝ) * ((smootherC4Test s).bound * s.bandwidth ^ 4) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg (fun i _ => abs_nonneg _))]
    calc
      _ ≤ ∑ _i : Fin n, (smootherC4Test s).bound * s.bandwidth ^ 4 := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [← smootherC4Test_fourthDiagonal_eq_diagonalFourth, Real.norm_eq_abs] using
          fourth_eval_bound s Y hYnorm ((z.1 + R z.2) + Z i z.2) i z.2
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have heq := integral_scaledGaussian_product μ A (Real.sqrt (1 - t)) K hK _ hbound
  have hc := intrinsic_gaussian_common_point_fourth_random_data μ hp s (Real.sqrt (1 - t) • A)
    (show 0 < 1 - t by linarith) (scaled_factor_diagonal A hdiag ht1.le) R hR Y Z hY hZ hz hQ
  rw [gaussianMaximumMean_slepian_scale_div A ht1] at hc
  simp_rw [smootherC4Test_fourthDiagonal_eq_diagonalFourth]
  exact heq.trans_le hc

private def gaussianFourthIntegrand {Ω : Type*} {p n : ℕ} (s : FaceSmoother p)
    (R : Ω → Vector p) (Y : Fin n → Ω → Vector p) (a b r : ℝ) (z : Vector p × Ω) : ℝ :=
  ∑ i, r * (1 - r) * (smootherC4Test s).fourthDiagonal
    ((b • z.1 + R z.2) + (a * r) • Y i z.2) (Y i z.2)

private theorem measurable_gaussianFourthIntegrand
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (R : Ω → Vector p) (hR : Measurable R)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) (a b : ℝ) :
    Measurable (fun q : ℝ × (Vector p × Ω) => gaussianFourthIntegrand s R Y a b q.1 q.2) := by
  apply Finset.measurable_sum
  intro i _
  have hp : Measurable (fun q : ℝ × (Vector p × Ω) =>
      (((b • q.2.1 + R q.2.2) + (a * q.1) • Y i q.2.2), Y i q.2.2)) :=
    (((measurable_const.smul (measurable_fst.comp measurable_snd)).add
    (hR.comp (measurable_snd.comp measurable_snd))).add
      ((measurable_const.mul measurable_fst).smul
        ((hY i).comp (measurable_snd.comp measurable_snd)))).prodMk
          ((hY i).comp (measurable_snd.comp measurable_snd))
  exact (measurable_fst.mul (measurable_const.sub measurable_fst)).mul
    ((smootherC4Test s).continuous_fourthDiagonal.measurable.comp hp)

private theorem norm_trapezoidal_weight_le_one {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) :
    ‖r * (1 - r)‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hr.1 (sub_nonneg.mpr hr.2))]
  nlinarith [sq_nonneg r, hr.2]

private theorem gaussianFourthIntegrand_norm_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (R : Ω → Vector p) (Y : Fin n → Ω → Vector p)
    (hYnorm : ∀ i ω, ‖Y i ω‖ ≤ s.bandwidth) (a b : ℝ)
    {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) 1) (z : Vector p × Ω) :
    ‖gaussianFourthIntegrand s R Y a b r z‖ ≤
      (n : ℝ) * ((smootherC4Test s).bound * s.bandwidth ^ 4) := by
  calc
    _ ≤ ∑ i, ‖r * (1 - r) * (smootherC4Test s).fourthDiagonal
        ((b • z.1 + R z.2) + (a * r) • Y i z.2) (Y i z.2)‖ := norm_sum_le _ _
    _ ≤ ∑ _i : Fin n, (smootherC4Test s).bound * s.bandwidth ^ 4 := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_mul]
      exact (mul_le_mul_of_nonneg_right (norm_trapezoidal_weight_le_one hr) (norm_nonneg _)).trans
        (by simpa only [one_mul] using (fourth_eval_bound s Y hYnorm
          ((b • z.1 + R z.2) + (a * r) • Y i z.2) i z.2))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- The actual trapezoidal fourth-order remainder, with the independent
Gaussian averaged only after the common-point contraction. All exchanges
with the segment integral are justified by genuine bounded domination. -/
theorem intrinsic_gaussian_trapezoidal_sum_bound
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (R : Ω → Vector p) (hR : Measurable R)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hYnorm : ∀ i ω, ‖Y i ω‖ ≤ s.bandwidth)
    (hQ : Integrable (fun ω => coordinateFourthBudget (fun i => Y i ω)) μ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) :
    |∑ i, ∫ z : Vector p × Ω, (smootherC4Test s).trapezoidalRemainder
      (Real.sqrt (1 - t) • z.1 + R z.2) (Y i z.2) (Real.sqrt t)
        ∂(gaussianLaw A).prod μ| ≤
      ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
        (gaussianMaximumMean A / Real.sqrt (1-t)) / s.bandwidth^3) *
          (∫ ω, coordinateFourthBudget (fun i => Y i ω) ∂μ) := by
  let ν := (gaussianLaw A).prod μ
  let ι : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) 1)
  haveI : IsFiniteMeasure ι := by dsimp only [ι]; infer_instance
  let a := Real.sqrt t
  let b := Real.sqrt (1 - t)
  let H := gaussianFourthIntegrand s R Y a b
  let cap := (n : ℝ) * ((smootherC4Test s).bound * s.bandwidth ^ 4)
  have hm := measurable_gaussianFourthIntegrand s R hR Y hY a b
  have hiH : Integrable (fun q : ℝ × (Vector p × Ω) => H q.1 q.2) (ι.prod ν) := by
    apply (integrable_const cap).mono' hm.aestronglyMeasurable
    have hmem : ∀ᵐ q : ℝ × (Vector p × Ω) ∂ι.prod ν, q.1 ∈ Set.Ioc (0 : ℝ) 1 :=
      (Measure.quasiMeasurePreserving_fst (μ := ι) (ν := ν)).ae (ae_restrict_mem measurableSet_Ioc)
    filter_upwards [hmem] with q hq
    exact gaussianFourthIntegrand_norm_le s R Y hYnorm a b ⟨hq.1.le, hq.2⟩ q.2
  have hbase : Measurable (fun z : Vector p × Ω => b • z.1 + R z.2) :=
    (measurable_const.smul measurable_fst).add (hR.comp measurable_snd)
  have hiR (i : Fin n) : Integrable
      (fun z : Vector p × Ω => (smootherC4Test s).trapezoidalRemainder
        (b • z.1 + R z.2) (Y i z.2) a) ν :=
    (smootherC4Test s).integrable_trapezoidalRemainder ν _ _ hbase
      ((hY i).comp measurable_snd) s.bandwidth (fun z => hYnorm i z.2) a
  have heq : (∑ i, ∫ z : Vector p × Ω, (smootherC4Test s).trapezoidalRemainder
      (b • z.1 + R z.2) (Y i z.2) a ∂ν) =
      ∫ r in (0 : ℝ)..1, ∫ z : Vector p × Ω, H r z ∂ν := by
    rw [← integral_finset_sum Finset.univ (fun i _ => hiR i)]
    calc
      _ = ∫ z : Vector p × Ω, (∫ r in (0 : ℝ)..1, H r z) ∂ν := by
        apply integral_congr_ae
        apply ae_of_all
        intro z
        change (∑ i, ∫ r in (0 : ℝ)..1, r * (1 - r) * (smootherC4Test s).fourthDiagonal
          ((b • z.1 + R z.2) + (a * r) • Y i z.2) (Y i z.2)) = _
        exact (intervalIntegral.integral_finset_sum (s := Finset.univ) (fun i _ =>
          (((continuous_id.mul (continuous_const.sub continuous_id)).mul
            ((smootherC4Test s).continuous_fourth_segment (b • z.1 + R z.2) (Y i z.2) a)).intervalIntegrable 0 1))).symm
      _ = ∫ z : Vector p × Ω, ∫ r, H r z ∂ι ∂ν := by
        simp only [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1), ι]
      _ = ∫ r, ∫ z : Vector p × Ω, H r z ∂ν ∂ι := (integral_integral_swap hiH).symm
      _ = _ := by rw [intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  have hb (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
      ‖∫ z : Vector p × Ω, H r z ∂ν‖ ≤
        ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
          (gaussianMaximumMean A / Real.sqrt (1-t)) / s.bandwidth^3) *
            (∫ ω, coordinateFourthBudget (fun i => Y i ω) ∂μ) := by
    let K : Fin n → Vector p × Ω → ℝ := fun i z =>
      (smootherC4Test s).fourthDiagonal ((b • z.1 + R z.2) + (a * r) • Y i z.2) (Y i z.2)
    have hiK (i : Fin n) : Integrable (K i) ν := by
      apply (integrable_const ((smootherC4Test s).bound * s.bandwidth ^ 4)).mono'
      · exact ((smootherC4Test s).continuous_fourthDiagonal.measurable.comp
          ((hbase.add (measurable_const.smul ((hY i).comp measurable_snd))).prodMk
            ((hY i).comp measurable_snd))).aestronglyMeasurable
      · exact ae_of_all _ (fun z => fourth_eval_bound s Y hYnorm _ i z.2)
    have hiS : Integrable (H r) ν := by
      exact integrable_finset_sum _ (fun i _ => (hiK i).const_mul (r * (1 - r)))
    have hiAbs : Integrable (fun z => ∑ i, |K i z|) ν :=
      integrable_finset_sum _ (fun i _ => (hiK i).abs)
    have hpoint (z : Vector p × Ω) : ‖H r z‖ ≤ ∑ i, |K i z| := by
      calc
        _ ≤ ∑ i, ‖r * (1 - r) * K i z‖ := norm_sum_le _ _
        _ ≤ ∑ i, ‖K i z‖ := by
          apply Finset.sum_le_sum
          intro i _
          rw [norm_mul]
          simpa only [one_mul] using
            mul_le_mul_of_nonneg_right (norm_trapezoidal_weight_le_one hr) (norm_nonneg (K i z))
        _ = _ := by simp only [Real.norm_eq_abs]
    calc
      _ ≤ ∫ z, ‖H r z‖ ∂ν := norm_integral_le_integral_norm _
      _ ≤ ∫ z, ∑ i, |K i z| ∂ν := integral_mono hiS.norm hiAbs hpoint
      _ ≤ _ := gaussian_fourth_segment_sum_abs_le μ hp s A hdiag R hR Y hY hYnorm hQ ht ht1 hr
  rw [heq]
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (0 : ℝ)) (b := 1) (f := fun r => ∫ z : Vector p × Ω, H r z ∂ν)
    (fun r hr => hb r (by
      rw [Set.uIoc_of_le (by norm_num : (0 : ℝ) ≤ 1)] at hr
      exact ⟨hr.1.le, hr.2⟩))
  simpa only [sub_zero, abs_one, mul_one, Real.norm_eq_abs] using hnorm

/-- The fourth remainder in the full paired Slepian identity, with its
actual truncated increments and original-summand common center. -/
theorem intrinsic_pairedGaussianRemainder_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (hp : 1 ≤ p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) {h : ℝ} (hh : 0 ≤ h) (hband : h ≤ s.bandwidth) :
    |∑ i, ∫ z, (smootherC4Test s).trapezoidalRemainder
      (C4Test.arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
      (C4Test.arrayCopyIncrement ξ i h z) (Real.sqrt t)
        ∂(gaussianLaw A).prod (μ.prod μ)| ≤
      ((75 * (Real.exp 2)^5 * Real.exp (3 / 2 : ℝ)) *
        (gaussianMaximumMean A / Real.sqrt (1-t)) / s.bandwidth^3) *
          (∫ z : Ω × Ω, coordinateFourthBudget (fun i => pairedTruncatedArray ξ h i z) ∂μ.prod μ) := by
  have hsum : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hR : Measurable (fun z : Ω × Ω => Real.sqrt t • sumVector ξ z.1) :=
    measurable_const.smul (hsum.comp measurable_fst)
  have hY (i : Fin n) : Measurable (pairedTruncatedArray ξ h i) :=
    measurable_pairedTruncatedArray ξ hξ h i
  have hnorm (i : Fin n) (z : Ω × Ω) : ‖pairedTruncatedArray ξ h i z‖ ≤ s.bandwidth :=
    (C4Test.norm_pairedTruncatedIncrement_le _ _ hh).trans hband
  have hiQ := integrable_pairedFourthBudget μ ξ hξ hh
  have hc := intrinsic_gaussian_trapezoidal_sum_bound (μ.prod μ) hp s A hdiag _ hR
    (pairedTruncatedArray ξ h) hY hnorm hiQ ht.le ht1
  simpa only [C4Test.arrayCopyPoint, C4Test.arrayCopyIncrement, pairedTruncatedArray, add_comm] using hc

end
end RectangleCLTArxivV1
