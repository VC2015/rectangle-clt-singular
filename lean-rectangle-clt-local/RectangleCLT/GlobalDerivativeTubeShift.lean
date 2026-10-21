import RectangleCLT.GlobalDerivativeTubeMoments

/-! Full-dual tube moments against an independent base vector. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

theorem dualImageRatioWeight_joint_measurable {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (width : ℝ) (g : Vector p → ℝ)
    (hg : Measurable g) (hd : IsUnit (A * A.transpose).det) :
    Measurable (fun rz : Vector p × CommonSamples p =>
      dualImageRatioWeight S s A rz.1 width g rz.2) := by
  have hb : Measurable (fun rz : Vector p × CommonSamples p =>
      base (dualImagePreimage S s A rz)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp
        (measurable_dualImagePreimage S s A))
  exact ((((standardGaussianDensity_measurable p).comp hb).div
    ((standardGaussianDensity_measurable p).comp
      (measurable_fst.comp measurable_snd))).mul (hg.comp hb)).indicator
        (measurableSet_dualImageEvent_joint S s A width hd)

theorem dualImageRatioWeight_polynomial_integrable_shift
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M) (k : ℕ) :
    Integrable (fun z : CommonSamples p × Ω =>
      dualImageRatioWeight S s A (V z.2) width (fullScorePolynomial A ν k) z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
  have hbase : Integrable (fun z : CommonSamples p × Ω =>
      (2 : ℝ) ^ k * commonFullScoreTubeWeight A ν M k z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    simpa only [mul_one] using
      ((commonFullScoreTubeWeight_integrable hp A hν hlower hM k).const_mul
        ((2 : ℝ) ^ k)).mul_prod (integrable_const (1 : ℝ) (μ := μ))
  apply hbase.mono'
    ((dualImageRatioWeight_joint_measurable S s A width _
      (fullScorePolynomial_measurable A ν k)
      (factor_covariance_det_isUnit_of_full_lower A hν hlower)).comp
        ((hV.comp measurable_snd).prodMk measurable_fst)).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg
      (dualImageRatioWeight_nonneg S s A (V z.2) width _
        (fullScorePolynomial_nonneg A ν k) z.1)]
    exact (dualImageRatioWeight_polynomial_le S s A (V z.2) hν hw
      ((sqrt_dimensionLog_ge_one hp).trans hM) hlower hwidth k z.1).trans (by
        apply mul_le_of_le_one_right
          (mul_nonneg (pow_nonneg (by norm_num) k)
            (fullScoreTubeWeight_nonneg A ν M k z.1.1))
        by_cases hz : z.1 ∈ dualImageEvent S s A (V z.2) width <;> simp [hz])

theorem integrable_softFace_fullScorePolynomial_shift
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (S : Finset (Face p)) (k : ℕ) :
    Integrable (fun z : Vector p × Ω =>
      s.softFaceWeight S (A.mulVec z.1 + V z.2) * fullScorePolynomial A ν k z.1)
      ((standardGaussian p).prod μ) := by
  have hbase : Integrable (fun z : Vector p × Ω => fullScorePolynomial A ν k z.1)
      ((standardGaussian p).prod μ) := by
    simpa only [mul_one] using
      (fullScorePolynomial_integrable hp A hν hlower k).mul_prod
        (integrable_const (1 : ℝ) (μ := μ))
  apply hbase.bdd_mul
    (((s.continuous_softFaceWeight _).measurable.comp
      (((measurable_mulVec A).comp measurable_fst).add
        (hV.comp measurable_snd))).aestronglyMeasurable)
  exact ⟨1, fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg _ _)]
    exact s.softFaceWeight_le_one _ _⟩

def shiftedDualFaceMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (V : Ω → Vector p) (k : ℕ) : ℝ :=
  (∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z.1 + V z.2) *
    fullScorePolynomial A ν k z.1 ∂(standardGaussian p).prod μ) / s.bandwidth ^ q

theorem integral_dualFaceMoment_shift_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (k : ℕ) :
    (∫ ω, dualFaceMoment S s A ν (V ω) k ∂μ) =
      shiftedDualFaceMoment μ S s A ν V k := by
  unfold dualFaceMoment shiftedDualFaceMoment FaceSmoother.fullDualGaussianSoftFaceMoment
  simp_rw [div_eq_mul_inv]
  rw [integral_mul_const]
  congr 1
  simp_rw [mul_comm (s.softFaceWeight _ _) _]
  simpa only [fullScorePolynomial, mul_comm] using
    (integral_prod_symm (μ := standardGaussian p) (ν := μ) _
      (integrable_softFace_fullScorePolynomial_shift s A V hV hp hν hlower
        (activeFaces S) k)).symm

theorem dualImageRatioWeight_integral_shift_eq_dualFaceMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ z, dualImageRatioWeight S s A (V z.2) width (fullScorePolynomial A ν k) z.1
      ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) =
      width ^ q * (q.factorial : ℝ) * shiftedDualFaceMoment μ S s A ν V k := by
  rw [integral_prod_symm _
    (dualImageRatioWeight_polynomial_integrable_shift S s A V hV hp hν hw hlower hM hwidth k)]
  calc
    _ = ∫ ω, width ^ q * (q.factorial : ℝ) * dualFaceMoment S s A ν (V ω) k ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ fun ω => dualImageRatioWeight_integral_eq_dualFaceMoment
        S s A (V ω) hp hν hw hlower hM hwidth hactive hgram k
    _ = _ := by
      rw [integral_const_mul, integral_dualFaceMoment_shift_eq S s A V hV hp hν hlower k]

theorem dualImageRatioWeight_integral_shift_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M) (k : ℕ) :
    (∫ z, dualImageRatioWeight S s A (V z.2) width (fullScorePolynomial A ν k) z.1
      ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) ≤
      (2 : ℝ) ^ k * ∫ z, commonFullScoreTubeWeight A ν M k z.1 *
        (liftedDualImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z
        ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ := by
  have hbase : Integrable (fun z : CommonSamples p × Ω =>
      commonFullScoreTubeWeight A ν M k z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    simpa only [mul_one] using
      (commonFullScoreTubeWeight_integrable hp A hν hlower hM k).mul_prod
        (integrable_const (1 : ℝ) (μ := μ))
  have hwi : Integrable (fun z => commonFullScoreTubeWeight A ν M k z.1 *
      (liftedDualImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    convert hbase.indicator (measurableSet_liftedDualImageEvent S s A V hV width
      (factor_covariance_det_isUnit_of_full_lower A hν hlower)) using 1
    funext z
    by_cases hz : z ∈ liftedDualImageEvent S s A V width <;> simp [hz]
  calc
    _ ≤ ∫ z, (2 : ℝ) ^ k * (commonFullScoreTubeWeight A ν M k z.1 *
        (liftedDualImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z)
        ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ := by
      apply integral_mono
        (dualImageRatioWeight_polynomial_integrable_shift S s A V hV hp hν hw hlower hM hwidth k)
        (hwi.const_mul _) (fun z => ?_)
      exact (dualImageRatioWeight_polynomial_le S s A (V z.2) hν hw
        ((sqrt_dimensionLog_ge_one hp).trans hM) hlower hwidth k z.1).trans_eq (by
          change (2 : ℝ) ^ k * fullScoreTubeWeight A ν M k z.1.1 *
            (dualImageEvent S s A (V z.2) width).indicator (fun _ => (1 : ℝ)) z.1 = _
          have he : (liftedDualImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z =
              (dualImageEvent S s A (V z.2) width).indicator (fun _ => (1 : ℝ)) z.1 := rfl
          rw [he]
          dsimp only [commonFullScoreTubeWeight]
          ring)
    _ = _ := integral_const_mul _ _

end

end RectangleCLT.GaussianTube
