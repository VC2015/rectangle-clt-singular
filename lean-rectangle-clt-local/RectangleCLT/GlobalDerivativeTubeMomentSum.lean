import RectangleCLT.GlobalDerivativeTubeShift
import RectangleCLT.GlobalDerivativeAssembly

/-! Ordered full-dual face sums with independent probability localization. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

theorem fullDual_normalMatrix_gram_det_pos {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v) :
    0 < ((normalMatrix S A).transpose * normalMatrix S A).det := by
  rw [normalMatrix_gram]
  apply S.gram_det_pos (full_lower_implies_local _ _ hlower q) hν
  intro i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

theorem shiftedDualFaceMoment_eq_canonical
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p q : ℕ} {faces : Finset (Face p)} (S : OrderedFaceTuples faces q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℝ) (V : Ω → Vector p) (k : ℕ) :
    shiftedDualFaceMoment μ S.val s A ν V k =
      shiftedDualFaceMoment μ (compatibleSetTuple (tupleActiveSet S)) s A ν V k := by
  have hset : activeFaces S.val = activeFaces (compatibleSetTuple (tupleActiveSet S)) := by
    rw [activeFaces_compatibleSetTuple]
    rfl
  unfold shiftedDualFaceMoment
  rw [hset]

theorem sum_ordered_shiftedDualFaceMoment_eq_factorial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (ν : ℝ) (V : Ω → Vector p) (k : ℕ) :
    (∑ S : OrderedFaceTuples s.faces q, shiftedDualFaceMoment μ S.val s A ν V k) =
      (q.factorial : ℝ) * ∑ T : CompatibleFaceSets s.faces q,
        shiftedDualFaceMoment μ (compatibleSetTuple T) s A ν V k := by
  classical
  calc
    _ = ∑ S : OrderedFaceTuples s.faces q,
        shiftedDualFaceMoment μ (compatibleSetTuple (tupleActiveSet S)) s A ν V k :=
      Finset.sum_congr rfl fun S _ => shiftedDualFaceMoment_eq_canonical μ S s A ν V k
    _ = _ := sum_orderedFaceTuples_eq_factorial s.faces
      (fun T => shiftedDualFaceMoment μ (compatibleSetTuple T) s A ν V k)

theorem sum_shiftedDualFaceMoment_mul_width_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p) (hq : 0 < q)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M) (k : ℕ)
    (B : ℝ) (hboundary : ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer ((q : ℝ) * width)} ≤ B) :
    width ^ q * (q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q,
        shiftedDualFaceMoment μ (compatibleSetTuple T) s A ν V k) ≤
      (2 : ℝ) ^ k * B * (Real.sqrt (dimensionLog p)) ^ k *
        Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) := by
  classical
  have hactive (T : CompatibleFaceSets s.faces q) (i : Fin q) :
      (compatibleSetTuple T).face i ∈ s.faces := by
    apply T.property.1
    rw [← activeFaces_compatibleSetTuple T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  have hB : 0 ≤ B := (measureReal_nonneg).trans (hboundary s 0)
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  let γ := (standardGaussian p).prod (exponentialRectangleLaw p)
  calc
    _ = ∑ T : CompatibleFaceSets s.faces q,
        ∫ z, dualImageRatioWeight (compatibleSetTuple T) s A (V z.2) width
          (fullScorePolynomial A ν k) z.1 ∂γ.prod μ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      exact (dualImageRatioWeight_integral_shift_eq_dualFaceMoment _ s A V hV hp
        hν hw hlower hM hwidth (hactive T)
        (fullDual_normalMatrix_gram_det_pos _ A hν hlower) k).symm
    _ ≤ ∑ T : CompatibleFaceSets s.faces q,
        (2 : ℝ) ^ k * ∫ z, commonFullScoreTubeWeight A ν M k z.1 *
          (liftedDualImageEvent (compatibleSetTuple T) s A V width).indicator
            (fun _ => (1 : ℝ)) z ∂γ.prod μ :=
      Finset.sum_le_sum fun T _ => dualImageRatioWeight_integral_shift_le
        _ s A V hV hp hν hw hlower hM hwidth k
    _ = (2 : ℝ) ^ k * ∑ T : CompatibleFaceSets s.faces q,
        ∫ z, commonFullScoreTubeWeight A ν M k z.1 *
          (liftedDualImageEvent (compatibleSetTuple T) s A V width).indicator
            (fun _ => (1 : ℝ)) z ∂γ.prod μ := (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ k * (B * ∫ e, commonFullScoreTubeWeight A ν M k e ∂γ) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
      apply integral_sum_weighted_dual_image_indicators_le Finset.univ compatibleSetTuple
        s A hd (fun T _ i => hactive T i)
        (fun T _ U _ h => Subtype.ext (by simpa only [activeFaces_compatibleSetTuple] using h))
        hq hw μ V hV γ _ (commonFullScoreTubeWeight_integrable hp A hν hlower hM k)
        (commonFullScoreTubeWeight_nonneg A ν M k) B hboundary
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left
        (commonFullScoreTubeWeight_integral_le hp A hν hlower hM k)
        (mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) k) hB)
      exact (by simpa only [mul_assoc] using hh)

end

end GaussianTube

namespace FaceSmoother

open GaussianTube

theorem integrable_fullDualGaussianSoftFaceMoment_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (S : Finset (Face p)) (k : ℕ) :
    Integrable (fun ω => s.fullDualGaussianSoftFaceMoment A ν (V ω) S k) μ := by
  simpa only [fullDualGaussianSoftFaceMoment, fullScorePolynomial, mul_comm] using
    (integrable_softFace_fullScorePolynomial_shift s A V hV hp hν hlower S k).integral_prod_right

theorem integrable_fullDualFaceMomentSum_comp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (q k : ℕ) :
    Integrable (fun ω => s.fullDualFaceMomentSum A ν (V ω) q k) μ := by
  classical
  exact integrable_finset_sum _ fun T _ =>
    s.integrable_fullDualGaussianSoftFaceMoment_comp A V hV hp hν hlower _ k

theorem integral_fullDualFaceMomentSum_div_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p)
    {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (k : ℕ) :
    (∫ ω, s.fullDualFaceMomentSum A ν (V ω) q k ∂μ) / s.bandwidth ^ q =
      ∑ S : OrderedFaceTuples s.faces q, shiftedDualFaceMoment μ S.val s A ν V k := by
  classical
  unfold fullDualFaceMomentSum
  rw [integral_finset_sum _ (fun T _ =>
    s.integrable_fullDualGaussianSoftFaceMoment_comp A V hV hp hν hlower _ k),
    Finset.sum_div]
  apply Finset.sum_congr rfl
  intro S _
  rw [← integral_dualFaceMoment_shift_eq S.val s A V hV hp hν hlower k]
  simp only [dualFaceMoment, div_eq_mul_inv, integral_mul_const]
  rfl

/-- Every ordered face moment is counted, with no dimension factor. The
boundary probability concerns an independent base vector. -/
theorem integral_fullDualFaceMomentSum_div_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (hp : 1 ≤ p) (hq : 0 < q)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M) (k : ℕ)
    (B : ℝ) (hboundary : ∀ (t : FaceSmoother p) (r : Vector p),
      μ.real {ω | V ω + r ∈ t.boundaryLayer ((q : ℝ) * width)} ≤ B) :
    width ^ q * ((∫ ω, s.fullDualFaceMomentSum A ν (V ω) q k ∂μ) /
      s.bandwidth ^ q) ≤
      (2 : ℝ) ^ k * B * (Real.sqrt (dimensionLog p)) ^ k *
        Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) := by
  rw [s.integral_fullDualFaceMomentSum_div_eq A V hV hp hν hlower k,
    sum_ordered_shiftedDualFaceMoment_eq_factorial, ← mul_assoc]
  exact sum_shiftedDualFaceMoment_mul_width_le s A V hV hp hq hν hw hlower
    hM hwidth k B hboundary

end FaceSmoother

end RectangleCLT
