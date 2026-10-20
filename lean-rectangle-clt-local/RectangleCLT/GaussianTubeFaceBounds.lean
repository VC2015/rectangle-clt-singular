import RectangleCLT.GaussianTubeDomination
import RectangleCLT.GaussianTubeTransport
import RectangleCLT.GaussianTubeUnion
import RectangleCLT.GaussianFaceEnumeration

/-! Integrated compatible-face bounds obtained from the concrete augmented
tubes. Each compatible active set is counted once. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

def projectionPolynomial {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (z : Vector p) : ℝ := (1 + fourFaceProjectionRadius A z) ^ k

def projectionTubeWeight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (M : ℝ) (k : ℕ)
    (z : Vector p) : ℝ :=
  Real.exp (fourFaceProjectionRadius A z / M) * projectionPolynomial A k z

theorem projectionPolynomial_measurable {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) : Measurable (projectionPolynomial A k) :=
  (measurable_const.add (measurable_fourFaceProjectionRadius A)).pow_const k

theorem projectionPolynomial_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (z : Vector p) :
    0 ≤ projectionPolynomial A k z :=
  pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A z]) k

theorem projectionTubeWeight_measurable {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (M : ℝ) (k : ℕ) : Measurable (projectionTubeWeight A M k) :=
  (((measurable_fourFaceProjectionRadius A).div_const M).exp).mul
    (projectionPolynomial_measurable A k)

theorem projectionTubeWeight_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (M : ℝ) (k : ℕ) (z : Vector p) :
    0 ≤ projectionTubeWeight A M k z :=
  mul_nonneg (Real.exp_nonneg _) (projectionPolynomial_nonneg A k z)

theorem sqrt_dimensionLog_ge_one {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ Real.sqrt (dimensionLog p) := by
  have hh := Real.sqrt_le_sqrt (log_exp_mul_nat_ge_one hp)
  simpa only [Real.sqrt_one] using hh

theorem projectionTubeWeight_integrable {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {M : ℝ}
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (projectionTubeWeight A M k) (standardGaussian p) :=
  (fourFaceProjectionRadius_weighted_moment_le hp A hM k).1

theorem projectionTubeWeight_integral_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {M : ℝ}
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    (∫ z, projectionTubeWeight A M k z ∂standardGaussian p) ≤
      (Real.sqrt (dimensionLog p)) ^ k * Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) :=
  (fourFaceProjectionRadius_weighted_moment_le hp A hM k).2

theorem projectionPolynomial_integrable {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Integrable (projectionPolynomial A k) (standardGaussian p) := by
  have hM : 0 ≤ Real.sqrt (dimensionLog p) := Real.sqrt_nonneg _
  apply (projectionTubeWeight_integrable hp A (le_refl _) k).mono'
    (projectionPolynomial_measurable A k).aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [Real.norm_eq_abs, abs_of_nonneg (projectionPolynomial_nonneg A k z)]
  have he : 1 ≤ Real.exp (fourFaceProjectionRadius A z / Real.sqrt (dimensionLog p)) :=
    Real.one_le_exp_iff.mpr (div_nonneg (fourFaceProjectionRadius_nonneg A z) hM)
  exact (one_mul _).symm.trans_le
    (mul_le_mul_of_nonneg_right he (projectionPolynomial_nonneg A k z))

theorem normalMatrix_gram_det_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    0 ≤ ((normalMatrix S A).transpose * normalMatrix S A).det := by
  have hh := gram_det_ordered (normalMatrix S A).transpose
  simp only [Matrix.transpose_transpose] at hh
  have hc : (0 : ℝ) < Fintype.card (Equiv.Perm (Fin q)) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hs : 0 ≤ ∑ f : Fin q → Fin p,
      (((normalMatrix S A).transpose.submatrix id f).det) ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  nlinarith

def faceMoment {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (k : ℕ) : ℝ :=
  (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
    ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) *
      projectionPolynomial A k z ∂standardGaussian p

theorem faceMoment_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (k : ℕ) :
    0 ≤ faceMoment S s A r k := by
  apply mul_nonneg (div_nonneg (normalMatrix_gram_det_nonneg S A) (pow_nonneg s.bandwidth_pos.le _))
  exact integral_nonneg fun z =>
    mul_nonneg (s.softFaceWeight_nonneg _ _) (projectionPolynomial_nonneg A k z)

theorem integrable_softFace_projectionPolynomial_shift
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (k : ℕ) :
    Integrable (fun z : Vector p × Ω =>
      s.softFaceWeight (activeFaces S) (A.mulVec z.1 + V z.2) *
        projectionPolynomial A k z.1) ((standardGaussian p).prod μ) := by
  have hbase : Integrable (fun z : Vector p × Ω => projectionPolynomial A k z.1)
      ((standardGaussian p).prod μ) := by
    simpa only [mul_one] using
      (projectionPolynomial_integrable hp A k).mul_prod (integrable_const (1 : ℝ) (μ := μ))
  apply hbase.bdd_mul
    (((s.continuous_softFaceWeight _).measurable.comp
      (((measurable_mulVec A).comp measurable_fst).add (hV.comp measurable_snd))).aestronglyMeasurable)
  exact ⟨1, fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg _ _)]
    exact s.softFaceWeight_le_one _ _⟩

def commonProjectionTubeWeight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (M : ℝ) (k : ℕ) (ze : CommonSamples p) : ℝ := projectionTubeWeight A M k ze.1

theorem commonProjectionTubeWeight_integrable {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {M : ℝ}
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (commonProjectionTubeWeight A M k)
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
  simpa only [mul_one] using
    (projectionTubeWeight_integrable hp A hM k).mul_prod
      (integrable_const (1 : ℝ) (μ := exponentialRectangleLaw p))

theorem commonProjectionTubeWeight_integral {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (M : ℝ) (k : ℕ) :
    (∫ ze, commonProjectionTubeWeight A M k ze
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ∫ z, projectionTubeWeight A M k z ∂standardGaussian p := by
  simpa only [measureReal_univ_eq_one, one_smul, commonProjectionTubeWeight] using
    (integral_fun_fst (μ := standardGaussian p) (ν := exponentialRectangleLaw p)
      (projectionTubeWeight A M k))

theorem imageRatioWeight_integral_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ ze, imageRatioWeight S s A r width (projectionPolynomial A k) ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) ≤
      (2 : ℝ) ^ k * ∫ ze, commonProjectionTubeWeight A M k ze *
        (imageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p) := by
  have hevent : MeasurableSet (imageEvent S s A r width) :=
    (measurableSet_imageEvent_joint S s A width hd).preimage
      (measurable_const.prodMk measurable_id)
  have hwi : Integrable (fun ze => commonProjectionTubeWeight A M k ze *
      (imageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze)
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
    convert (commonProjectionTubeWeight_integrable hp A hM k).indicator hevent using 1
    funext ze
    by_cases hz : ze ∈ imageEvent S s A r width <;> simp [hz]
  calc
    _ ≤ ∫ ze, (2 : ℝ) ^ k * (commonProjectionTubeWeight A M k ze *
        (imageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze)
        ∂(standardGaussian p).prod (exponentialRectangleLaw p) := by
      apply integral_mono
        (imageRatioWeight_projection_integrable S s A r hp hq0 hq hv hdiag hw hM hwidth hd k)
        (hwi.const_mul _) (fun ze => ?_)
      have hh := imageRatioWeight_projection_le S s A r hq0 hq hv hdiag hw
        ((sqrt_dimensionLog_ge_one hp).trans hM) hwidth hd k ze
      dsimp only [commonProjectionTubeWeight, projectionTubeWeight, projectionPolynomial]
      convert hh using 1
      ring
    _ = _ := integral_const_mul _ _

/-- Global weighted union estimate for all compatible face sets. Its right
side depends logarithmically on the number of coordinates, independently of
the number of active face sets. -/
theorem sum_all_imageRatioWeight_le_total {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    (∑ T : CompatibleFaceSets s.faces q,
      ∫ ze, imageRatioWeight (compatibleSetTuple T) s A r width (projectionPolynomial A k) ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) ≤
      (2 : ℝ) ^ k * (Real.sqrt (dimensionLog p)) ^ k *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  classical
  calc
    _ ≤ ∑ T : CompatibleFaceSets s.faces q,
        (2 : ℝ) ^ k * ∫ ze, commonProjectionTubeWeight A M k ze *
          (imageEvent (compatibleSetTuple T) s A r width).indicator (fun _ => (1 : ℝ)) ze
          ∂(standardGaussian p).prod (exponentialRectangleLaw p) :=
      Finset.sum_le_sum (fun T _ =>
        imageRatioWeight_integral_le _ s A r hp hq0 hq hv hdiag hw hM hwidth (hd T) k)
    _ = (2 : ℝ) ^ k * ∑ T : CompatibleFaceSets s.faces q,
        ∫ ze, commonProjectionTubeWeight A M k ze *
          (imageEvent (compatibleSetTuple T) s A r width).indicator (fun _ => (1 : ℝ)) ze
          ∂(standardGaussian p).prod (exponentialRectangleLaw p) :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ k * ∫ ze, commonProjectionTubeWeight A M k ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p) := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg (by norm_num) k)
      exact integral_sum_all_fixed_compatible_images_le_total s A r width hd _ _
        (commonProjectionTubeWeight_integrable hp A hM k)
        (fun ze => projectionTubeWeight_nonneg A M k ze.1)
    _ ≤ _ := by
      rw [commonProjectionTubeWeight_integral]
      exact (mul_le_mul_of_nonneg_left (projectionTubeWeight_integral_le hp A hM k)
        (pow_nonneg (by norm_num) k)).trans_eq (by ring)

theorem imageRatioWeight_integral_shift_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ z, imageRatioWeight S s A (V z.2) width (projectionPolynomial A k) z.1
      ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) ≤
      (2 : ℝ) ^ k * ∫ z, commonProjectionTubeWeight A M k z.1 *
        (liftedImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z
        ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ := by
  have hbase : Integrable (fun z : CommonSamples p × Ω => commonProjectionTubeWeight A M k z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    simpa only [mul_one] using
      (commonProjectionTubeWeight_integrable hp A hM k).mul_prod
        (integrable_const (1 : ℝ) (μ := μ))
  have hwi : Integrable (fun z => commonProjectionTubeWeight A M k z.1 *
      (liftedImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    convert hbase.indicator (measurableSet_liftedImageEvent S s A V hV width hd) using 1
    funext z
    by_cases hz : z ∈ liftedImageEvent S s A V width <;> simp [hz]
  calc
    _ ≤ ∫ z, (2 : ℝ) ^ k * (commonProjectionTubeWeight A M k z.1 *
        (liftedImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z)
        ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ := by
      apply integral_mono
        (imageRatioWeight_projection_integrable_shift S s A V hV hp hq0 hq hv hdiag hw hM hwidth hd k)
        (hwi.const_mul _) (fun z => ?_)
      have hh := imageRatioWeight_projection_le S s A (V z.2) hq0 hq hv hdiag hw
        ((sqrt_dimensionLog_ge_one hp).trans hM) hwidth hd k z.1
      have he : (liftedImageEvent S s A V width).indicator (fun _ => (1 : ℝ)) z =
          (imageEvent S s A (V z.2) width).indicator (fun _ => (1 : ℝ)) z.1 := rfl
      rw [he]
      dsimp only [commonProjectionTubeWeight, projectionTubeWeight, projectionPolynomial]
      convert hh using 1
      ring
    _ = _ := integral_const_mul _ _

/-- Actual bounded-base localization of the whole weighted tube family. The
gain comes from one common annulus event and genuine independent bounded
summands; no face-concentration premise is assumed. -/
theorem sum_all_imageRatioWeight_le_local
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n q : ℕ} {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ j, (A * A.transpose) j j = ρ)
    (hq0 : 0 < q) (hq : q ≤ 4) {width M : ℝ} (hw : 0 < width)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt ρ * width ≤ 1 / M)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    (∑ T : CompatibleFaceSets s.faces q,
      ∫ z, imageRatioWeight (compatibleSetTuple T) s A (sumVector ξ z.2) width
        (projectionPolynomial A k) z.1
        ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) ≤
      (2 : ℝ) ^ k *
        (1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v)) *
        ((Real.sqrt (dimensionLog p)) ^ k * Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2)) := by
  classical
  let C := 1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v)
  have hC : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (mul_nonneg (by norm_num) (add_nonneg
      (mul_nonneg (mul_nonneg (Nat.cast_nonneg q) hρ.le) hw.le) h.delta_nonneg)) (Real.sqrt_nonneg _)
  calc
    _ ≤ ∑ T : CompatibleFaceSets s.faces q,
        (2 : ℝ) ^ k * ∫ z, commonProjectionTubeWeight A M k z.1 *
          (liftedImageEvent (compatibleSetTuple T) s A (sumVector ξ) width).indicator
            (fun _ => (1 : ℝ)) z
          ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ :=
      Finset.sum_le_sum (fun T _ => imageRatioWeight_integral_shift_le
        (compatibleSetTuple T) s A (sumVector ξ) h.measurable_sum hp hq0 hq hρ.le hA hw.le hM hwidth (hd T) k)
    _ = (2 : ℝ) ^ k * ∑ T : CompatibleFaceSets s.faces q,
        ∫ z, commonProjectionTubeWeight A M k z.1 *
          (liftedImageEvent (compatibleSetTuple T) s A (sumVector ξ) width).indicator
            (fun _ => (1 : ℝ)) z
          ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ :=
      (Finset.mul_sum _ _ _).symm
    _ ≤ (2 : ℝ) ^ k * C * ∫ ze, commonProjectionTubeWeight A M k ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p) := by
      have hh := integral_sum_all_compatible_images_le s A hρ hA hd hq0 hw h hp hv hdiag
        ((standardGaussian p).prod (exponentialRectangleLaw p)) (commonProjectionTubeWeight A M k)
        (commonProjectionTubeWeight_integrable hp A hM k)
        (fun ze => projectionTubeWeight_nonneg A M k ze.1)
      exact (mul_le_mul_of_nonneg_left hh (pow_nonneg (by norm_num) k)).trans_eq (by ring)
    _ ≤ _ := by
      rw [commonProjectionTubeWeight_integral]
      exact mul_le_mul_of_nonneg_left (projectionTubeWeight_integral_le hp A hM k)
        (mul_nonneg (pow_nonneg (by norm_num) k) hC)

theorem imageRatioWeight_integral_eq_faceMoment {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (hactive : ∀ i, S.face i ∈ s.faces)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ ze, imageRatioWeight S s A r width (projectionPolynomial A k) ze
        ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      width ^ q * (q.factorial : ℝ) * faceMoment S s A r k := by
  have hi : Integrable (imageRatioWeight S s A r width (projectionPolynomial A k))
      ((standardGaussian p).prod (exponentialRectangleLaw p)) :=
    imageRatioWeight_projection_integrable S s A r hp hq0 hq hv hdiag hw hM hwidth hd k
  have hn : ∀ᵐ ze ∂(standardGaussian p).prod (exponentialRectangleLaw p),
      0 ≤ imageRatioWeight S s A r width (projectionPolynomial A k) ze :=
    ae_of_all _ (imageRatioWeight_nonneg S s A r width _ (projectionPolynomial_nonneg A k))
  have hh := lintegral_imageRatioWeight_eq_softFaceWeight S s A r
    (projectionPolynomial A k) (projectionPolynomial_measurable A k)
    (projectionPolynomial_integrable hp A k) (projectionPolynomial_nonneg A k)
    hactive hw hd (normalMatrix_gram_det_nonneg S A)
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hh
  have hright : 0 ≤ width ^ q *
      (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
      (q.factorial : ℝ) *
      ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) *
        projectionPolynomial A k z ∂standardGaussian p :=
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg hw q)
      (div_nonneg (normalMatrix_gram_det_nonneg S A) (pow_nonneg s.bandwidth_pos.le q)))
      (Nat.cast_nonneg _)) (integral_nonneg (fun z =>
        mul_nonneg (s.softFaceWeight_nonneg _ _) (projectionPolynomial_nonneg A k z)))
  have hreal := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), ENNReal.toReal_ofReal hright] at hreal
  exact hreal.trans (by unfold faceMoment; ring)

/-- The global Gaussian weighted face estimate, proved from the actual tube
Jacobian and the disjoint common experiment. Keeping the exact width and
factorial visible makes the conversion to ordered active faces immediate. -/
theorem sum_faceMoment_mul_width_le {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    width ^ q * (q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q, faceMoment (compatibleSetTuple T) s A r k) ≤
      (2 : ℝ) ^ k * (Real.sqrt (dimensionLog p)) ^ k *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  classical
  have hactive (T : CompatibleFaceSets s.faces q) (i : Fin q) :
      (compatibleSetTuple T).face i ∈ s.faces := by
    apply T.property.1
    rw [← activeFaces_compatibleSetTuple T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  calc
    _ = ∑ T : CompatibleFaceSets s.faces q,
        ∫ ze, imageRatioWeight (compatibleSetTuple T) s A r width (projectionPolynomial A k) ze
          ∂(standardGaussian p).prod (exponentialRectangleLaw p) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      exact (imageRatioWeight_integral_eq_faceMoment _ s A r hp hq0 hq hv hdiag
        (hactive T) hw hM hwidth (hd T) k).symm
    _ ≤ _ := sum_all_imageRatioWeight_le_total s A r hp hq0 hq hv hdiag hw hM hwidth hd k

def shiftedFaceMoment {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (k : ℕ) : ℝ :=
  (((normalMatrix S A).transpose * normalMatrix S A).det / s.bandwidth ^ q) *
    ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z.1 + V z.2) *
      projectionPolynomial A k z.1 ∂(standardGaussian p).prod μ

theorem integral_faceMoment_shift_eq
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (k : ℕ) :
    (∫ ω, faceMoment S s A (V ω) k ∂μ) = shiftedFaceMoment μ S s A V k := by
  unfold faceMoment shiftedFaceMoment
  rw [integral_const_mul]
  congr 1
  exact (integral_prod_symm _
    (integrable_softFace_projectionPolynomial_shift S s A V hV hp k)).symm

theorem imageRatioWeight_integral_shift_eq_faceMoment
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (hactive : ∀ i, S.face i ∈ s.faces)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ z, imageRatioWeight S s A (V z.2) width (projectionPolynomial A k) z.1
      ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) =
      width ^ q * (q.factorial : ℝ) * shiftedFaceMoment μ S s A V k := by
  have hi : Integrable (fun z : CommonSamples p × Ω =>
      imageRatioWeight S s A (V z.2) width (projectionPolynomial A k) z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) :=
    imageRatioWeight_projection_integrable_shift S s A V hV hp hq0 hq hv hdiag hw hM hwidth hd k
  rw [integral_prod_symm _ hi]
  calc
    _ = ∫ ω, width ^ q * (q.factorial : ℝ) * faceMoment S s A (V ω) k ∂μ := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω =>
        imageRatioWeight_integral_eq_faceMoment S s A (V ω) hp hq0 hq hv hdiag
          hactive hw hM hwidth hd k)
    _ = _ := by rw [integral_const_mul, integral_faceMoment_shift_eq S s A V hV hp k]

/-- The localized Gaussian weighted face estimate against an actual
independent bounded base. All compatible active sets are summed, with no
cardinality loss. -/
theorem sum_shiftedFaceMoment_mul_width_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n q : ℕ} {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ j, (A * A.transpose) j j = ρ)
    (hq0 : 0 < q) (hq : q ≤ 4) {width M : ℝ} (hw : 0 < width)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt ρ * width ≤ 1 / M)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    width ^ q * (q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q,
        shiftedFaceMoment μ (compatibleSetTuple T) s A (sumVector ξ) k) ≤
      (2 : ℝ) ^ k *
        (1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v)) *
        ((Real.sqrt (dimensionLog p)) ^ k * Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2)) := by
  classical
  have hactive (T : CompatibleFaceSets s.faces q) (i : Fin q) :
      (compatibleSetTuple T).face i ∈ s.faces := by
    apply T.property.1
    rw [← activeFaces_compatibleSetTuple T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  calc
    _ = ∑ T : CompatibleFaceSets s.faces q,
        ∫ z, imageRatioWeight (compatibleSetTuple T) s A (sumVector ξ z.2) width
          (projectionPolynomial A k) z.1
          ∂((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro T _
      exact (imageRatioWeight_integral_shift_eq_faceMoment _ s A (sumVector ξ) h.measurable_sum
        hp hq0 hq hρ.le hA (hactive T) hw.le hM hwidth (hd T) k).symm
    _ ≤ _ := sum_all_imageRatioWeight_le_local h hp hv hdiag s A hρ hA hq0 hq hw hM hwidth hd k

def faceTubeWidth (p q : ℕ) (v : ℝ) : ℝ :=
  1 / ((q : ℝ) * Real.sqrt v * Real.sqrt (dimensionLog p))

theorem faceTubeWidth_pos {p q : ℕ} (hp : 1 ≤ p) (hq : 0 < q)
    {v : ℝ} (hv : 0 < v) : 0 < faceTubeWidth p q v := by
  have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq
  have hL : 0 < Real.sqrt (dimensionLog p) :=
    lt_of_lt_of_le zero_lt_one (sqrt_dimensionLog_ge_one hp)
  unfold faceTubeWidth
  positivity

theorem faceTubeWidth_normalization {p q : ℕ} (hp : 1 ≤ p) (hq : 0 < q)
    {v : ℝ} (hv : 0 < v) :
    (q : ℝ) * Real.sqrt v * faceTubeWidth p q v = 1 / Real.sqrt (dimensionLog p) := by
  have hq' : (q : ℝ) ≠ 0 := ne_of_gt (Nat.cast_pos.mpr hq)
  have hv' : Real.sqrt v ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hv)
  have hL : Real.sqrt (dimensionLog p) ≠ 0 :=
    ne_of_gt (lt_of_lt_of_le zero_lt_one (sqrt_dimensionLog_ge_one hp))
  unfold faceTubeWidth
  field_simp [hq', hv', hL]

theorem faceTubeWidth_variance_normalization {p q : ℕ} (hp : 1 ≤ p) (hq : 0 < q)
    {v : ℝ} (hv : 0 < v) :
    (q : ℝ) * v * faceTubeWidth p q v = Real.sqrt v / Real.sqrt (dimensionLog p) := by
  have hh := faceTubeWidth_normalization hp hq hv
  have hs := Real.sq_sqrt hv.le
  calc
    _ = (q : ℝ) * (Real.sqrt v) ^ 2 * faceTubeWidth p q v := by rw [hs]
    _ = Real.sqrt v * ((q : ℝ) * Real.sqrt v * faceTubeWidth p q v) := by ring
    _ = _ := by rw [hh]; ring

/-- Direct global rate after choosing the tube width. This is the ordered
face normalization: the factorial exactly matches the number of orders of
each compatible face set. -/
theorem sum_faceMoment_le {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    (q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q, faceMoment (compatibleSetTuple T) s A r k) ≤
      (2 : ℝ) ^ k * (q : ℝ) ^ q * (Real.sqrt v) ^ q *
        (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  let D := (q : ℝ) * Real.sqrt v * Real.sqrt (dimensionLog p)
  have hD : 0 < D := by
    have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
    have hL : 0 < Real.sqrt (dimensionLog p) :=
      lt_of_lt_of_le zero_lt_one (sqrt_dimensionLog_ge_one hp)
    dsimp [D]
    positivity
  have hh := sum_faceMoment_mul_width_le s A r hp hq0 hq hv.le hdiag
    (faceTubeWidth_pos hp hq0 hv).le (le_refl (Real.sqrt (dimensionLog p)))
    (faceTubeWidth_normalization hp hq0 hv).le hd k
  have hdiv : ((q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q, faceMoment (compatibleSetTuple T) s A r k)) / D ^ q ≤
      (2 : ℝ) ^ k * (Real.sqrt (dimensionLog p)) ^ k *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
    simpa only [faceTubeWidth, D, one_div, inv_pow, div_eq_mul_inv, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have hmul := (div_le_iff₀ (pow_pos hD q)).mp hdiv
  convert hmul using 1
  dsimp only [D]
  rw [mul_pow, mul_pow, pow_add]
  ring

/-- Direct bounded-base local rate. The localization factor is
`(sqrt ρ + η sqrt L) / sqrt v`; no full covariance eigenvalue enters it. -/
theorem sum_shiftedFaceMoment_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n q : ℕ} {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ j, (A * A.transpose) j j = ρ)
    (hq0 : 0 < q) (hq : q ≤ 4)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det) (k : ℕ) :
    (q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q,
        shiftedFaceMoment μ (compatibleSetTuple T) s A (sumVector ξ) k) ≤
      (2 : ℝ) ^ k * 1073741824 * (q : ℝ) ^ q * (Real.sqrt ρ) ^ q *
        (Real.sqrt (dimensionLog p)) ^ (q + k) *
        Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) *
        (Real.sqrt ρ + η * Real.sqrt (dimensionLog p)) / Real.sqrt v := by
  let D := (q : ℝ) * Real.sqrt ρ * Real.sqrt (dimensionLog p)
  have hL : 0 < Real.sqrt (dimensionLog p) :=
    lt_of_lt_of_le zero_lt_one (sqrt_dimensionLog_ge_one hp)
  have hD : 0 < D := by
    have hq' : (0 : ℝ) < q := Nat.cast_pos.mpr hq0
    dsimp [D]
    positivity
  have hh := sum_shiftedFaceMoment_mul_width_le h hp hv hdiag s A hρ hA hq0 hq
    (faceTubeWidth_pos hp hq0 hρ) (le_refl (Real.sqrt (dimensionLog p)))
    (faceTubeWidth_normalization hp hq0 hρ).le hd k
  have hboundary : ((q : ℝ) * ρ * faceTubeWidth p q ρ + η) *
      Real.sqrt (dimensionLog p / v) =
        (Real.sqrt ρ + η * Real.sqrt (dimensionLog p)) / Real.sqrt v := by
    rw [faceTubeWidth_variance_normalization hp hq0 hρ,
      Real.sqrt_div (show 0 ≤ dimensionLog p from
        le_trans zero_le_one (log_exp_mul_nat_ge_one hp))]
    field_simp [hL.ne']
  have hdiv : ((q.factorial : ℝ) *
      (∑ T : CompatibleFaceSets s.faces q,
        shiftedFaceMoment μ (compatibleSetTuple T) s A (sumVector ξ) k)) / D ^ q ≤
      (2 : ℝ) ^ k * 1073741824 *
        ((Real.sqrt ρ + η * Real.sqrt (dimensionLog p)) / Real.sqrt v) *
        ((Real.sqrt (dimensionLog p)) ^ k * Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2)) := by
    have hh' := hh
    rw [mul_assoc (1073741824 : ℝ), hboundary] at hh'
    simpa only [faceTubeWidth, D, one_div, inv_pow, div_eq_mul_inv, one_mul,
      mul_assoc, mul_left_comm, mul_comm] using hh'
  have hmul := (div_le_iff₀ (pow_pos hD q)).mp hdiv
  convert hmul using 1
  dsimp only [D]
  rw [mul_pow, mul_pow, pow_add]
  ring

theorem faceMoment_eq_canonical {p q : ℕ} {faces : Finset (Face p)}
    (S : OrderedFaceTuples faces q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (k : ℕ) :
    faceMoment S.val s A r k = faceMoment (compatibleSetTuple (tupleActiveSet S)) s A r k := by
  have hset : activeFaces S.val = activeFaces (compatibleSetTuple (tupleActiveSet S)) := by
    rw [activeFaces_compatibleSetTuple]
    rfl
  unfold faceMoment
  rw [normalMatrix_gram, normalMatrix_gram, gram_det_eq_canonical, hset]

theorem sum_ordered_faceMoment_eq_factorial {p q : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (k : ℕ) :
    (∑ S : OrderedFaceTuples s.faces q, faceMoment S.val s A r k) =
      (q.factorial : ℝ) *
        ∑ T : CompatibleFaceSets s.faces q, faceMoment (compatibleSetTuple T) s A r k := by
  classical
  calc
    _ = ∑ S : OrderedFaceTuples s.faces q,
        faceMoment (compatibleSetTuple (tupleActiveSet S)) s A r k :=
      Finset.sum_congr rfl (fun S _ => faceMoment_eq_canonical S s A r k)
    _ = _ := sum_orderedFaceTuples_eq_factorial s.faces
      (fun T => faceMoment (compatibleSetTuple T) s A r k)

theorem shiftedFaceMoment_eq_canonical
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p q : ℕ} {faces : Finset (Face p)} (S : OrderedFaceTuples faces q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (k : ℕ) :
    shiftedFaceMoment μ S.val s A V k =
      shiftedFaceMoment μ (compatibleSetTuple (tupleActiveSet S)) s A V k := by
  have hset : activeFaces S.val = activeFaces (compatibleSetTuple (tupleActiveSet S)) := by
    rw [activeFaces_compatibleSetTuple]
    rfl
  unfold shiftedFaceMoment
  rw [normalMatrix_gram, normalMatrix_gram, gram_det_eq_canonical, hset]

theorem sum_ordered_shiftedFaceMoment_eq_factorial
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    {p q : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (k : ℕ) :
    (∑ S : OrderedFaceTuples s.faces q, shiftedFaceMoment μ S.val s A V k) =
      (q.factorial : ℝ) *
        ∑ T : CompatibleFaceSets s.faces q, shiftedFaceMoment μ (compatibleSetTuple T) s A V k := by
  classical
  calc
    _ = ∑ S : OrderedFaceTuples s.faces q,
        shiftedFaceMoment μ (compatibleSetTuple (tupleActiveSet S)) s A V k :=
      Finset.sum_congr rfl (fun S _ => shiftedFaceMoment_eq_canonical μ S s A V k)
    _ = _ := sum_orderedFaceTuples_eq_factorial s.faces
      (fun T => shiftedFaceMoment μ (compatibleSetTuple T) s A V k)

end
end RectangleCLT.GaussianTube
