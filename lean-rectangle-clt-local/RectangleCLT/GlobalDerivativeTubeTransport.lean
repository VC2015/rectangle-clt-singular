import RectangleCLT.GlobalDerivativeTubeDisjoint
import RectangleCLT.GaussianTubeTransport

/-! Measurability and the exact common-experiment transport for the dual
Gaussian tubes. Source exponential integration is reused from the checked
local tube proof; its Gram determinant is divided out exactly. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.GaussianTube

noncomputable section

theorem measurableEmbedding_dualMap {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (hdual : N.transpose * U = 1)
    {h E₀ : ℝ} (hh : h ≠ 0) (hE₀ : E₀ ≠ 0) (a : Fin q → ℝ) :
    MeasurableEmbedding (dualMap N U h E₀ a) :=
  (contDiff_dualMap N U h E₀ a).continuous.measurableEmbedding
    (dualMap_injective N U hdual hh hE₀ a)

theorem image_dualMap_subset_positive_tube {p q : ℕ}
    (N U : Matrix (Fin p) (Fin q) ℝ) (h : ℝ) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (a : Fin q → ℝ) (D : Set (Coordinates p q)) :
    dualMap N U h E₀ a '' D ⊆ {y : Coordinates p q | ∀ i, 0 < tube y i} := by
  rintro y ⟨w, _, rfl⟩ i
  exact mul_pos hE₀ (Real.exp_pos _)

theorem measurableSet_dualImage_sourceDomain {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {E₀ : ℝ} (hE₀ : 0 < E₀) (e : Face p → ℝ) (width : ℝ)
    (hd : IsUnit (A * A.transpose).det) :
    MeasurableSet (dualMap (normalMatrix S A) (fullDualMatrix S A)
      s.bandwidth E₀ (activeOffsets S s r) '' sourceDomain S s A r E₀ e width) :=
  (measurableEmbedding_dualMap _ _ (normalMatrix_transpose_mul_fullDualMatrix S A hd)
    s.bandwidth_pos.ne' hE₀.ne' _).measurableSet_image.mpr
      (measurableSet_sourceDomain S s A r E₀ e width)

theorem dualImageEvent_iff_preimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (hd : IsUnit (A * A.transpose).det)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    ze ∈ dualImageEvent S s A r width ↔ 0 < ze.2.1 ∧ (∀ f, 0 < ze.2.2 f) ∧
      dualImagePreimage S s A (r, ze) ∈ sourceDomain S s A r ze.2.1 ze.2.2 width := by
  have hdual := normalMatrix_transpose_mul_fullDualMatrix S A hd
  constructor
  · rintro ⟨h0, he, w, hw, hmap⟩
    refine ⟨h0, he, ?_⟩
    change dualInverse _ _ s.bandwidth ze.2.1 (activeOffsets S s r)
      (Sum.elim ze.1 (fun i => ze.2.2 (S.face i))) ∈ _
    rw [← hmap, dualInverse_dualMap _ _ hdual s.bandwidth_pos.ne' h0.ne']
    exact hw
  · rintro ⟨h0, he, hw⟩
    refine ⟨h0, he, dualImagePreimage S s A (r, ze), hw, ?_⟩
    exact dualMap_dualInverse _ _ hdual s.bandwidth_pos.ne' h0 _ _
      (fun i => he (S.face i))

theorem measurable_dualImagePreimage {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) :
    Measurable (dualImagePreimage S s A) := by
  apply measurable_pi_lambda
  intro j
  cases j <;> simp only [dualImagePreimage, dualInverse, dualRecoveredTube,
    activeThreshold, activeOffsets, base, tube, Sum.elim_inl, Sum.elim_inr,
    Matrix.mulVec, dotProduct, Pi.sub_apply, normalDot_eq_faceSign_mul]
  all_goals fun_prop

theorem measurableSet_dualImageEvent_joint {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (width : ℝ)
    (hd : IsUnit (A * A.transpose).det) :
    MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
      rze.2 ∈ dualImageEvent S s A rze.1 width} := by
  simp_rw [dualImageEvent_iff_preimage S s A _ width hd]
  have hpre := measurable_dualImagePreimage S s A
  have hb : Measurable (fun rze => base (dualImagePreimage S s A rze)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hpre)
  have hW : Measurable (fun rze => A.mulVec (base (dualImagePreimage S s A rze)) + rze.1) :=
    ((measurable_mulVec A).comp hb).add measurable_fst
  change MeasurableSet {rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) |
    0 < rze.2.2.1 ∧ (∀ f, 0 < rze.2.2.2 f) ∧
      (∀ i, 0 < tube (dualImagePreimage S s A rze) i ∧
        tube (dualImagePreimage S s A rze) i < width) ∧
      ∀ f ∈ s.faces, f ∉ activeFaces S →
        rze.2.2.1 * (s.weights (A.mulVec (base (dualImagePreimage S s A rze)) + rze.1)).weight f <
          rze.2.2.2 f}
  simp only [Set.setOf_and, Set.setOf_forall]
  refine MeasurableSet.inter (measurableSet_lt measurable_const ?_)
    (MeasurableSet.inter (MeasurableSet.iInter (fun f => ?_))
      (MeasurableSet.inter (MeasurableSet.iInter (fun i => ?_))
        (MeasurableSet.iInter (fun f => MeasurableSet.iInter (fun _ =>
          MeasurableSet.iInter (fun _ => ?_))))))
  · fun_prop
  · exact measurableSet_lt measurable_const (by fun_prop)
  · have ht := (measurable_pi_apply (Sum.inr i : Fin p ⊕ Fin q)).comp hpre
    exact (measurableSet_lt measurable_const ht).inter (measurableSet_lt ht measurable_const)
  · have h0 : Measurable (fun rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) =>
        rze.2.2.1) := by fun_prop
    exact measurableSet_lt (h0.mul ((s.continuous_weight f).measurable.comp hW)) (by fun_prop)

def dualPulledDensity {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (E₀ : ℝ) (y : Coordinates p q) : ℝ :=
  standardGaussianDensity p (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
    s.bandwidth E₀ (activeOffsets S s r) y)) * Real.exp (-(∑ i, tube y i))

def dualSourceDensity {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (w : Coordinates p q) (re : ℝ × (Face p → ℝ)) : ℝ :=
  sourceDensity S s A r width w re / ((normalMatrix S A).transpose * normalMatrix S A).det

def dualImageRatioWeight {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (g : Vector p → ℝ) (ze : Vector p × (ℝ × (Face p → ℝ))) : ℝ :=
  (dualImageEvent S s A r width).indicator (fun ze =>
    (standardGaussianDensity p (base (dualImagePreimage S s A (r, ze))) /
      standardGaussianDensity p ze.1) * g (base (dualImagePreimage S s A (r, ze)))) ze

theorem dualImageRatioWeight_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (g : Vector p → ℝ) (hg : Measurable g)
    (hd : IsUnit (A * A.transpose).det) :
    Measurable (dualImageRatioWeight S s A r width g) := by
  have hp : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      dualImagePreimage S s A (r, ze)) :=
    (measurable_dualImagePreimage S s A).comp (measurable_const.prodMk measurable_id)
  have hb : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      base (dualImagePreimage S s A (r, ze))) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hp)
  have hevent : MeasurableSet (dualImageEvent S s A r width) :=
    (measurableSet_dualImageEvent_joint S s A width hd).preimage
      (measurable_const.prodMk measurable_id)
  exact ((((standardGaussianDensity_measurable p).comp hb).div
    ((standardGaussianDensity_measurable p).comp measurable_fst)).mul (hg.comp hb)).indicator hevent

theorem lintegral_dualPulledDensity_weighted_image_eq_sourceDensity {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (g : Vector p → ℝ)
    (hactive : ∀ i, S.face i ∈ s.faces) {E₀ : ℝ} (hE₀ : 0 < E₀)
    (e : Face p → ℝ) (width : ℝ) (hd : IsUnit (A * A.transpose).det)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ y in dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) '' sourceDomain S s A r E₀ e width,
      ENNReal.ofReal (dualPulledDensity S s A r E₀ y *
        g (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
          s.bandwidth E₀ (activeOffsets S s r) y)))) =
      ∫⁻ w, ENNReal.ofReal (dualSourceDensity S s A r width w (E₀, e) * g (base w)) := by
  have hdual := normalMatrix_transpose_mul_fullDualMatrix S A hd
  rw [lintegral_image_dualMap _ _ hdual s.bandwidth_pos hE₀ _
    (measurableSet_sourceDomain S s A r E₀ e width)]
  rw [← lintegral_indicator (measurableSet_sourceDomain S s A r E₀ e width)]
  apply lintegral_congr_ae
  filter_upwards [] with w
  by_cases hw : w ∈ sourceDomain S s A r E₀ e width
  · rw [Set.indicator_of_mem hw]
    have hi := dualInverse_dualMap _ _ hdual s.bandwidth_pos.ne' hE₀.ne'
      (activeOffsets S s r) w
    have hp : (∏ i, tube (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) w) i) =
        ∏ f ∈ activeFaces S, E₀ * (s.weights (A.mulVec (base w) + r)).weight f := by
      rw [activeFaces_prod]
      exact Finset.prod_congr rfl (fun i _ => activeExponential_eq S s A r hactive E₀ w i)
    have hs : (∑ i, tube (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) w) i) =
        activeMass (s.weights (A.mulVec (base w) + r)) (activeFaces S) * E₀ := by
      simp only [activeMass, activeFaces_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun i _ => by
        rw [show tube (dualMap (normalMatrix S A) (fullDualMatrix S A)
          s.bandwidth E₀ (activeOffsets S s r) w) i =
            tube (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w) i from rfl,
          activeExponential_eq S s A r hactive E₀ w i, mul_comm])
    have hj : 0 ≤ (∏ i, tube (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) w) i) / s.bandwidth ^ q := by
      apply div_nonneg (Finset.prod_nonneg (fun i _ => ?_)) (pow_nonneg s.bandwidth_pos.le _)
      exact (mul_pos hE₀ (Real.exp_pos _)).le
    rw [← ENNReal.ofReal_mul hj]
    simp only [dualPulledDensity, hi, hp, hs, dualSourceDensity,
      sourceDensity, Set.indicator_of_mem hw, mul_one]
    congr 1
    field_simp [hgram.ne', s.bandwidth_pos.ne']
    ring
  · simp only [Set.indicator_of_not_mem hw, dualSourceDensity, sourceDensity,
      mul_zero, zero_mul, zero_div, ENNReal.ofReal_zero]

theorem dualSourceDensity_integral_source_weighted {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (g : Vector p → ℝ)
    {width : ℝ} (hw : 0 ≤ width)
    (hgram : ((normalMatrix S A).transpose * normalMatrix S A).det ≠ 0) :
    (∫ w : Coordinates p q, ∫ re, dualSourceDensity S s A r width w re * g (base w)
      ∂exponentialRectangleLaw p) =
      width ^ q / s.bandwidth ^ q * (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p := by
  simp only [dualSourceDensity, div_mul_eq_mul_div, integral_div]
  rw [sourceDensity_integral_source_weighted S s A r g hw]
  field_simp [hgram, s.bandwidth_pos.ne']
  ring

theorem lintegral_dualPulledDensity_weighted_images {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    {width : ℝ} (hw : 0 ≤ width) (hd : IsUnit (A * A.transpose).det)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ re, ∫⁻ y in dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth re.1 (activeOffsets S s r) '' sourceDomain S s A r re.1 re.2 width,
      ENNReal.ofReal (dualPulledDensity S s A r re.1 y *
        g (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
          s.bandwidth re.1 (activeOffsets S s r) y)))
      ∂volume ∂exponentialRectangleLaw p) =
      ENNReal.ofReal (width ^ q / s.bandwidth ^ q * (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p) := by
  have hm : Measurable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      dualSourceDensity S s A r width z.1 z.2 * g (base z.1)) := by
    exact ((sourceDensity_measurable S s A r width).div_const _).mul
      (hgm.comp (measurable_pi_lambda _ (fun j =>
        (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp measurable_fst)))
  have hi : Integrable (fun z : Coordinates p q × (ℝ × (Face p → ℝ)) =>
      dualSourceDensity S s A r width z.1 z.2 * g (base z.1))
      (volume.prod (exponentialRectangleLaw p)) := by
    simpa only [dualSourceDensity, div_mul_eq_mul_div] using
      (sourceDensity_integrable_weighted S s A r g hgm hgi width hgram.le).div_const
        (((normalMatrix S A).transpose * normalMatrix S A).det)
  have hnonneg : ∀ᵐ z ∂volume.prod (exponentialRectangleLaw p),
      0 ≤ dualSourceDensity S s A r width z.1 z.2 * g (base z.1) := by
    filter_upwards [((Measure.quasiMeasurePreserving_snd (μ := (volume : Measure (Coordinates p q)))
      (ν := exponentialRectangleLaw p)).ae (exponentialRectangleLaw_ae_pos p))] with z hz
    exact mul_nonneg
      (div_nonneg (sourceDensity_nonneg S s A r width z.1 z.2 hz.1.le hgram.le) hgram.le)
      (hg0 _)
  calc
    _ = ∫⁻ re, ∫⁻ w, ENNReal.ofReal
        (dualSourceDensity S s A r width w re * g (base w))
        ∂volume ∂exponentialRectangleLaw p := by
      apply lintegral_congr_ae
      filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
      exact lintegral_dualPulledDensity_weighted_image_eq_sourceDensity
        S s A r g hactive hre.1 re.2 width hd hgram
    _ = ∫⁻ w, ∫⁻ re, ENNReal.ofReal
        (dualSourceDensity S s A r width w re * g (base w)) ∂exponentialRectangleLaw p :=
      (lintegral_lintegral_swap hm.ennreal_ofReal.aemeasurable).symm
    _ = ENNReal.ofReal (∫ w, ∫ re,
        dualSourceDensity S s A r width w re * g (base w) ∂exponentialRectangleLaw p) := by
      rw [lintegral_lintegral hm.ennreal_ofReal.aemeasurable,
        ← ofReal_integral_eq_lintegral_ofReal hi hnonneg, integral_prod _ hi]
    _ = _ := congrArg ENNReal.ofReal
      (dualSourceDensity_integral_source_weighted S s A r g hw hgram.ne')

theorem dualImageEvent_replaceActive_iff {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (a : Fin q → ℝ) (z : Vector p) (width : ℝ)
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (ha : ∀ i, 0 < a i) :
    (z, E₀, replaceActive S e a) ∈ dualImageEvent S s A r width ↔
      Sum.elim z a ∈ dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) '' sourceDomain S s A r E₀ e width := by
  simp only [dualImageEvent, Set.mem_setOf_eq, hE₀, replaceActive_pos S e a he ha,
    true_and, replaceActive_at, sourceDomain_replaceActive]
  simp

theorem dualImagePreimage_replaceActive {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (E₀ : ℝ) (e : Face p → ℝ) (y : Coordinates p q) :
    dualImagePreimage S s A (r, (base y, E₀, replaceActive S e (tube y))) =
      dualInverse (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) y := by
  unfold dualImagePreimage
  have hc : Sum.elim (base y) (fun i => replaceActive S e (tube y) (S.face i)) = y := by
    ext j
    cases j <;> simp [base, tube, replaceActive_at]
  rw [hc]

theorem density_mul_dualImageRatioWeight {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (g : Vector p → ℝ) (E₀ : ℝ) (e : Face p → ℝ)
    (hE₀ : 0 < E₀) (he : ∀ f, 0 < e f) (y : Coordinates p q)
    (hy : ∀ i, 0 < tube y i) :
    ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
      ENNReal.ofReal (dualImageRatioWeight S s A r width g
        (base y, E₀, replaceActive S e (tube y))) =
      (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) '' sourceDomain S s A r E₀ e width).indicator
        (fun y => ENNReal.ofReal (dualPulledDensity S s A r E₀ y *
          g (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
            s.bandwidth E₀ (activeOffsets S s r) y)))) y := by
  classical
  have hcoord : Sum.elim (base y) (tube y) = y := by
    ext j
    cases j <;> rfl
  have hevent := dualImageEvent_replaceActive_iff S s A r E₀ e (tube y) (base y)
    width hE₀ he hy
  rw [hcoord] at hevent
  by_cases hmem : y ∈ dualMap (normalMatrix S A) (fullDualMatrix S A)
      s.bandwidth E₀ (activeOffsets S s r) '' sourceDomain S s A r E₀ e width
  · have hze := hevent.mpr hmem
    simp only [dualImageRatioWeight, Set.indicator_of_mem hze, Set.indicator_of_mem hmem,
      dualImagePreimage_replaceActive]
    rw [← ENNReal.ofReal_mul
      (mul_nonneg (standardGaussianDensity_pos p (base y)).le (Real.exp_nonneg _))]
    apply congrArg ENNReal.ofReal
    unfold dualPulledDensity
    field_simp [(standardGaussianDensity_pos p (base y)).ne']
    ring
  · have hze := mt hevent.mp hmem
    simp only [dualImageRatioWeight, Set.indicator_of_not_mem hze, ENNReal.ofReal_zero,
      mul_zero, Set.indicator_of_not_mem hmem]

/-- Exact full-dual face normalization in the common Gaussian/exponential
experiment. There is no covariance or Gram determinant in the result. -/
theorem lintegral_dualImageRatioWeight_eq_softFaceWeight {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hactive : ∀ i, S.face i ∈ s.faces)
    {width : ℝ} (hw : 0 ≤ width) (hd : IsUnit (A * A.transpose).det)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) :
    (∫⁻ ze, ENNReal.ofReal (dualImageRatioWeight S s A r width g ze)
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      ENNReal.ofReal (width ^ q / s.bandwidth ^ q * (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) * g z ∂standardGaussian p) := by
  rw [lintegral_common_eq_active_volume S _
    (dualImageRatioWeight_measurable S s A r width g hgm hd).ennreal_ofReal]
  have hpositive : (∫⁻ re, ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
          ENNReal.ofReal (dualImageRatioWeight S s A r width g
            (base y, re.1, replaceActive S re.2 (tube y)))
        ∂volume ∂exponentialRectangleLaw p) =
      ∫⁻ re, ∫⁻ y in dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth re.1 (activeOffsets S s r) '' sourceDomain S s A r re.1 re.2 width,
        ENNReal.ofReal (dualPulledDensity S s A r re.1 y *
          g (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
            s.bandwidth re.1 (activeOffsets S s r) y)))
        ∂volume ∂exponentialRectangleLaw p := by
    apply lintegral_congr_ae
    filter_upwards [exponentialRectangleLaw_ae_pos p] with re hre
    calc
      _ = ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
          (dualMap (normalMatrix S A) (fullDualMatrix S A)
            s.bandwidth re.1 (activeOffsets S s r) '' sourceDomain S s A r re.1 re.2 width).indicator
            (fun y => ENNReal.ofReal (dualPulledDensity S s A r re.1 y *
              g (base (dualInverse (normalMatrix S A) (fullDualMatrix S A)
                s.bandwidth re.1 (activeOffsets S s r) y)))) y := by
        apply setLIntegral_congr_fun (measurableSet_positive_tube p q)
        exact ae_of_all _ fun y hy => density_mul_dualImageRatioWeight S s A r width g
          re.1 re.2 hre.1 hre.2 y hy
      _ = _ := by
        rw [setLIntegral_indicator
          (measurableSet_dualImage_sourceDomain S s A r hre.1 re.2 width hd),
          Set.inter_eq_left.mpr (image_dualMap_subset_positive_tube _ _ s.bandwidth hre.1 _ _)]
  rw [hpositive]
  exact lintegral_dualPulledDensity_weighted_images S s A r g hgm hgi hg0 hactive hw hd hgram

end

end RectangleCLT.GaussianTube
