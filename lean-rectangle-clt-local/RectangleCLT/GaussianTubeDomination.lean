import RectangleCLT.GaussianTubeIntegration
import RectangleCLT.GaussianProjectionMaximum

/-! Quantitative Gaussian-density and projection-radius bounds on the actual
augmented tubes. The radius is a maximum over spans of at most four signed
normals, so no ambient-dimension factor enters the change of variables. -/

open MeasureTheory
open scoped BigOperators InnerProductSpace

namespace RectangleCLT.GaussianTube

noncomputable section

theorem projectionEuclideanVector_norm_sq {p : ℕ} (x : Vector p) :
    ‖projectionEuclideanVector x‖ ^ 2 = vectorNormSq x := by
  have hh := PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ) (projectionEuclideanVector x)
  simpa only [Real.norm_eq_abs, sq_abs, projectionEuclideanVector, vectorNormSq] using hh

theorem signedRowNormal_euclidean_norm {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ j, (A * A.transpose) j j = v) (f : Face p) :
    ‖projectionEuclideanVector (signedRowNormal A f)‖ = Real.sqrt v := by
  have hs := signedRowNormal_gram A f f
  have hss := faceSign_sq f
  rw [hdiag] at hs
  have hn : vectorNormSq (signedRowNormal A f) = v := by
    have he : vectorNormSq (signedRowNormal A f) =
        faceDot (signedRowNormal A f) (signedRowNormal A f) := by
      simp [vectorNormSq, faceDot, pow_two]
    rw [he]
    nlinarith
  have hnorm := projectionEuclideanVector_norm_sq (signedRowNormal A f)
  rw [hn] at hnorm
  nlinarith [Real.sq_sqrt hv, norm_nonneg (projectionEuclideanVector (signedRowNormal A f)),
    Real.sqrt_nonneg v]

theorem normalMatrix_mulVec_euclidean_sum {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) :
    projectionEuclideanVector ((normalMatrix S A).mulVec u) =
      ∑ i, u i • projectionEuclideanVector (signedRowNormal A (S.face i)) := by
  ext j
  change _ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin p => ℝ) j)
    (∑ i, u i • projectionEuclideanVector (signedRowNormal A (S.face i)))
  rw [map_sum]
  simp only [map_smul, PiLp.proj_apply, smul_eq_mul]
  change (normalMatrix S A).mulVec u j = ∑ i, u i * signedRowNormal A (S.face i) j
  simp only [normalMatrix, Matrix.mulVec, dotProduct, signedRowNormal]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem normalMatrix_mulVec_mem_normalSpan {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) :
    projectionEuclideanVector ((normalMatrix S A).mulVec u) ∈ S.normalSpan A := by
  rw [normalMatrix_mulVec_euclidean_sum]
  apply Submodule.sum_mem
  intro i _
  exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem normalMatrix_mulVec_norm_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v) {width : ℝ}
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) :
    ‖projectionEuclideanVector ((normalMatrix S A).mulVec u)‖ ≤
      (q : ℝ) * Real.sqrt v * width := by
  rw [normalMatrix_mulVec_euclidean_sum]
  calc
    _ ≤ ∑ i, ‖u i • projectionEuclideanVector (signedRowNormal A (S.face i))‖ :=
      norm_sum_le _ _
    _ = ∑ i, |u i| * Real.sqrt v := by
      simp only [norm_smul, Real.norm_eq_abs, signedRowNormal_euclidean_norm A hv hdiag]
    _ ≤ ∑ _ : Fin q, width * Real.sqrt v :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hu i) (Real.sqrt_nonneg v))
    _ = _ := by simp; ring

theorem sourceDomain_displacement_norm_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ j, (A * A.transpose) j j = v)
    (E₀ : ℝ) (e : Face p → ℝ) {width : ℝ} (_hw : 0 ≤ width)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) :
    ‖projectionEuclideanVector ((normalMatrix S A).mulVec (tube w))‖ ≤
      (q : ℝ) * Real.sqrt v * width := by
  apply normalMatrix_mulVec_norm_le S A hv hdiag
  intro i
  rw [abs_of_pos (hsource.1 i).1]
  exact (hsource.1 i).2.le

theorem standardGaussianDensity_sub {p : ℕ} (y d : Vector p) :
    standardGaussianDensity p (y - d) = standardGaussianDensity p y *
      Real.exp (faceDot d y - vectorNormSq d / 2) := by
  have hn : vectorNormSq (-d) = vectorNormSq d := by
    simp [vectorNormSq]
  have hd : faceDot (-d) y = -faceDot d y := by
    simp [faceDot, Finset.sum_neg_distrib]
  simpa only [sub_eq_add_neg, hn, hd, neg_neg] using
    standardGaussianDensity_translate y (-d)

theorem density_displacement_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (hq0 : 0 < q) (hq : q ≤ 4)
    (y d : Vector p) (hd : projectionEuclideanVector d ∈ S.normalSpan A) :
    standardGaussianDensity p (y - d) ≤ standardGaussianDensity p y *
      Real.exp (‖projectionEuclideanVector d‖ * fourFaceProjectionRadius A y) := by
  rw [standardGaussianDensity_sub]
  apply mul_le_mul_of_nonneg_left _ (standardGaussianDensity_pos p y).le
  apply Real.exp_le_exp.mpr
  exact (sub_le_self _ (div_nonneg (vectorNormSq_nonneg d) (by norm_num))).trans
    ((le_abs_self _).trans (S.abs_faceDot_normalSpan_le_projectionRadius A hq0 hq hd y))

theorem tube_density_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (E₀ : ℝ) (e : Face p → ℝ) {width M : ℝ} (hw : 0 ≤ width) (_hM : 0 < M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) :
    standardGaussianDensity p (base w) ≤
      standardGaussianDensity p
        (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)) *
      Real.exp (fourFaceProjectionRadius A
        (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)) / M) := by
  let d := (normalMatrix S A).mulVec (tube w)
  let y := base w + d
  have hnorm : ‖projectionEuclideanVector d‖ ≤ 1 / M :=
    (sourceDomain_displacement_norm_le S s A r hv hdiag E₀ e hw w hsource).trans hwidth
  have hh := density_displacement_le S A hq0 hq y d
    (normalMatrix_mulVec_mem_normalSpan S A (tube w))
  have hy : y - d = base w := by dsimp [y]; exact add_sub_cancel_right _ _
  rw [hy] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (standardGaussianDensity_pos p y).le
  apply Real.exp_le_exp.mpr
  simpa only [one_div_mul_eq_div] using
    mul_le_mul_of_nonneg_right hnorm (fourFaceProjectionRadius_nonneg A y)

theorem tube_projectionRadius_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {v : ℝ} (hv : 0 ≤ v) (hdiag : ∀ j, (A * A.transpose) j j = v)
    (E₀ : ℝ) (e : Face p → ℝ) {width M : ℝ} (hw : 0 ≤ width)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) :
    fourFaceProjectionRadius A (base w) ≤
      fourFaceProjectionRadius A
        (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)) + 1 / M := by
  let d := (normalMatrix S A).mulVec (tube w)
  let y := base w + d
  have hnorm : ‖projectionEuclideanVector d‖ ≤ 1 / M :=
    (sourceDomain_displacement_norm_le S s A r hv hdiag E₀ e hw w hsource).trans hwidth
  have hh := fourFaceProjectionRadius_add_le A y (-d)
  have hy : y + -d = base w := by dsimp [y]; exact add_neg_cancel_right _ _
  have hn : projectionEuclideanVector (-d) = -projectionEuclideanVector d := rfl
  rw [hy, hn, norm_neg] at hh
  exact hh.trans (add_le_add_left hnorm _)

theorem tube_density_polynomial_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    (E₀ : ℝ) (e : Face p → ℝ) {width M : ℝ} (hw : 0 ≤ width) (hM : 1 ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) (k : ℕ) :
    standardGaussianDensity p (base w) * (1 + fourFaceProjectionRadius A (base w)) ^ k ≤
      (2 : ℝ) ^ k * standardGaussianDensity p
        (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)) *
        (Real.exp (fourFaceProjectionRadius A
          (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)) / M) *
          (1 + fourFaceProjectionRadius A
            (base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w))) ^ k) := by
  let y := base (map (normalMatrix S A) s.bandwidth E₀ (activeOffsets S s r) w)
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hdens := tube_density_le S s A r hq0 hq hv hdiag E₀ e hw hMpos hwidth w hsource
  have hrad := tube_projectionRadius_le S s A r hv hdiag E₀ e hw hwidth w hsource
  have hinv : 1 / M ≤ 1 := (div_le_one hMpos).mpr hM
  have hp : (1 + fourFaceProjectionRadius A (base w)) ^ k ≤
      (2 * (1 + fourFaceProjectionRadius A y)) ^ k := by
    apply pow_le_pow_left₀ (by linarith [fourFaceProjectionRadius_nonneg A (base w)])
    dsimp only [y] at *
    nlinarith [fourFaceProjectionRadius_nonneg A y]
  have hh := mul_le_mul hdens hp
    (pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A (base w)]) k)
    (mul_nonneg (standardGaussianDensity_pos p y).le (Real.exp_nonneg _))
  apply hh.trans_eq
  rw [mul_pow]
  ring

theorem imageEvent_density_ratio_polynomial_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : 1 ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (ze : Vector p × (ℝ × (Face p → ℝ))) (hze : ze ∈ imageEvent S s A r width) (k : ℕ) :
    (standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
        standardGaussianDensity p ze.1) *
      (1 + fourFaceProjectionRadius A (base (imagePreimage S s A (r, ze)))) ^ k ≤
      (2 : ℝ) ^ k *
        (Real.exp (fourFaceProjectionRadius A ze.1 / M) *
          (1 + fourFaceProjectionRadius A ze.1) ^ k) := by
  have hh := (imageEvent_iff_preimage S s A r width hd ze).mp hze
  have hmap := map_inverse (normalMatrix S A) s.bandwidth_pos.ne' hh.1 hd
    (activeOffsets S s r) (Sum.elim ze.1 (fun i => ze.2.2 (S.face i)))
    (fun i => hh.2.1 (S.face i))
  change map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r)
    (imagePreimage S s A (r, ze)) = _ at hmap
  have hb : base (map (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r)
      (imagePreimage S s A (r, ze))) = ze.1 := by rw [hmap]; rfl
  have hdens := tube_density_polynomial_le S s A r hq0 hq hv hdiag ze.2.1 ze.2.2
    hw hM hwidth (imagePreimage S s A (r, ze)) hh.2.2 k
  rw [hb] at hdens
  rw [div_mul_eq_mul_div]
  apply (div_le_iff₀ (standardGaussianDensity_pos p ze.1)).mpr
  convert hdens using 1
  ring

/-- The actual common-space tube image, weighted by the recovered Gaussian
base and its Gaussian density ratio. This definition is shared with the
active-exponential transport theorem. -/
def imageRatioWeight {p q : ℕ} (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (g : Vector p → ℝ) (ze : Vector p × (ℝ × (Face p → ℝ))) : ℝ :=
  (imageEvent S s A r width).indicator (fun ze =>
    (standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
      standardGaussianDensity p ze.1) *
        g (base (imagePreimage S s A (r, ze)))) ze

theorem imageRatioWeight_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (g : Vector p → ℝ) (hg : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Measurable (imageRatioWeight S s A r width g) := by
  have hp : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      imagePreimage S s A (r, ze)) :=
    (measurable_imagePreimage S s A).comp (measurable_const.prodMk measurable_id)
  have hb : Measurable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      base (imagePreimage S s A (r, ze))) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp hp)
  have hevent : MeasurableSet (imageEvent S s A r width) :=
    (measurableSet_imageEvent_joint S s A width hd).preimage
      (measurable_const.prodMk measurable_id)
  exact ((((standardGaussianDensity_measurable p).comp hb).div
    ((standardGaussianDensity_measurable p).comp measurable_fst)).mul
      (hg.comp hb)).indicator hevent

theorem imageRatioWeight_joint_measurable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (width : ℝ)
    (g : Vector p → ℝ) (hg : Measurable g)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    Measurable (fun rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) =>
      imageRatioWeight S s A rze.1 width g rze.2) := by
  have hb : Measurable (fun rze : Vector p × (Vector p × (ℝ × (Face p → ℝ))) =>
      base (imagePreimage S s A rze)) :=
    measurable_pi_lambda _ (fun j =>
      (measurable_pi_apply (Sum.inl j : Fin p ⊕ Fin q)).comp (measurable_imagePreimage S s A))
  have hfun := (((standardGaussianDensity_measurable p).comp hb).div
    ((standardGaussianDensity_measurable p).comp (measurable_fst.comp measurable_snd))).mul
      (hg.comp hb)
  exact hfun.indicator (measurableSet_imageEvent_joint S s A width hd)

theorem imageRatioWeight_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (width : ℝ) (g : Vector p → ℝ) (hg : ∀ z, 0 ≤ g z)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    0 ≤ imageRatioWeight S s A r width g ze := by
  exact Set.indicator_nonneg (fun ze _ =>
    mul_nonneg (div_nonneg (standardGaussianDensity_pos p _).le
      (standardGaussianDensity_pos p _).le) (hg _)) _

theorem imageRatioWeight_projection_le {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : 1 ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (k : ℕ) (ze : Vector p × (ℝ × (Face p → ℝ))) :
    imageRatioWeight S s A r width (fun z => (1 + fourFaceProjectionRadius A z) ^ k) ze ≤
      (2 : ℝ) ^ k *
        (Real.exp (fourFaceProjectionRadius A ze.1 / M) *
          (1 + fourFaceProjectionRadius A ze.1) ^ k) *
        (imageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze := by
  classical
  by_cases hz : ze ∈ imageEvent S s A r width
  · simpa only [imageRatioWeight, Set.indicator_of_mem hz, mul_one] using
      imageEvent_density_ratio_polynomial_le S s A r hq0 hq hv hdiag hw hM hwidth hd ze hz k
  · simp only [imageRatioWeight, Set.indicator_of_not_mem hz, mul_zero, le_refl]

theorem imageRatioWeight_projection_integrable {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ} (hv : 0 ≤ v)
    (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    Integrable (imageRatioWeight S s A r width
      (fun z => (1 + fourFaceProjectionRadius A z) ^ k))
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
  have hMone : 1 ≤ M := by
    have hh := Real.sqrt_le_sqrt (log_exp_mul_nat_ge_one hp)
    rw [Real.sqrt_one] at hh
    exact hh.trans hM
  have hi := (fourFaceProjectionRadius_weighted_moment_le hp A hM k).1
  have hprod : Integrable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      (2 : ℝ) ^ k * (Real.exp (fourFaceProjectionRadius A ze.1 / M) *
        (1 + fourFaceProjectionRadius A ze.1) ^ k))
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
    simpa only [mul_one] using
      (hi.const_mul ((2 : ℝ) ^ k)).mul_prod
        (integrable_const (1 : ℝ) (μ := exponentialRectangleLaw p))
  apply hprod.mono'
    (imageRatioWeight_measurable S s A r width _
      ((measurable_const.add (measurable_fourFaceProjectionRadius A)).pow_const k) hd).aestronglyMeasurable
  exact ae_of_all _ (fun ze => by
    rw [Real.norm_eq_abs, abs_of_nonneg (imageRatioWeight_nonneg S s A r width _
      (fun z => pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A z]) k) ze)]
    have hh := imageRatioWeight_projection_le S s A r hq0 hq hv hdiag hw hMone hwidth hd k ze
    exact hh.trans (by
      by_cases hz : ze ∈ imageEvent S s A r width
      · simp only [Set.indicator_of_mem hz, mul_one]
        exact le_refl _
      · simp only [Set.indicator_of_not_mem hz, mul_zero]
        exact mul_nonneg (pow_nonneg (by norm_num) k)
          (mul_nonneg (Real.exp_nonneg _) (pow_nonneg
            (by linarith [fourFaceProjectionRadius_nonneg A ze.1]) k))))

theorem imageRatioWeight_projection_integrable_shift
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (hV : Measurable V) (hp : 1 ≤ p) (hq0 : 0 < q) (hq : q ≤ 4) {v : ℝ}
    (hv : 0 ≤ v) (hdiag : ∀ j, (A * A.transpose) j j = v)
    {width M : ℝ} (hw : 0 ≤ width) (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * Real.sqrt v * width ≤ 1 / M)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    Integrable
      (fun z : (Vector p × (ℝ × (Face p → ℝ))) × Ω =>
        imageRatioWeight S s A (V z.2) width
          (fun y => (1 + fourFaceProjectionRadius A y) ^ k) z.1)
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
  have hMone : 1 ≤ M := by
    have hh := Real.sqrt_le_sqrt (log_exp_mul_nat_ge_one hp)
    rw [Real.sqrt_one] at hh
    exact hh.trans hM
  have hi := (fourFaceProjectionRadius_weighted_moment_le hp A hM k).1
  have hcommon : Integrable (fun ze : Vector p × (ℝ × (Face p → ℝ)) =>
      (2 : ℝ) ^ k * (Real.exp (fourFaceProjectionRadius A ze.1 / M) *
        (1 + fourFaceProjectionRadius A ze.1) ^ k))
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
    simpa only [mul_one] using
      (hi.const_mul ((2 : ℝ) ^ k)).mul_prod
        (integrable_const (1 : ℝ) (μ := exponentialRectangleLaw p))
  have hprod : Integrable (fun z : (Vector p × (ℝ × (Face p → ℝ))) × Ω =>
      (2 : ℝ) ^ k * (Real.exp (fourFaceProjectionRadius A z.1.1 / M) *
        (1 + fourFaceProjectionRadius A z.1.1) ^ k))
      (((standardGaussian p).prod (exponentialRectangleLaw p)).prod μ) := by
    simpa only [mul_one] using hcommon.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  apply hprod.mono'
    ((imageRatioWeight_joint_measurable S s A width _
      ((measurable_const.add (measurable_fourFaceProjectionRadius A)).pow_const k) hd).comp
        ((hV.comp measurable_snd).prodMk measurable_fst)).aestronglyMeasurable
  exact ae_of_all _ (fun z => by
    dsimp only [Function.comp_apply]
    rw [Real.norm_eq_abs, abs_of_nonneg (imageRatioWeight_nonneg S s A (V z.2) width _
      (fun y => pow_nonneg (by linarith [fourFaceProjectionRadius_nonneg A y]) k) z.1)]
    have hh := imageRatioWeight_projection_le S s A (V z.2) hq0 hq hv hdiag hw hMone hwidth hd k z.1
    exact hh.trans (by
      by_cases hz : z.1 ∈ imageEvent S s A (V z.2) width
      · simp only [Set.indicator_of_mem hz, mul_one]
        exact le_refl _
      · simp only [Set.indicator_of_not_mem hz, mul_zero]
        exact mul_nonneg (pow_nonneg (by norm_num) k)
          (mul_nonneg (Real.exp_nonneg _) (pow_nonneg
            (by linarith [fourFaceProjectionRadius_nonneg A z.1.1]) k))))

end
end RectangleCLT.GaussianTube
