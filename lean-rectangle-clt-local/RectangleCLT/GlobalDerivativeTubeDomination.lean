import RectangleCLT.GlobalDerivativeTubeTransport

/-! Quantitative density and normalized-score control along actual full-dual
Gaussian tubes. Width is measured in physical coordinate units. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

theorem faceDot_fullDualMatrix_mulVec {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) (z : Vector p) :
    faceDot ((fullDualMatrix S A).mulVec u) z =
      ∑ i, u i * faceSign (S.face i) * faceDot (fullGaussianDual A (S.face i).1) z := by
  have hcol (i : Fin q) : (fullDualMatrix S A).transpose.mulVec z i =
      faceSign (S.face i) * faceDot (fullGaussianDual A (S.face i).1) z := by
    simp only [Matrix.mulVec, dotProduct, Matrix.transpose_apply, fullDualMatrix,
      faceDot, Finset.mul_sum, mul_assoc]
  rw [faceDot_mulVec]
  change (∑ i, u i * (fullDualMatrix S A).transpose.mulVec z i) = _
  simp_rw [hcol]
  exact Finset.sum_congr rfl (fun _ _ => by ring)

theorem abs_faceDot_fullDualMatrix_mulVec_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν width : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) (z : Vector p) :
    |faceDot ((fullDualMatrix S A).mulVec u) z| ≤
      (q : ℝ) * width * (‖normalizedFullGaussianScoreFamily A ν z‖ / Real.sqrt ν) := by
  rw [faceDot_fullDualMatrix_mulVec]
  calc
    _ ≤ ∑ i, |u i * faceSign (S.face i) * faceDot (fullGaussianDual A (S.face i).1) z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin q, width * (‖normalizedFullGaussianScoreFamily A ν z‖ / Real.sqrt ν) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [abs_mul, abs_faceSign, mul_one]
      exact mul_le_mul (hu i) (abs_faceDot_fullGaussianDual_le_scoreMaximum A hν z _)
        (abs_nonneg _) hw
    _ = _ := by simp; ring

theorem abs_faceDot_fullGaussianDual_displacement_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν width : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) (j : Fin p) :
    |faceDot (fullGaussianDual A j) ((fullDualMatrix S A).mulVec u)| ≤
      (q : ℝ) * width / ν := by
  rw [faceDot_comm, faceDot_fullDualMatrix_mulVec]
  calc
    _ ≤ ∑ i, |u i * faceSign (S.face i) *
        faceDot (fullGaussianDual A (S.face i).1) (fullGaussianDual A j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _ : Fin q, width * (1 / ν) := by
      apply Finset.sum_le_sum
      intro i _
      simp only [abs_mul, abs_faceSign, mul_one]
      exact mul_le_mul (hu i) (abs_faceDot_fullGaussianDual_le_inv A hν hlower _ j)
        (abs_nonneg _) hw
    _ = _ := by simp; ring

theorem normalizedFullGaussianScoreFamily_displacement_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν width : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) :
    ‖normalizedFullGaussianScoreFamily A ν ((fullDualMatrix S A).mulVec u)‖ ≤
      (q : ℝ) * width / Real.sqrt ν := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro j
  rw [Real.norm_eq_abs, normalizedFullGaussianScoreFamily_apply, abs_mul,
    abs_of_pos (Real.sqrt_pos.mpr hν)]
  calc
    _ ≤ Real.sqrt ν * ((q : ℝ) * width / ν) := mul_le_mul_of_nonneg_left
      (abs_faceDot_fullGaussianDual_displacement_le S A hν hw hlower u hu j)
      (Real.sqrt_nonneg ν)
    _ = ((q : ℝ) * width) * (Real.sqrt ν / ν) := by ring
    _ = ((q : ℝ) * width) * (1 / Real.sqrt ν) := by rw [Real.sqrt_div_self']
    _ = _ := by ring

theorem normalizedFullGaussianScoreFamily_sub {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (z d : Vector p) :
    normalizedFullGaussianScoreFamily A ν (z - d) =
      normalizedFullGaussianScoreFamily A ν z - normalizedFullGaussianScoreFamily A ν d := by
  ext j
  simp only [normalizedFullGaussianScoreFamily, linearProjectionFamily, Pi.sub_apply,
    mul_sub, Finset.sum_sub_distrib]

theorem normalizedFullGaussianScoreFamily_sub_displacement_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν width : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) (z : Vector p) :
    ‖normalizedFullGaussianScoreFamily A ν (z - (fullDualMatrix S A).mulVec u)‖ ≤
      ‖normalizedFullGaussianScoreFamily A ν z‖ + (q : ℝ) * width / Real.sqrt ν := by
  rw [normalizedFullGaussianScoreFamily_sub]
  exact (norm_sub_le _ _).trans (add_le_add_left
    (normalizedFullGaussianScoreFamily_displacement_le S A hν hw hlower u hu) _)

theorem dual_density_displacement_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    {ν width : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (u : Fin q → ℝ) (hu : ∀ i, |u i| ≤ width) (z : Vector p) :
    standardGaussianDensity p (z - (fullDualMatrix S A).mulVec u) ≤
      standardGaussianDensity p z * Real.exp ((q : ℝ) * width / Real.sqrt ν *
        ‖normalizedFullGaussianScoreFamily A ν z‖) := by
  rw [standardGaussianDensity_sub]
  apply mul_le_mul_of_nonneg_left _ (standardGaussianDensity_pos p z).le
  apply Real.exp_le_exp.mpr
  calc
    _ ≤ faceDot ((fullDualMatrix S A).mulVec u) z :=
      sub_le_self _ (div_nonneg (vectorNormSq_nonneg _) (by norm_num))
    _ ≤ |faceDot ((fullDualMatrix S A).mulVec u) z| := le_abs_self _
    _ ≤ (q : ℝ) * width *
        (‖normalizedFullGaussianScoreFamily A ν z‖ / Real.sqrt ν) :=
      abs_faceDot_fullDualMatrix_mulVec_le S A hν hw u hu z
    _ = _ := by ring

theorem dual_tube_density_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (E₀ : ℝ) (e : Face p → ℝ)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) :
    standardGaussianDensity p (base w) ≤
      standardGaussianDensity p (base (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth E₀ (activeOffsets S s r) w)) *
      Real.exp (‖normalizedFullGaussianScoreFamily A ν
        (base (dualMap (normalMatrix S A) (fullDualMatrix S A)
          s.bandwidth E₀ (activeOffsets S s r) w))‖ / M) := by
  let y := base w + (fullDualMatrix S A).mulVec (tube w)
  have hu (i : Fin q) : |tube w i| ≤ width := by
    rw [abs_of_pos (hsource.1 i).1]
    exact (hsource.1 i).2.le
  have hh := dual_density_displacement_le S A hν hw (tube w) hu y
  have hy : y - (fullDualMatrix S A).mulVec (tube w) = base w :=
    add_sub_cancel_right _ _
  rw [hy] at hh
  apply hh.trans
  apply mul_le_mul_of_nonneg_left _ (standardGaussianDensity_pos p y).le
  apply Real.exp_le_exp.mpr
  simpa only [one_div_mul_eq_div] using
    mul_le_mul_of_nonneg_right hwidth (norm_nonneg (normalizedFullGaussianScoreFamily A ν y))

theorem dual_tube_scoreRadius_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (E₀ : ℝ) (e : Face p → ℝ)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (w : Coordinates p q) (hsource : w ∈ sourceDomain S s A r E₀ e width) :
    ‖normalizedFullGaussianScoreFamily A ν (base w)‖ ≤
      ‖normalizedFullGaussianScoreFamily A ν
        (base (dualMap (normalMatrix S A) (fullDualMatrix S A)
          s.bandwidth E₀ (activeOffsets S s r) w))‖ + 1 / M := by
  let y := base w + (fullDualMatrix S A).mulVec (tube w)
  have hu (i : Fin q) : |tube w i| ≤ width := by
    rw [abs_of_pos (hsource.1 i).1]
    exact (hsource.1 i).2.le
  have hh := normalizedFullGaussianScoreFamily_sub_displacement_le
    S A hν hw hlower (tube w) hu y
  have hy : y - (fullDualMatrix S A).mulVec (tube w) = base w :=
    add_sub_cancel_right _ _
  rw [hy] at hh
  exact hh.trans (add_le_add_left hwidth _)

def fullScorePolynomial {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ)
    (k : ℕ) (z : Vector p) : ℝ :=
  (1 + ‖normalizedFullGaussianScoreFamily A ν z‖) ^ k

def fullScoreTubeWeight {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (ν M : ℝ) (k : ℕ) (z : Vector p) : ℝ :=
  Real.exp (‖normalizedFullGaussianScoreFamily A ν z‖ / M) * fullScorePolynomial A ν k z

theorem fullScorePolynomial_measurable {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (k : ℕ) :
    Measurable (fullScorePolynomial A ν k) := by
  exact (measurable_const.add ((measurable_linearProjectionFamily
    (fun j k => Real.sqrt ν * fullGaussianDual A j k)).norm)).pow_const k

theorem fullScorePolynomial_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν : ℝ) (k : ℕ) (z : Vector p) :
    0 ≤ fullScorePolynomial A ν k z := by
  unfold fullScorePolynomial
  positivity

theorem fullScoreTubeWeight_measurable {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν M : ℝ) (k : ℕ) :
    Measurable (fullScoreTubeWeight A ν M k) := by
  exact ((((measurable_linearProjectionFamily
    (fun j k => Real.sqrt ν * fullGaussianDual A j k)).norm).div_const M).exp).mul
      (fullScorePolynomial_measurable A ν k)

theorem fullScoreTubeWeight_weighted_moment_le {p : ℕ}
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν M : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (fullScoreTubeWeight A ν M k) (standardGaussian p) ∧
      (∫ z, fullScoreTubeWeight A ν M k z ∂standardGaussian p) ≤
        (Real.sqrt (dimensionLog p)) ^ k * Real.exp (2 + (k + 1 : ℝ) ^ 2 / 2) := by
  letI : Nonempty (Fin p) := ⟨⟨0, hp⟩⟩
  have hL : 1 ≤ dimensionLog p := log_exp_mul_nat_ge_one hp
  have hp₀ : (0 : ℝ) < p := by exact_mod_cast (show 0 < p from hp)
  have hcard : 2 * (Fintype.card (Fin p) : ℝ) ≤ Real.exp (2 * dimensionLog p) := by
    simp only [Fintype.card_fin]
    have he : (2 : ℝ) ≤ Real.exp 1 := by
      simpa only [one_add_one_eq_two] using Real.add_one_le_exp (1 : ℝ)
    calc
      2 * (p : ℝ) ≤ Real.exp 1 * (p : ℝ) := mul_le_mul_of_nonneg_right he hp₀.le
      _ = Real.exp (dimensionLog p) := by
        rw [dimensionLog, Real.exp_log (mul_pos (Real.exp_pos 1) hp₀)]
      _ ≤ Real.exp (2 * dimensionLog p) := Real.exp_le_exp.mpr (by linarith)
  have hh := projectionMaximum_weighted_moment_le
    (d := 1) (L := dimensionLog p) (C := 2) (M := M)
    (fun j k => Real.sqrt ν * fullGaussianDual A j k)
    (normalized_fullGaussianDual_normSq_le_one A hν hlower)
    (fun z => ‖normalizedFullGaussianScoreFamily A ν z‖)
    (measurable_linearProjectionFamily (fun j k => Real.sqrt ν * fullGaussianDual A j k)).norm
    (fun z => norm_nonneg _) hL hcard (fun z => by simp [normalizedFullGaussianScoreFamily]) hM k
  simpa only [fullScoreTubeWeight, fullScorePolynomial, one_mul] using hh

theorem fullScorePolynomial_integrable {p : ℕ}
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ) {ν : ℝ} (hν : 0 < ν)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (k : ℕ) : Integrable (fullScorePolynomial A ν k) (standardGaussian p) := by
  have hi := (fullScoreTubeWeight_weighted_moment_le hp A hν hlower le_rfl k).1
  apply hi.mono' (fullScorePolynomial_measurable A ν k).aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (fullScorePolynomial_nonneg A ν k z)]
    unfold fullScoreTubeWeight
    apply le_mul_of_one_le_left (fullScorePolynomial_nonneg A ν k z)
    exact Real.one_le_exp_iff.mpr (div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _))

theorem dualImageRatioWeight_polynomial_le {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width) (hM : 1 ≤ M)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (k : ℕ) (ze : Vector p × (ℝ × (Face p → ℝ))) :
    dualImageRatioWeight S s A r width (fullScorePolynomial A ν k) ze ≤
      (2 : ℝ) ^ k * fullScoreTubeWeight A ν M k ze.1 *
        (dualImageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze := by
  classical
  have hd := factor_covariance_det_isUnit_of_full_lower A hν hlower
  by_cases hevent : ze ∈ dualImageEvent S s A r width
  · have hp := (dualImageEvent_iff_preimage S s A r width hd ze).mp hevent
    let w := dualImagePreimage S s A (r, ze)
    have hsource : w ∈ sourceDomain S s A r ze.2.1 ze.2.2 width := hp.2.2
    have hmap := dualMap_dualInverse (normalMatrix S A) (fullDualMatrix S A)
      (normalMatrix_transpose_mul_fullDualMatrix S A hd) s.bandwidth_pos.ne'
      hp.1 (activeOffsets S s r)
      (Sum.elim ze.1 (fun i => ze.2.2 (S.face i))) (fun i => hp.2.1 (S.face i))
    have hbase : base (dualMap (normalMatrix S A) (fullDualMatrix S A)
        s.bandwidth ze.2.1 (activeOffsets S s r) w) = ze.1 := congrArg base hmap
    have hden := dual_tube_density_le S s A r hν hw ze.2.1 ze.2.2 hwidth w hsource
    rw [hbase] at hden
    have hden' : standardGaussianDensity p (base w) / standardGaussianDensity p ze.1 ≤
        Real.exp (‖normalizedFullGaussianScoreFamily A ν ze.1‖ / M) := by
      apply (div_le_iff₀ (standardGaussianDensity_pos p ze.1)).mpr
      simpa only [mul_comm] using hden
    have hradius := dual_tube_scoreRadius_le S s A r hν hw hlower
      ze.2.1 ze.2.2 hwidth w hsource
    rw [hbase] at hradius
    have hiM : 1 / M ≤ 1 := by
      simpa only [one_div_one] using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hM
    have hpoly : fullScorePolynomial A ν k (base w) ≤
        (2 : ℝ) ^ k * fullScorePolynomial A ν k ze.1 := by
      unfold fullScorePolynomial
      calc
        _ ≤ (2 * (1 + ‖normalizedFullGaussianScoreFamily A ν ze.1‖)) ^ k := by
          apply pow_le_pow_left₀ (by positivity)
          linarith [norm_nonneg (normalizedFullGaussianScoreFamily A ν ze.1)]
        _ = _ := mul_pow _ _ _
    simp only [dualImageRatioWeight, Set.indicator_of_mem hevent, mul_one]
    change (standardGaussianDensity p (base w) / standardGaussianDensity p ze.1) *
      fullScorePolynomial A ν k (base w) ≤ _
    calc
      _ ≤ Real.exp (‖normalizedFullGaussianScoreFamily A ν ze.1‖ / M) *
          ((2 : ℝ) ^ k * fullScorePolynomial A ν k ze.1) :=
        mul_le_mul hden' hpoly (by unfold fullScorePolynomial; positivity) (Real.exp_nonneg _)
      _ = _ := by unfold fullScoreTubeWeight; ring
  · simp [dualImageRatioWeight, Set.indicator_of_not_mem hevent]

theorem dualImageRatioWeight_nonneg {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (g : Vector p → ℝ) (hg : ∀ z, 0 ≤ g z)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    0 ≤ dualImageRatioWeight S s A r width g ze := by
  classical
  unfold dualImageRatioWeight
  by_cases hz : ze ∈ dualImageEvent S s A r width
  · rw [Set.indicator_of_mem hz]
    exact mul_nonneg (div_nonneg (standardGaussianDensity_pos _ _).le
      (standardGaussianDensity_pos _ _).le) (hg _)
  · rw [Set.indicator_of_not_mem hz]

theorem fullScoreTubeWeight_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (ν M : ℝ) (k : ℕ) (z : Vector p) :
    0 ≤ fullScoreTubeWeight A ν M k z :=
  mul_nonneg (Real.exp_nonneg _) (fullScorePolynomial_nonneg A ν k z)

theorem dualImageRatioWeight_polynomial_integrable {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (hp : 1 ≤ p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M) (k : ℕ) :
    Integrable (dualImageRatioWeight S s A r width (fullScorePolynomial A ν k))
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
  have hMone : 1 ≤ M := (Real.one_le_sqrt.mpr (log_exp_mul_nat_ge_one hp)).trans hM
  have hbase : Integrable
      (fun ze : Vector p × (ℝ × (Face p → ℝ)) => fullScoreTubeWeight A ν M k ze.1)
      ((standardGaussian p).prod (exponentialRectangleLaw p)) := by
    simpa only [mul_one] using
      (fullScoreTubeWeight_weighted_moment_le hp A hν hlower hM k).1.mul_prod
        (integrable_const (1 : ℝ) (μ := exponentialRectangleLaw p))
  apply (hbase.const_mul ((2 : ℝ) ^ k)).mono'
    (dualImageRatioWeight_measurable S s A r width _
      (fullScorePolynomial_measurable A ν k)
      (factor_covariance_det_isUnit_of_full_lower A hν hlower)).aestronglyMeasurable
  exact ae_of_all _ fun ze => by
    rw [Real.norm_eq_abs, abs_of_nonneg
      (dualImageRatioWeight_nonneg S s A r width _ (fullScorePolynomial_nonneg A ν k) ze)]
    calc
      _ ≤ (2 : ℝ) ^ k * fullScoreTubeWeight A ν M k ze.1 *
          (dualImageEvent S s A r width).indicator (fun _ => (1 : ℝ)) ze :=
        dualImageRatioWeight_polynomial_le S s A r hν hw hMone hlower hwidth k ze
      _ ≤ _ := by
        apply mul_le_of_le_one_right
          (mul_nonneg (pow_nonneg (by norm_num) k) (fullScoreTubeWeight_nonneg A ν M k ze.1))
        by_cases hz : ze ∈ dualImageEvent S s A r width <;> simp [hz]

/-- The real integral form of the exact full-dual transport normalization.
All integrability is obtained from the proved score-tube domination. -/
theorem integral_dualImageRatioWeight_eq_softFaceWeight {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (hp : 1 ≤ p)
    {ν width M : ℝ} (hν : 0 < ν) (hw : 0 ≤ width)
    (hlower : ∀ v, ν * vectorNormSq v ≤ matrixQuadratic (A * A.transpose) v)
    (hM : Real.sqrt (dimensionLog p) ≤ M)
    (hwidth : (q : ℝ) * width / Real.sqrt ν ≤ 1 / M)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hgram : 0 < ((normalMatrix S A).transpose * normalMatrix S A).det) (k : ℕ) :
    (∫ ze, dualImageRatioWeight S s A r width (fullScorePolynomial A ν k) ze
      ∂(standardGaussian p).prod (exponentialRectangleLaw p)) =
      width ^ q / s.bandwidth ^ q * (q.factorial : ℝ) *
        ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) *
          fullScorePolynomial A ν k z ∂standardGaussian p := by
  have hi := dualImageRatioWeight_polynomial_integrable S s A r hp hν hw hlower hM hwidth k
  have hn := ae_of_all ((standardGaussian p).prod (exponentialRectangleLaw p))
    (dualImageRatioWeight_nonneg S s A r width _ (fullScorePolynomial_nonneg A ν k))
  have hh := lintegral_dualImageRatioWeight_eq_softFaceWeight S s A r
    (fullScorePolynomial A ν k) (fullScorePolynomial_measurable A ν k)
    (fullScorePolynomial_integrable hp A hν hlower k) (fullScorePolynomial_nonneg A ν k)
    hactive hw (factor_covariance_det_isUnit_of_full_lower A hν hlower) hgram
  rw [← ofReal_integral_eq_lintegral_ofReal hi hn] at hh
  have hright : 0 ≤ width ^ q / s.bandwidth ^ q * (q.factorial : ℝ) *
      ∫ z, s.softFaceWeight (activeFaces S) (A.mulVec z + r) *
        fullScorePolynomial A ν k z ∂standardGaussian p :=
    mul_nonneg (mul_nonneg (div_nonneg (pow_nonneg hw q)
      (pow_nonneg s.bandwidth_pos.le q)) (Nat.cast_nonneg _))
      (integral_nonneg (fun z => mul_nonneg (s.softFaceWeight_nonneg _ _)
        (fullScorePolynomial_nonneg A ν k z)))
  have hreal := congrArg ENNReal.toReal hh
  rw [ENNReal.toReal_ofReal (integral_nonneg_of_ae hn), ENNReal.toReal_ofReal hright] at hreal
  exact hreal

end

end RectangleCLT.GaussianTube
