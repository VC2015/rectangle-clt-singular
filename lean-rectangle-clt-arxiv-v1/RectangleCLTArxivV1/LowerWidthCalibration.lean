import RectangleCLTArxivV1.GaussianCalibration
import RectangleCLTCompanion.SplitV4.SymmetricFamilyGaussian
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Data.Real.StarOrdered

/-!
# Actual Gaussian widths for the two-count lower-bound grid

The new paper permits `r` leading coordinates and `m` rare coordinates,
independently. The archive's observation family has `r=m`. The law here is
the actual independent Gaussian-pair pushforward in either case; its width
estimates require no assumed lower-bound distribution or comparison rate.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators

/-- The prescribed width `w_n` in the frozen lower-bound statements. -/
noncomputable def independentAbsGaussianMean (r : ℕ) : ℝ :=
  ∫ g : Vector r, ‖g‖ ∂standardGaussian r

theorem gaussianLaw_one (r : ℕ) : gaussianLaw (1 : Matrix (Fin r) (Fin r) ℝ) = standardGaussian r := by
  unfold gaussianLaw
  have heq : (1 : Matrix (Fin r) (Fin r) ℝ).mulVec = id := funext (fun _ => Matrix.one_mulVec _)
  rw [heq, Measure.map_id]

theorem independentAbsGaussianMean_eq (r : ℕ) :
    independentAbsGaussianMean r = gaussianMaximumMean (1 : Matrix (Fin r) (Fin r) ℝ) := by
  simp only [independentAbsGaussianMean, gaussianMaximumMean, gaussianLaw_one]

theorem standardGaussian_integrable_norm (r : ℕ) :
    Integrable (fun g : Vector r => ‖g‖) (standardGaussian r) := by
  simpa only [gaussianLaw_one] using gaussianLaw_integrable_norm (1 : Matrix (Fin r) (Fin r) ℝ)

theorem independentAbsGaussianMean_nonneg (r : ℕ) : 0 ≤ independentAbsGaussianMean r :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem independentAbsGaussianMean_lower {r : ℕ} (hr : 1 ≤ r) :
    Real.sqrt (2 / Real.pi) ≤ independentAbsGaussianMean r := by
  rw [independentAbsGaussianMean_eq]
  apply sqrt_two_div_pi_le_gaussianMaximumMean hr
  intro j
  simp

theorem independentAbsGaussianMean_upper {r : ℕ} (hr : 1 ≤ r) :
    independentAbsGaussianMean r ≤ 2 * Real.sqrt (dimensionLog r) := by
  rw [independentAbsGaussianMean_eq]
  exact gaussianLaw_integral_norm_le hr _ (fun _ => by simp)

theorem independentAbsGaussianMean_one : independentAbsGaussianMean 1 = Real.sqrt (2 / Real.pi) := by
  have hnorm (g : Vector 1) : ‖g‖ = |g 0| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro j
      rw [Subsingleton.elim j 0, Real.norm_eq_abs]
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm g 0
  unfold independentAbsGaussianMean
  simp_rw [hnorm]
  have h := integral_map (μ := standardGaussian 1) (measurable_pi_apply (0 : Fin 1)).aemeasurable
    (f := fun x : ℝ => |x|) measurable_id.abs.aestronglyMeasurable
  rw [standardGaussian_map_eval, standardNormal_integral_abs] at h
  exact h.symm

/-- The concrete Gaussian counterpart `Z_{ju}=sG_j+tH_u`. -/
def lowerGridGaussianMap {r m : ℕ} (s t : ℝ) (z : Vector r × Vector m) : Vector (r * m) :=
  fun k => s * z.1 (finProdFinEquiv.symm k).1 + t * z.2 (finProdFinEquiv.symm k).2

theorem lowerGridGaussianMap_measurable (r m : ℕ) (s t : ℝ) :
    Measurable (lowerGridGaussianMap (r := r) (m := m) s t) := by
  apply measurable_pi_lambda
  intro k
  exact (measurable_const.mul ((measurable_pi_apply _).comp measurable_fst)).add
    (measurable_const.mul ((measurable_pi_apply _).comp measurable_snd))

noncomputable def lowerGridGaussianLaw (r m : ℕ) (s t : ℝ) : Measure (Vector (r * m)) :=
  ((standardGaussian r).prod (standardGaussian m)).map (lowerGridGaussianMap s t)

instance lowerGridGaussianLaw_probability (r m : ℕ) (s t : ℝ) :
    IsProbabilityMeasure (lowerGridGaussianLaw r m s t) :=
  isProbabilityMeasure_map (lowerGridGaussianMap_measurable r m s t).aemeasurable

noncomputable def lowerGridGaussianMean (r m : ℕ) (s t : ℝ) : ℝ :=
  ∫ z, ‖z‖ ∂lowerGridGaussianLaw r m s t

theorem lowerGridGaussianMean_eq_integral (r m : ℕ) (s t : ℝ) :
    lowerGridGaussianMean r m s t =
      ∫ z : Vector r × Vector m, ‖lowerGridGaussianMap s t z‖
        ∂(standardGaussian r).prod (standardGaussian m) := by
  unfold lowerGridGaussianMean lowerGridGaussianLaw
  rw [integral_map (lowerGridGaussianMap_measurable r m s t).aemeasurable
    measurable_norm.aestronglyMeasurable]

theorem lowerGridGaussianMap_norm_le {r m : ℕ} (s t : ℝ) (z : Vector r × Vector m) :
    ‖lowerGridGaussianMap s t z‖ ≤ |s| * ‖z.1‖ + |t| * ‖z.2‖ := by
  apply (pi_norm_le_iff_of_nonneg (by positivity)).mpr
  intro k
  rw [Real.norm_eq_abs]
  calc
    _ ≤ |s * z.1 (finProdFinEquiv.symm k).1| + |t * z.2 (finProdFinEquiv.symm k).2| := abs_add_le _ _
    _ = |s| * |z.1 (finProdFinEquiv.symm k).1| + |t| * |z.2 (finProdFinEquiv.symm k).2| := by
      rw [abs_mul, abs_mul]
    _ ≤ _ := add_le_add
      (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.1 _) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (by simpa only [Real.norm_eq_abs] using norm_le_pi_norm z.2 _) (abs_nonneg _))

theorem lowerGridGaussianMap_integrable_norm (r m : ℕ) (s t : ℝ) :
    Integrable (fun z : Vector r × Vector m => ‖lowerGridGaussianMap s t z‖)
      ((standardGaussian r).prod (standardGaussian m)) := by
  have h₁ : Integrable (fun z : Vector r × Vector m => ‖z.1‖)
      ((standardGaussian r).prod (standardGaussian m)) := by
    simpa only [mul_one] using (standardGaussian_integrable_norm r).mul_prod
      (integrable_const (1 : ℝ) : Integrable _ (standardGaussian m))
  have h₂ : Integrable (fun z : Vector r × Vector m => ‖z.2‖)
      ((standardGaussian r).prod (standardGaussian m)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable _ (standardGaussian r)).mul_prod
      (standardGaussian_integrable_norm m)
  apply ((h₁.const_mul |s|).add (h₂.const_mul |t|)).mono'
    (measurable_norm.comp (lowerGridGaussianMap_measurable r m s t)).aestronglyMeasurable
  apply ae_of_all
  intro z
  change ‖‖lowerGridGaussianMap s t z‖‖ ≤ |s| * ‖z.1‖ + |t| * ‖z.2‖
  rw [norm_norm]
  exact lowerGridGaussianMap_norm_le s t z

/-- The upper half of the printed family-width calibration. -/
theorem lowerGridGaussianMean_upper (r m : ℕ) (s t : ℝ) :
    lowerGridGaussianMean r m s t ≤ |s| * independentAbsGaussianMean r +
      |t| * independentAbsGaussianMean m := by
  rw [lowerGridGaussianMean_eq_integral]
  have h₁ : Integrable (fun z : Vector r × Vector m => |s| * ‖z.1‖)
      ((standardGaussian r).prod (standardGaussian m)) := by
    simpa only [mul_one] using ((standardGaussian_integrable_norm r).const_mul |s|).mul_prod
      (integrable_const (1 : ℝ) : Integrable _ (standardGaussian m))
  have h₂ : Integrable (fun z : Vector r × Vector m => |t| * ‖z.2‖)
      ((standardGaussian r).prod (standardGaussian m)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable _ (standardGaussian r)).mul_prod
      ((standardGaussian_integrable_norm m).const_mul |t|)
  calc
    _ ≤ ∫ z : Vector r × Vector m, |s| * ‖z.1‖ + |t| * ‖z.2‖
        ∂(standardGaussian r).prod (standardGaussian m) :=
      integral_mono (lowerGridGaussianMap_integrable_norm r m s t) (h₁.add h₂)
        (lowerGridGaussianMap_norm_le s t)
    _ = _ := by
      rw [integral_add h₁ h₂, integral_const_mul, integral_const_mul,
        integral_fun_fst, integral_fun_snd]
      simp [independentAbsGaussianMean]

/-- A fixed leading sample still has an integrable maximum under the rare Gaussian sample. -/
theorem lowerGridGaussianMap_slice_integrable_norm {r m : ℕ} (s t : ℝ) (g : Vector r) :
    Integrable (fun h : Vector m => ‖lowerGridGaussianMap s t (g, h)‖) (standardGaussian m) := by
  have henv := (integrable_const (|s| * ‖g‖) : Integrable _ (standardGaussian m)).add
    ((standardGaussian_integrable_norm m).const_mul |t|)
  apply henv.mono'
    (measurable_norm.comp ((lowerGridGaussianMap_measurable r m s t).comp
      (measurable_const.prodMk measurable_id))).aestronglyMeasurable
  apply ae_of_all
  intro h
  change ‖‖lowerGridGaussianMap s t (g, h)‖‖ ≤ |s| * ‖g‖ + |t| * ‖h‖
  rw [norm_norm]
  exact lowerGridGaussianMap_norm_le s t (g, h)

/-- The lower half of the printed family-width calibration follows by
averaging over the independent centered rare Gaussian coordinates. -/
theorem lowerGridGaussianMean_lower {r m : ℕ} (hr : 1 ≤ r) (hm : 1 ≤ m) (s t : ℝ) :
    |s| * independentAbsGaussianMean r ≤ lowerGridGaussianMean r m s t := by
  classical
  let u : Fin m := ⟨0, by omega⟩
  have hfixed (g : Vector r) : |s| * ‖g‖ ≤
      ∫ h : Vector m, ‖lowerGridGaussianMap s t (g, h)‖ ∂standardGaussian m := by
    have hnonempty : (Finset.univ : Finset (Fin r)).Nonempty :=
      ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
    obtain ⟨j, _, hj⟩ := Finset.exists_max_image Finset.univ (fun j => |g j|) hnonempty
    have hnorm : ‖g‖ = |g j| := by
      apply le_antisymm
      · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
        intro k
        simpa only [Real.norm_eq_abs] using hj k (Finset.mem_univ k)
      · simpa only [Real.norm_eq_abs] using norm_le_pi_norm g j
    let f : Vector m → ℝ := fun h => s * g j + t * h u
    have hf : Integrable f (standardGaussian m) :=
      (integrable_const _).add ((standardGaussian_integrable_coordinate m u).const_mul t)
    have hmean : (∫ h, f h ∂standardGaussian m) = s * g j := by
      rw [show f = (fun h => s * g j + t * h u) from rfl,
        integral_add (integrable_const _) ((standardGaussian_integrable_coordinate m u).const_mul t),
        integral_const, integral_const_mul, standardGaussian_integral_coordinate,
        measureReal_univ_eq_one, one_smul, mul_zero, add_zero]
    calc
      _ = |s * g j| := by rw [hnorm, abs_mul]
      _ ≤ ∫ h, |f h| ∂standardGaussian m := by
        rw [← hmean]
        exact abs_integral_le_integral_abs
      _ ≤ _ := by
        apply integral_mono hf.abs (lowerGridGaussianMap_slice_integrable_norm s t g)
        intro h
        have hb := norm_le_pi_norm (lowerGridGaussianMap s t (g, h)) (finProdFinEquiv (j, u))
        simpa only [Real.norm_eq_abs, lowerGridGaussianMap, Equiv.symm_apply_apply] using hb
  rw [lowerGridGaussianMean_eq_integral,
    integral_prod _ (lowerGridGaussianMap_integrable_norm r m s t)]
  have h := integral_mono ((standardGaussian_integrable_norm r).const_mul |s|)
    (lowerGridGaussianMap_integrable_norm r m s t).integral_prod_left hfixed
  simpa only [integral_const_mul, independentAbsGaussianMean] using h

/-- A concrete rectangular covariance factor for the two independent Gaussian blocks. -/
def lowerGridGaussianFactor (r m : ℕ) (s t : ℝ) :
    Matrix (Fin (r * m)) (Fin r ⊕ Fin m) ℝ :=
  fun k => Sum.elim (fun j => if (finProdFinEquiv.symm k).1 = j then s else 0)
    (fun u => if (finProdFinEquiv.symm k).2 = u then t else 0)

theorem lowerGridGaussianFactor_mulVec {r m : ℕ} (s t : ℝ)
    (z : (Fin r ⊕ Fin m) → ℝ) (k : Fin (r * m)) :
    (lowerGridGaussianFactor r m s t).mulVec z k =
      s * z (Sum.inl (finProdFinEquiv.symm k).1) +
        t * z (Sum.inr (finProdFinEquiv.symm k).2) := by
  classical
  simp [lowerGridGaussianFactor, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, eq_comm]

/-- The exact covariance entries, with separate counts `r` and `m`. -/
theorem lowerGridGaussianFactor_gram (r m : ℕ) (s t : ℝ) :
    lowerGridGaussianFactor r m s t * (lowerGridGaussianFactor r m s t).transpose =
      fun k l => s ^ 2 * (if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1 then 1 else 0) +
        t ^ 2 * (if (finProdFinEquiv.symm k).2 = (finProdFinEquiv.symm l).2 then 1 else 0) := by
  classical
  ext k l
  simp only [Matrix.mul_apply, Matrix.transpose_apply, lowerGridGaussianFactor,
    Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr]
  by_cases hj : (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1 <;>
    by_cases hu : (finProdFinEquiv.symm k).2 = (finProdFinEquiv.symm l).2 <;>
    simp [hj, hu, eq_comm, mul_ite, ite_mul, pow_two]

/-- The Gaussian law was constructed from actual independent samples;
the rectangular-factor identification is proved by its pushforward map. -/
theorem lowerGridGaussianLaw_eq_rectangular (r m : ℕ) (s t : ℝ) :
    lowerGridGaussianLaw r m s t =
      Companion.SplitV4.rectangularGaussianLaw (lowerGridGaussianFactor r m s t) := by
  have hp := measurePreserving_sumPiEquivProdPi_symm
    (fun _ : Fin r ⊕ Fin m => gaussianReal 0 1)
  unfold lowerGridGaussianLaw Companion.SplitV4.rectangularGaussianLaw Companion.SplitV4.finiteStandardGaussian
  rw [← hp.map_eq, Measure.map_map (Companion.SplitV4.measurable_rectangularMulVec _) hp.measurable]
  apply Measure.map_congr
  exact ae_of_all _ (fun z => by
    funext k
    rw [Function.comp_apply, lowerGridGaussianFactor_mulVec]
    rfl)

/-- Every square factor of the computed covariance gives this same actual law. -/
theorem lowerGridGaussianLaw_eq_gaussianLaw {r m : ℕ} (s t : ℝ)
    (A : Matrix (Fin (r * m)) (Fin (r * m)) ℝ)
    (hA : A * A.transpose = lowerGridGaussianFactor r m s t * (lowerGridGaussianFactor r m s t).transpose) :
    lowerGridGaussianLaw r m s t = gaussianLaw A := by
  rw [lowerGridGaussianLaw_eq_rectangular]
  exact Companion.SplitV4.rectangularGaussianLaw_eq_gaussianLaw _ A hA.symm

/-- There is an actual square covariance factor; no rank condition is an input. -/
theorem lowerGridGaussianFactor_exists (r m : ℕ) (s t : ℝ) :
    ∃ A : Matrix (Fin (r * m)) (Fin (r * m)) ℝ,
      A * A.transpose = lowerGridGaussianFactor r m s t * (lowerGridGaussianFactor r m s t).transpose := by
  have hPSD : (lowerGridGaussianFactor r m s t * (lowerGridGaussianFactor r m s t).transpose).PosSemidef := by
    simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using
      Matrix.posSemidef_self_mul_conjTranspose (lowerGridGaussianFactor r m s t)
  refine ⟨hPSD.sqrt, ?_⟩
  have hs : hPSD.sqrt.transpose = hPSD.sqrt := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hPSD.posSemidef_sqrt.isHermitian
  rw [hs]
  exact hPSD.sqrt_mul_self

/-- The displayed covariance matrix is the covariance of the constructed law. -/
theorem covariance_lowerGridGaussianLaw (r m : ℕ) (s t : ℝ) :
    covariance (lowerGridGaussianLaw r m s t) id =
      fun k l => s ^ 2 * (if (finProdFinEquiv.symm k).1 = (finProdFinEquiv.symm l).1 then 1 else 0) +
        t ^ 2 * (if (finProdFinEquiv.symm k).2 = (finProdFinEquiv.symm l).2 then 1 else 0) := by
  obtain ⟨A, hA⟩ := lowerGridGaussianFactor_exists r m s t
  rw [lowerGridGaussianLaw_eq_gaussianLaw s t A hA, covariance_gaussianLaw, hA,
    lowerGridGaussianFactor_gram]

theorem gaussianMaximumMean_lowerGrid {r m : ℕ} (s t : ℝ)
    (A : Matrix (Fin (r * m)) (Fin (r * m)) ℝ)
    (hA : A * A.transpose = lowerGridGaussianFactor r m s t * (lowerGridGaussianFactor r m s t).transpose) :
    gaussianMaximumMean A = lowerGridGaussianMean r m s t := by
  simp only [gaussianMaximumMean, lowerGridGaussianMean, lowerGridGaussianLaw_eq_gaussianLaw s t A hA]

/-- The archive's actual symmetric-family factor is the equal-count specialization. -/
theorem lowerGridGaussianFactor_archived (P : Companion.SplitV4.SymmetricFamilyParameters) (m : ℕ) :
    lowerGridGaussianFactor m m P.scale (Real.sqrt P.variance) =
      Companion.SplitV4.familyGaussianFactor P m := rfl

/-- The actual archived lower-bound Gaussian counterpart obeys the same
width calibration; this statement assumes only its computed covariance factor. -/
theorem archived_family_gaussianMaximumMean_bounds
    (P : Companion.SplitV4.SymmetricFamilyParameters) {m : ℕ} (hm : 1 ≤ m)
    (A : Matrix (Fin (m * m)) (Fin (m * m)) ℝ)
    (hA : A * A.transpose = Companion.SplitV4.familyCovariance m P.variance) :
    P.scale * independentAbsGaussianMean m ≤ gaussianMaximumMean A ∧
      gaussianMaximumMean A ≤ (P.scale + Real.sqrt P.variance) * independentAbsGaussianMean m := by
  have hf : A * A.transpose = lowerGridGaussianFactor m m P.scale (Real.sqrt P.variance) *
      (lowerGridGaussianFactor m m P.scale (Real.sqrt P.variance)).transpose := by
    rw [lowerGridGaussianFactor_archived, Companion.SplitV4.familyGaussianFactor_gram]
    exact hA
  rw [gaussianMaximumMean_lowerGrid _ _ A hf]
  constructor
  · simpa only [abs_of_pos P.scale_pos] using lowerGridGaussianMean_lower hm hm P.scale (Real.sqrt P.variance)
  · simpa only [abs_of_pos P.scale_pos, abs_of_nonneg (Real.sqrt_nonneg _), add_mul] using
      lowerGridGaussianMean_upper m m P.scale (Real.sqrt P.variance)

/-- The printed width profile follows from the two concrete Gaussian
blocks once the rare block's expected maximum tends to zero. The leading
count may vary or remain equal to one. -/
theorem lowerGridGaussianMean_width_profile (r m : ℕ → ℕ) (v : ℕ → ℝ)
    (hr : ∀ n, 1 ≤ r n) (hm : ∀ n, 1 ≤ m n)
    (hv : Filter.Tendsto v Filter.atTop (nhds 0))
    (hrare : Filter.Tendsto (fun n => Real.sqrt (v n) * independentAbsGaussianMean (m n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => lowerGridGaussianMean (r n) (m n)
      (Real.sqrt (1 - v n)) (Real.sqrt (v n)) / independentAbsGaussianMean (r n))
      Filter.atTop (nhds 1) := by
  let d := Real.sqrt (2 / Real.pi)
  have hd : 0 < d := by dsimp [d]; positivity
  have hgr (n : ℕ) : d ≤ independentAbsGaussianMean (r n) := independentAbsGaussianMean_lower (hr n)
  have hgrpos (n : ℕ) : 0 < independentAbsGaussianMean (r n) := hd.trans_le (hgr n)
  have hs : Filter.Tendsto (fun n => Real.sqrt (1 - v n)) Filter.atTop (nhds 1) := by
    simpa only [sub_zero, Real.sqrt_one] using
      (Real.continuous_sqrt.tendsto (1 - (0 : ℝ))).comp (tendsto_const_nhds.sub hv)
  have he : Filter.Tendsto
      (fun n => (Real.sqrt (v n) * independentAbsGaussianMean (m n)) / d)
      Filter.atTop (nhds 0) := by simpa using hrare.div_const d
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le hs
    (by simpa only [add_zero] using hs.add he)
  · intro n
    apply (le_div_iff₀ (hgrpos n)).mpr
    simpa only [abs_of_nonneg (Real.sqrt_nonneg _)] using
      lowerGridGaussianMean_lower (hr n) (hm n) (Real.sqrt (1 - v n)) (Real.sqrt (v n))
  · intro n
    have hu := lowerGridGaussianMean_upper (r n) (m n)
      (Real.sqrt (1 - v n)) (Real.sqrt (v n))
    simp only [abs_of_nonneg (Real.sqrt_nonneg _)] at hu
    calc
      _ ≤ (Real.sqrt (1 - v n) * independentAbsGaussianMean (r n) +
          Real.sqrt (v n) * independentAbsGaussianMean (m n)) / independentAbsGaussianMean (r n) :=
        div_le_div_of_nonneg_right hu (hgrpos n).le
      _ = Real.sqrt (1 - v n) +
          (Real.sqrt (v n) * independentAbsGaussianMean (m n)) / independentAbsGaussianMean (r n) := by
        rw [add_div, mul_div_cancel_right₀ _ (hgrpos n).ne']
      _ ≤ _ := add_le_add_left (div_le_div_of_nonneg_left
        (mul_nonneg (Real.sqrt_nonneg _) (independentAbsGaussianMean_nonneg _)) hd (hgr n)) _

/-- In particular, a single leading coordinate gives the exact bounded-width
limit claimed after Theorem 4, independently of the growth of the rare count. -/
theorem lowerGridGaussianMean_one_tendsto (m : ℕ → ℕ) (v : ℕ → ℝ)
    (hm : ∀ n, 1 ≤ m n) (hv : Filter.Tendsto v Filter.atTop (nhds 0))
    (hrare : Filter.Tendsto (fun n => Real.sqrt (v n) * independentAbsGaussianMean (m n))
      Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun n => lowerGridGaussianMean 1 (m n)
      (Real.sqrt (1 - v n)) (Real.sqrt (v n))) Filter.atTop (nhds (Real.sqrt (2 / Real.pi))) := by
  have h := lowerGridGaussianMean_width_profile (fun _ => 1) m v (fun _ => by norm_num) hm hv hrare
  have hp : Real.sqrt (2 / Real.pi) ≠ 0 := ne_of_gt (by positivity)
  have hh := h.mul_const (Real.sqrt (2 / Real.pi))
  simpa only [independentAbsGaussianMean_one, div_mul_cancel₀ _ hp, one_mul] using hh

end RectangleCLTArxivV1
