import RectangleCLT.GaussianComponentSplitting
import RectangleCLT.GaussianMoments
import RectangleCLT.TruncationBasic
import RectangleCLT.TruncationCovarianceIdentity

/-!
# Symmetric truncation of the exact Gaussian increments

The cutoff is imposed on the whole vector.  It preserves symmetry, hence
the coordinate means and every third mixed moment vanish exactly.  Only
finite fourth moments are needed for the error estimates.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

theorem truncateVector_neg {p : ℕ} (u : ℝ) (x : Vector p) :
    truncateVector u (-x) = -truncateVector u x := by
  by_cases hx : ‖x‖ ≤ u <;> simp [truncateVector, hx]

theorem gaussianComponent_truncated_integral_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) (j : Fin p) :
    (∫ x, truncateVector u x j ∂gaussianLaw B) = 0 := by
  apply gaussianComponent_integral_odd B
    ((measurable_pi_apply j).comp (measurable_truncateVector u))
  intro x
  simp only [truncateVector_neg, Pi.neg_apply]

theorem gaussianComponent_truncated_third_integral_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) (j k l : Fin p) :
    (∫ x, truncateVector u x j * truncateVector u x k *
      truncateVector u x l ∂gaussianLaw B) = 0 := by
  apply gaussianComponent_integral_odd B
    ((((measurable_pi_apply j).comp (measurable_truncateVector u)).mul
      ((measurable_pi_apply k).comp (measurable_truncateVector u))).mul
      ((measurable_pi_apply l).comp (measurable_truncateVector u)))
  intro x
  simp only [truncateVector_neg, Pi.neg_apply]
  ring

theorem gaussianComponent_truncationMean_eq_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) :
    truncationMean (gaussianLaw B) id u = 0 := by
  ext j
  exact gaussianComponent_truncated_integral_zero B u j

theorem gaussianComponent_centeredTruncate_eq {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) :
    centeredTruncateVector (gaussianLaw B) id u = truncateVector u := by
  funext x
  simp only [centeredTruncateVector, id_eq,
    gaussianComponent_truncationMean_eq_zero, sub_zero]

theorem gaussianComponent_integrable_coordinate_fourth {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (j : Fin p) :
    Integrable (fun x : Vector p => x j ^ 4) (gaussianLaw B) := by
  have hLp : MemLp (fun x : Vector p => B.mulVec x j)
      (4 : ℝ≥0∞) (standardGaussian p) := by
    simpa using standardGaussian_memLp_mulVec_coordinate B j 4
  have hi := hLp.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
  have hi' : Integrable (fun x : Vector p => B.mulVec x j ^ 4)
      (standardGaussian p) := by
    simpa only [Real.norm_eq_abs,
      (show Even 4 from by decide).pow_abs] using hi
  unfold gaussianLaw
  exact (integrable_map_measure
    ((measurable_pi_apply j).pow_const 4).aestronglyMeasurable
    (measurable_mulVec B).aemeasurable).mpr hi'

theorem vector_norm_fourth_le_sum {p : ℕ} (hp : 1 ≤ p) (x : Vector p) :
    ‖x‖ ^ 4 ≤ ∑ j, x j ^ 4 := by
  classical
  have hn : (Finset.univ : Finset (Fin p)).Nonempty :=
    ⟨⟨0, by omega⟩, Finset.mem_univ _⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ (fun j => |x j|) hn
  have heq : ‖x‖ = |x j| := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun i =>
        by simpa only [Real.norm_eq_abs] using hmax i (Finset.mem_univ i)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  rw [heq, ← abs_pow, abs_of_nonneg (by positivity : 0 ≤ x j ^ 4)]
  exact Finset.single_le_sum (fun i _ => by positivity) hj

theorem gaussianComponent_integrable_norm_fourth {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fun x : Vector p => ‖x‖ ^ 4) (gaussianLaw B) := by
  have hi := integrable_finset_sum Finset.univ
    (fun j _ => gaussianComponent_integrable_coordinate_fourth B j)
  apply hi.mono' (measurable_norm.pow_const 4).aestronglyMeasurable
  exact ae_of_all _ fun x => by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖x‖ ^ 4)]
      using vector_norm_fourth_le_sum hp x

/-- A fourth-moment cutoff estimate for the actual Gaussian vector, with
no rank or minimum-eigenvalue condition. -/
theorem gaussianComponent_norm_tail_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) {u : ℝ} (hu : 0 < u) :
    (gaussianLaw B).real {x | u < ‖x‖} ≤
      (∫ x : Vector p, ‖x‖ ^ 4 ∂gaussianLaw B) / u ^ 4 := by
  let A : Set (Vector p) := {x | u < ‖x‖}
  have hA : MeasurableSet A := measurableSet_lt measurable_const measurable_norm
  have hiA : Integrable (A.indicator (fun _ => (1 : ℝ))) (gaussianLaw B) :=
    (integrable_const 1).indicator hA
  have hi := (gaussianComponent_integrable_norm_fourth hp B).div_const (u ^ 4)
  calc
    _ = ∫ x, A.indicator (fun _ => (1 : ℝ)) x ∂gaussianLaw B := by
      rw [integral_indicator_const (1 : ℝ) hA, smul_eq_mul, mul_one]
    _ ≤ ∫ x : Vector p, ‖x‖ ^ 4 / u ^ 4 ∂gaussianLaw B := by
      apply integral_mono hiA hi
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.indicator_of_mem hx, Pi.one_apply]
        apply (le_div_iff₀ (pow_pos hu 4)).mpr
        simpa only [one_mul] using pow_le_pow_left₀ hu.le hx.le 4
      · simp only [Set.indicator_of_not_mem hx]
        positivity
    _ = _ := integral_div _ _

/-- Truncation has no centering loss for Gaussian increments. -/
theorem gaussianComponent_truncated_fourth_le {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (u : ℝ) (j : Fin p) :
    (∫ x, truncateVector u x j ^ 4 ∂gaussianLaw B) ≤
      ∫ x : Vector p, x j ^ 4 ∂gaussianLaw B := by
  rw [truncateVector_coordinate_eq_indicator id u j]
  exact indicator_fourth_integral_le
    (measurableSet_le measurable_norm measurable_const)
    (gaussianComponent_integrable_coordinate_fourth B j)

/-- Every entry of the discarded covariance tends to zero.  The estimate
uses the same fourth moment for all coordinate pairs. -/
theorem gaussianComponent_covariance_deficit_le {p : ℕ} (hp : 1 ≤ p)
    (B : Matrix (Fin p) (Fin p) ℝ) {u : ℝ} (hu : 0 < u) (j k : Fin p) :
    |(B * B.transpose) j k -
      covariance (gaussianLaw B) (truncateVector u) j k| ≤
        (∫ x : Vector p, ‖x‖ ^ 4 ∂gaussianLaw B) / u ^ 2 := by
  let A : Set (Vector p) := {x | ‖x‖ ≤ u}
  have hA : MeasurableSet A := measurableSet_le measurable_norm measurable_const
  have hid := truncation_covariance_deficit (μ := gaussianLaw B) measurable_id
    (gaussianLaw_integrable_coordinate_product B)
    (gaussianLaw_integral_coordinate B) u j k
  rw [covariance_gaussianLaw, gaussianComponent_truncationMean_eq_zero] at hid
  simp only [Pi.zero_apply, zero_mul, add_zero] at hid
  change |(B * B.transpose) j k -
    covariance (gaussianLaw B) (fun x => truncateVector u x) j k| ≤ _
  rw [hid]
  have hi : Integrable (Aᶜ.indicator (fun x => x j * x k)) (gaussianLaw B) :=
    (gaussianLaw_integrable_coordinate_product B j k).indicator hA.compl
  have hdom := (gaussianComponent_integrable_norm_fourth hp B).div_const (u ^ 2)
  calc
    _ ≤ ∫ x, |Aᶜ.indicator (fun x => x j * x k) x| ∂gaussianLaw B :=
      abs_integral_le_integral_abs
    _ ≤ ∫ x : Vector p, ‖x‖ ^ 4 / u ^ 2 ∂gaussianLaw B := by
      apply integral_mono hi.abs hdom
      intro x
      by_cases hx : x ∈ A
      · simp only [Set.mem_compl_iff, hx, not_true_eq_false,
          Set.indicator_of_not_mem, abs_zero]
        positivity
      · have hux : u ≤ ‖x‖ := (lt_of_not_ge hx).le
        have hj : |x j| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
        have hk : |x k| ≤ ‖x‖ := by simpa only [Real.norm_eq_abs] using norm_le_pi_norm x k
        have hprod : |x j * x k| ≤ ‖x‖ ^ 2 := by
          rw [abs_mul, pow_two]
          exact mul_le_mul hj hk (abs_nonneg _) (norm_nonneg _)
        have hsquare : u ^ 2 ≤ ‖x‖ ^ 2 := pow_le_pow_left₀ hu.le hux 2
        have hquot : ‖x‖ ^ 2 ≤ ‖x‖ ^ 4 / u ^ 2 := by
          apply (le_div_iff₀ (pow_pos hu 2)).mpr
          nlinarith [mul_le_mul_of_nonneg_left hsquare (sq_nonneg ‖x‖)]
        simpa only [Set.mem_compl_iff, hx, not_false_eq_true,
          Set.indicator_of_mem] using hprod.trans hquot
    _ = _ := integral_div _ _

/-- One small centered increment in the exact finite-splitting experiment. -/
def gaussianComponentIncrement {p : ℕ} (k : ℕ) (x : Vector p) : Vector p :=
  ((k : ℝ) ^ 3)⁻¹ • truncateVector ((k : ℝ) ^ 2) x

theorem measurable_gaussianComponentIncrement {p : ℕ} (k : ℕ) :
    Measurable (gaussianComponentIncrement (p := p) k) :=
  (measurable_truncateVector ((k : ℝ) ^ 2)).const_smul _

theorem norm_gaussianComponentIncrement_le {p : ℕ} {k : ℕ} (hk : k ≠ 0)
    (x : Vector p) : ‖gaussianComponentIncrement k x‖ ≤ (k : ℝ)⁻¹ := by
  have hk' : 0 < (k : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hk
  calc
    _ = ((k : ℝ) ^ 3)⁻¹ * ‖truncateVector ((k : ℝ) ^ 2) x‖ := by
      rw [gaussianComponentIncrement, norm_smul, Real.norm_eq_abs,
        abs_of_nonneg (by positivity : 0 ≤ ((k : ℝ) ^ 3)⁻¹)]
    _ ≤ ((k : ℝ) ^ 3)⁻¹ * (k : ℝ) ^ 2 :=
      mul_le_mul_of_nonneg_left (norm_truncateVector_le (sq_nonneg _) x) (by positivity)
    _ = _ := by field_simp [ne_of_gt hk']; ring

theorem gaussianComponentIncrement_integral_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (j : Fin p) :
    (∫ x, gaussianComponentIncrement k x j ∂gaussianLaw B) = 0 := by
  simp only [gaussianComponentIncrement, Pi.smul_apply, smul_eq_mul,
    integral_const_mul, gaussianComponent_truncated_integral_zero, mul_zero]

theorem gaussianComponentIncrement_third_integral_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (j l r : Fin p) :
    (∫ x, gaussianComponentIncrement k x j * gaussianComponentIncrement k x l *
      gaussianComponentIncrement k x r ∂gaussianLaw B) = 0 := by
  have heq (x : Vector p) :
      gaussianComponentIncrement k x j * gaussianComponentIncrement k x l *
        gaussianComponentIncrement k x r =
      (((k : ℝ) ^ 3)⁻¹) ^ 3 *
        (truncateVector ((k : ℝ) ^ 2) x j * truncateVector ((k : ℝ) ^ 2) x l *
          truncateVector ((k : ℝ) ^ 2) x r) := by
    simp only [gaussianComponentIncrement, Pi.smul_apply, smul_eq_mul]
    ring
  simp_rw [heq]
  rw [integral_const_mul, gaussianComponent_truncated_third_integral_zero, mul_zero]

/-- The finite truncated increment array has the exact bounded independent
hypotheses required by the bounded proxy theorem. -/
theorem gaussianComponentIncrement_boundedIndependent {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    BoundedIndependentHypotheses (gaussianComponentArrayLaw B (k ^ 6))
      (fun i z => gaussianComponentIncrement k (z i)) (k : ℝ)⁻¹ := by
  refine ⟨fun i => (measurable_gaussianComponentIncrement k).comp (measurable_pi_apply i),
    (gaussianComponentArray_iIndepFun B).comp
      (fun _ => gaussianComponentIncrement k)
      (fun _ => measurable_gaussianComponentIncrement k), ?_,
    fun i => ae_of_all _ fun z => norm_gaussianComponentIncrement_le hk (z i),
    inv_nonneg.mpr (Nat.cast_nonneg _)⟩
  intro i j
  have hmap := integral_map (μ := gaussianComponentArrayLaw B (k ^ 6))
    (measurable_pi_apply i).aemeasurable
    (((measurable_pi_apply j).comp
      (measurable_gaussianComponentIncrement k)).aestronglyMeasurable)
  rw [gaussianComponentArrayLaw_map_eval B] at hmap
  exact hmap.symm.trans (gaussianComponentIncrement_integral_zero B k j)

/-- Truncation preserves the signed third-moment cancellation, rather than
bounding the third absolute moments. -/
theorem gaussianComponentIncrement_array_third_zero {p : ℕ}
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) (j l r : Fin p) :
    (∑ i : Fin (k ^ 6), ∫ z,
      gaussianComponentIncrement k (z i) j * gaussianComponentIncrement k (z i) l *
        gaussianComponentIncrement k (z i) r
      ∂gaussianComponentArrayLaw B (k ^ 6)) = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hmeas :=
    ((((measurable_pi_apply j).comp (measurable_gaussianComponentIncrement k)).mul
      ((measurable_pi_apply l).comp (measurable_gaussianComponentIncrement k))).mul
      ((measurable_pi_apply r).comp (measurable_gaussianComponentIncrement k)))
  have hmap := integral_map (μ := gaussianComponentArrayLaw B (k ^ 6))
    (measurable_pi_apply i).aemeasurable hmeas.aestronglyMeasurable
  rw [gaussianComponentArrayLaw_map_eval B] at hmap
  exact hmap.symm.trans (gaussianComponentIncrement_third_integral_zero B k j l r)

end

end RectangleCLT
