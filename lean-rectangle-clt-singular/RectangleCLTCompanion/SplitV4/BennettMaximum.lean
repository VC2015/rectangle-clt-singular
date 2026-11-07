import Mathlib.Analysis.SpecialFunctions.Integrals
import Mathlib.Probability.Moments.Basic
import RectangleCLTCompanion.GaussianEntropy
import RectangleCLT.BoundedMaximum
import RectangleCLTCompanion.SplitV4.BennettTruncation

/-!
The truncated Bennett maximum in Lemma G.4, with the universal constant `2`.
No desired maximum estimate is an assumption.  The Bennett correction is
retained through the independent exponential moments and actual signed
log-sum-exp bound, before choosing the Laplace parameter.  The separate
truncation module provides symmetry, genuine moment integrability, the
omitted-tail estimate and the zero-variance case.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def bennettCorrection (a : ℝ) : ℝ := Real.exp a - 1 - a

def bennettKernel (a : ℝ) : ℝ :=
  ∫ r in (0 : ℝ)..1, (1 - r) * Real.exp (r * a)

theorem bennettCorrection_nonneg (a : ℝ) : 0 ≤ bennettCorrection a := by
  unfold bennettCorrection
  linarith [Real.add_one_le_exp a]

theorem bennettKernel_integrable (a : ℝ) :
    IntervalIntegrable (fun r : ℝ => (1 - r) * Real.exp (r * a)) volume 0 1 := by
  exact (by fun_prop : Continuous (fun r : ℝ => (1 - r) * Real.exp (r * a))).intervalIntegrable _ _

/-- An integral Taylor identity valid without division, including `a = 0`. -/
theorem bennettCorrection_eq_sq_mul_kernel (a : ℝ) :
    bennettCorrection a = a ^ 2 * bennettKernel a := by
  let F : ℝ → ℝ := fun r => (a * (r - 1) - 1) * Real.exp (r * a)
  have hd (r : ℝ) : HasDerivAt F (a ^ 2 * ((r - 1) * Real.exp (r * a))) r := by
    have hleft := (((hasDerivAt_id r).sub_const 1).const_mul a).sub_const 1
    have hright := ((hasDerivAt_id r).mul_const a).exp
    convert hleft.mul hright using 1 <;> dsimp [F] <;> ring
  have hi := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun r _ => hd r)
    ((by fun_prop : Continuous (fun r : ℝ => a ^ 2 * ((r - 1) * Real.exp (r * a)))).intervalIntegrable 0 1)
  rw [intervalIntegral.integral_const_mul] at hi
  have hneg : (∫ r in (0 : ℝ)..1, (r - 1) * Real.exp (r * a)) = -bennettKernel a := by
    unfold bennettKernel
    rw [← intervalIntegral.integral_neg]
    congr 1
    ext r
    dsimp [bennettKernel]
    ring
  rw [hneg] at hi
  dsimp [F] at hi
  simp only [sub_self, mul_zero, zero_sub, one_mul, zero_mul, Real.exp_zero, mul_one] at hi
  unfold bennettCorrection
  linarith

theorem bennettKernel_mono : Monotone bennettKernel := by
  intro a b hab
  apply intervalIntegral.integral_mono_on (by norm_num : (0 : ℝ) ≤ 1)
    (bennettKernel_integrable a) (bennettKernel_integrable b)
  intro r hr
  apply mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hab hr.1))
  linarith [hr.2]

/-- The pointwise Bennett majorant retains the linear term, so centering
can be used after integration.  A lower bound on `x` is not required. -/
theorem exp_le_bennett_quadratic {u t x : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (hx : x ≤ u) :
    Real.exp (t * x) ≤ 1 + t * x +
      (bennettCorrection (t * u) / u ^ 2) * x ^ 2 := by
  have hk := bennettKernel_mono (mul_le_mul_of_nonneg_left hx ht)
  have hm := mul_le_mul_of_nonneg_left hk (sq_nonneg (t * x))
  have hxu := bennettCorrection_eq_sq_mul_kernel (t * x)
  have huu := bennettCorrection_eq_sq_mul_kernel (t * u)
  have heq : (t * x) ^ 2 * bennettKernel (t * u) =
      (bennettCorrection (t * u) / u ^ 2) * x ^ 2 := by
    rw [huu]
    field_simp
    ring
  rw [heq] at hm
  unfold bennettCorrection at hxu
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Genuine exponential integrability follows from the one-sided bound. -/
theorem integrable_exp_mul_of_bounded_above {X : Ω → ℝ} (hX : Measurable X)
    {u t : ℝ} (ht : 0 ≤ t) (hbound : ∀ᵐ ω ∂μ, X ω ≤ u) :
    Integrable (fun ω => Real.exp (t * X ω)) μ := by
  apply (integrable_const (Real.exp (t * u))).mono'
    (hX.const_mul t).exp.aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hω ht)

/-- A centered summand's actual MGF has the full Bennett correction. -/
theorem bounded_centered_bennett_mgf {X : Ω → ℝ} (hX : Measurable X)
    (hXi : Integrable X μ) (hX2 : Integrable (fun ω => X ω ^ 2) μ)
    (hmean : (∫ ω, X ω ∂μ) = 0) {u t : ℝ} (hu : 0 < u) (ht : 0 ≤ t)
    (hbound : ∀ᵐ ω ∂μ, X ω ≤ u) :
    mgf X μ t ≤ Real.exp (((∫ ω, X ω ^ 2 ∂μ) / u ^ 2) *
      bennettCorrection (t * u)) := by
  have he := integrable_exp_mul_of_bounded_above hX ht hbound
  let c := bennettCorrection (t * u) / u ^ 2
  have hp := integral_mono_ae he
    (((integrable_const (1 : ℝ)).add (hXi.const_mul t)).add (hX2.const_mul c))
    (hbound.mono (fun ω hω => exp_le_bennett_quadratic hu ht hω))
  have hcalc : (∫ ω, (1 + t * X ω) + c * X ω ^ 2 ∂μ) =
      1 + c * (∫ ω, X ω ^ 2 ∂μ) := by
    have hadd := integral_add ((integrable_const (1 : ℝ)).add (hXi.const_mul t))
      (hX2.const_mul c)
    have hlinear := integral_add (integrable_const (1 : ℝ) (μ := μ)) (hXi.const_mul t)
    simp only [Pi.add_apply] at hadd hlinear
    rw [hadd, hlinear, integral_const_mul, integral_const_mul, hmean]
    simp
  change (∫ ω, Real.exp (t * X ω) ∂μ) ≤ _
  calc
    _ ≤ 1 + c * (∫ ω, X ω ^ 2 ∂μ) := hp.trans_eq hcalc
    _ ≤ Real.exp (c * (∫ ω, X ω ^ 2 ∂μ)) := by
      linarith [Real.add_one_le_exp (c * (∫ ω, X ω ^ 2 ∂μ))]
    _ = _ := by congr 1; dsimp [c]; ring

/-- Independence is used for the actual product of exponential moments;
only the sum of the coordinate variances enters the resulting bound. -/
theorem independent_sum_bennett_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hXi : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {u t v : ℝ}
    (hu : 0 < u) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ u)
    (hv : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (t * ∑ i, X i ω)) μ ∧
    mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp ((v / u ^ 2) * bennettCorrection (t * u)) := by
  have he (i : Fin n) := integrable_exp_mul_of_bounded_above (hX i) ht (hbound i)
  have heSum := hind.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ => he i)
  refine ⟨by simpa only [Finset.sum_apply] using heSum, ?_⟩
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i ∈ (Finset.univ : Finset (Fin n)), X i := by
    ext ω
    simp
  rw [hfun, hind.mgf_sum hX Finset.univ]
  calc
    _ ≤ ∏ i : Fin n, Real.exp (((∫ ω, X i ω ^ 2 ∂μ) / u ^ 2) *
        bennettCorrection (t * u)) := by
      apply Finset.prod_le_prod (fun _ _ => mgf_nonneg)
      intro i _
      exact bounded_centered_bennett_mgf (hX i) (hXi i) (hX2 i) (hmean i) hu ht (hbound i)
    _ = Real.exp (((∑ i, ∫ ω, X i ω ^ 2 ∂μ) / u ^ 2) *
        bennettCorrection (t * u)) := by
      rw [← Real.exp_sum]
      congr 1
      simp only [Finset.sum_mul, Finset.sum_div]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      exact mul_le_mul_of_nonneg_right
        (div_le_div_of_nonneg_right hv (sq_nonneg _)) (bennettCorrection_nonneg _)

theorem independent_sum_bennett_log_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hXi : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {u t v : ℝ}
    (hu : 0 < u) (ht : 0 ≤ t)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ u)
    (hv : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    Real.log (mgf (fun ω => ∑ i, X i ω) μ t) ≤
      (v / u ^ 2) * bennettCorrection (t * u) := by
  have hm := independent_sum_bennett_mgf X hX hind hXi hX2 hmean hu ht hbound hv
  exact (Real.log_le_iff_le_exp (mgf_pos hm.1)).mpr hm.2

theorem exp_norm_le_signed_coordinate_sum {p : ℕ} (hp : 1 ≤ p)
    (x : Vector p) (t : ℝ) :
    Real.exp (t * ‖x‖) ≤
      ∑ j : Fin p, (Real.exp (t * x j) + Real.exp (t * (-x j))) := by
  haveI : Nonempty (Fin p) := ⟨⟨0, by omega⟩⟩
  obtain ⟨j, hj, hmax⟩ := Finset.exists_max_image Finset.univ
    (fun j : Fin p => |x j|) Finset.univ_nonempty
  have hnorm : ‖x‖ = |x j| := by
    apply le_antisymm
    · apply (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr
      intro k
      simpa only [Real.norm_eq_abs] using hmax k (Finset.mem_univ k)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x j
  rw [hnorm]
  have habs : Real.exp (t * |x j|) ≤ Real.exp (t * x j) + Real.exp (t * (-x j)) := by
    rcases le_total 0 (x j) with hx | hx
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_nonpos hx]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  exact habs.trans (Finset.single_le_sum (fun k _ => add_nonneg
    (Real.exp_nonneg (t * x k)) (Real.exp_nonneg (t * (-x k)))) hj)

/-- Log-sum-exp for the actual expected maximum, with both coordinate signs.
The common MGF bound is an intermediate input that the Bennett summand
theorem supplies; no maximum bound is assumed. -/
theorem expected_norm_le_log_signed_mgf {p : ℕ} (hp : 1 ≤ p)
    (S : Ω → Vector p) (hS : Measurable S)
    (hSi : Integrable (fun ω => ‖S ω‖) μ) {t b : ℝ} (ht : 0 < t)
    (he : ∀ j : Fin p,
      Integrable (fun ω => Real.exp (t * S ω j)) μ ∧
      Integrable (fun ω => Real.exp (t * (-S ω j))) μ)
    (hb : ∀ j : Fin p,
      mgf (fun ω => S ω j) μ t ≤ Real.exp b ∧
      mgf (fun ω => -S ω j) μ t ≤ Real.exp b) :
    (∫ ω, ‖S ω‖ ∂μ) ≤ (Real.log (2 * (p : ℝ)) + b) / t := by
  have hsum : Integrable (fun ω => ∑ j : Fin p,
      (Real.exp (t * S ω j) + Real.exp (t * (-S ω j)))) μ := by
    exact integrable_finset_sum _ (fun j _ => (he j).1.add (he j).2)
  have henorm : Integrable (fun ω => Real.exp (t * ‖S ω‖)) μ := by
    apply hsum.mono' ((hS.norm.const_mul t).exp.aestronglyMeasurable)
    refine ae_of_all _ ?_
    intro ω
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_norm_le_signed_coordinate_sum hp (S ω) t
  have hj := weighted_exp_mean_le μ (fun _ : Ω => (1 : ℝ))
    (fun ω => t * ‖S ω‖) (fun _ => zero_le_one) (integrable_const 1)
    (by simpa only [one_mul] using hSi.const_mul t)
    (by simpa only [one_mul] using henorm) (by simp)
  have hj' : Real.exp (t * ∫ ω, ‖S ω‖ ∂μ) ≤ ∫ ω, Real.exp (t * ‖S ω‖) ∂μ := by
    simpa [integral_const_mul] using hj
  have hpoint := integral_mono_ae henorm hsum
    (ae_of_all _ (fun ω => exp_norm_le_signed_coordinate_sum hp (S ω) t))
  have hupper : (∫ ω, ∑ j : Fin p,
      (Real.exp (t * S ω j) + Real.exp (t * (-S ω j))) ∂μ) ≤
      (2 * (p : ℝ)) * Real.exp b := by
    have hsumint := integral_finset_sum (Finset.univ : Finset (Fin p))
      (fun j _ => (he j).1.add (he j).2)
    simp only [Pi.add_apply] at hsumint
    rw [hsumint]
    calc
      _ ≤ ∑ _j : Fin p, (Real.exp b + Real.exp b) := by
        apply Finset.sum_le_sum
        intro j _
        have hadd := integral_add (he j).1 (he j).2
        simp only [Pi.add_apply] at hadd
        rw [hadd]
        exact add_le_add (hb j).1 (hb j).2
      _ = _ := by simp; ring
  have hpp : 0 < 2 * (p : ℝ) := by positivity
  have hexp : Real.exp (t * ∫ ω, ‖S ω‖ ∂μ) ≤
      Real.exp (Real.log (2 * (p : ℝ)) + b) := by
    rw [Real.exp_add, Real.exp_log hpp]
    exact hj'.trans (hpoint.trans hupper)
  exact (le_div_iff₀ ht).mpr (by
    simpa only [mul_comm] using Real.exp_le_exp.mp hexp)

/-- The bounded vector part of G.4 before choosing the Laplace parameter. -/
theorem bounded_vector_bennett_maximum {p n : ℕ} {T : Fin n → Ω → Vector p}
    {u t v : ℝ} (h : BoundedIndependentHypotheses μ T u) (hp : 1 ≤ p)
    (hu : 0 < u) (ht : 0 < t)
    (hv : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      (Real.log (2 * (p : ℝ)) + (v / u ^ 2) * bennettCorrection (t * u)) / t := by
  have hm (j : Fin p) := fun i : Fin n => (measurable_pi_apply j).comp (h.measurable i)
  have hi (i : Fin n) (j : Fin p) : Integrable (fun ω => T i ω j) μ := by
    apply (integrable_const u).mono' (hm j i).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j
  have hi2 (i : Fin n) (j : Fin p) : Integrable (fun ω => T i ω j ^ 2) μ :=
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 2
  have hplus (j : Fin p) := independent_sum_bennett_mgf
    (fun i ω => T i ω j) (hm j)
    (h.independent.comp (fun _ x => x j) (fun _ => measurable_pi_apply j))
    (fun i => hi i j) (fun i => hi2 i j) (fun i => h.centered i j) hu ht.le
    (fun i => (h.abs_coordinate_le i j).mono (fun _ hx => le_trans (le_abs_self _) hx)) (hv j)
  have hminus (j : Fin p) := independent_sum_bennett_mgf
    (fun i ω => -T i ω j) (fun i => (hm j i).neg)
    (h.independent.comp (fun _ x => -x j) (fun _ => (measurable_pi_apply j).neg))
    (fun i => (hi i j).neg) (fun i => by simpa only [neg_sq] using hi2 i j)
    (fun i => by rw [integral_neg, h.centered i j, neg_zero]) hu ht.le
    (fun i => (h.abs_coordinate_le i j).mono (fun _ hx => le_trans (neg_le_abs _) hx))
    (by simpa only [neg_sq] using hv j)
  apply expected_norm_le_log_signed_mgf hp (sumVector T) h.measurable_sum
    h.integrable_norm_sum ht
  · intro j
    constructor
    · simpa only [sumVector, Finset.sum_apply] using (hplus j).1
    · simpa only [sumVector, Finset.sum_apply, Finset.sum_neg_distrib] using (hminus j).1
  · intro j
    constructor
    · simpa only [sumVector, Finset.sum_apply] using (hplus j).2
    · simpa only [sumVector, Finset.sum_apply, Finset.sum_neg_distrib] using (hminus j).2

/-- The optimized bounded part has the exact logarithmic Bennett gain. -/
theorem bounded_vector_bennett_maximum_optimized {p n : ℕ}
    {T : Fin n → Ω → Vector p} {u v : ℝ}
    (h : BoundedIndependentHypotheses μ T u) (hp : 1 ≤ p)
    (hu : 0 < u) (hv : 0 < v)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      2 * u * dimensionLog p / Real.log (1 + u ^ 2 * dimensionLog p / v) := by
  let L := dimensionLog p
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let k := u ^ 2 * L / v
  have hk : 0 < k := div_pos (mul_pos (sq_pos_of_pos hu) hL) hv
  let a := Real.log (1 + k)
  have ha : 0 < a := Real.log_pos (by linarith)
  let t := a / u
  have ht : 0 < t := div_pos ha hu
  have htu : t * u = a := by dsimp [t]; field_simp
  have hcorr : bennettCorrection (t * u) ≤ k := by
    rw [htu]
    unfold bennettCorrection a
    rw [Real.exp_log (by linarith : 0 < 1 + k)]
    linarith
  have hvcorr : (v / u ^ 2) * bennettCorrection (t * u) ≤ L := by
    have hm := mul_le_mul_of_nonneg_left hcorr (div_nonneg hv.le (sq_nonneg u))
    have heq : (v / u ^ 2) * k = L := by dsimp [k]; field_simp; ring
    exact hm.trans_eq heq
  have hlog : Real.log (2 * (p : ℝ)) ≤ L := by
    apply Real.log_le_log
    · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
      positivity
    · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)
  have hb := bounded_vector_bennett_maximum h hp hu ht hvariance
  calc
    _ ≤ (Real.log (2 * (p : ℝ)) + (v / u ^ 2) * bennettCorrection (t * u)) / t := hb
    _ ≤ (2 * L) / t := div_le_div_of_nonneg_right (by linarith) ht.le
    _ = _ := by dsimp [t, a, k, L]; field_simp; ring

/-- Lemma G.4 for the actual finite independent array, including genuine
second and envelope-moment integrability.  Central symmetry is used only
to center the bounded norm truncations. The universal constant is `2`.
No coordinate independence or covariance nondegeneracy is assumed. -/
theorem truncated_bennett_maximum {p n : ℕ} (T : Fin n → Ω → Vector p)
    (hp : 1 ≤ p) (hT : ∀ i, Measurable (T i)) (hind : iIndepFun T μ)
    (hsym : ∀ i, IdentDistrib (T i) (fun ω => -T i ω) μ μ)
    {q u v A : ℝ} (hq : 1 < q) (hu : 0 < u) (hv : 0 < v)
    (hsecond : ∀ i j, Integrable (fun ω => T i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v)
    (hmoment : ∀ i, Integrable (fun ω => ‖T i ω‖ ^ q) μ)
    (hbudget : (∑ i, ∫ ω, ‖T i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      2 * u * dimensionLog p / Real.log (1 + u ^ 2 * dimensionLog p / v) +
        A ^ q / u ^ (q - 1) := by
  let Y : Fin n → Ω → Vector p := fun i ω => bennettTruncate u (T i ω)
  let R : Fin n → Ω → Vector p := fun i ω => T i ω - Y i ω
  have hY : BoundedIndependentHypotheses μ Y u :=
    { measurable := fun i => measurable_bennettTruncate_random (hT i)
      independent := iIndepFun_bennettTruncate hind
      centered := fun i j => integral_bennettTruncate_coordinate_eq_zero (hT i) hu.le (hsym i) j
      bounded := fun i => ae_of_all _ (fun ω => norm_bennettTruncate_le hu.le (T i ω))
      delta_nonneg := hu.le }
  have hYvar (j : Fin p) : (∑ i, ∫ ω, Y i ω j ^ 2 ∂μ) ≤ v := by
    apply (Finset.sum_le_sum (fun i _ =>
      integral_bennettTruncate_coordinate_sq_le (u := u) (hT i) j (hsecond i j))).trans
    exact hvariance j
  have hYi : Integrable (sumVector Y) μ :=
    integrable_finset_sum _ (fun i _ => integrable_bennettTruncate (hT i) hu.le)
  have hRi (i : Fin n) : Integrable (R i) μ :=
    integrable_bennettRemainder (hT i) hu hq (hmoment i)
  have hRsum : Integrable (sumVector R) μ := integrable_finset_sum _ (fun i _ => hRi i)
  have hdecomp : sumVector T = fun ω => sumVector Y ω + sumVector R ω := by
    ext ω j
    simp [sumVector, R, Finset.sum_sub_distrib]
  have hTi : Integrable (sumVector T) μ := by
    rw [hdecomp]
    exact hYi.add hRsum
  have htriangle : (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      (∫ ω, ‖sumVector Y ω‖ ∂μ) + (∫ ω, ‖sumVector R ω‖ ∂μ) := by
    have hh := integral_mono hTi.norm (hYi.norm.add hRsum.norm)
      (fun ω => by rw [hdecomp]; exact norm_add_le _ _)
    have hadd := integral_add hYi.norm hRsum.norm
    simp only [Pi.add_apply] at hadd
    exact hh.trans_eq hadd
  have htail := integral_norm_sum_bennettRemainder_le_budget hT hu hq hmoment A hbudget
  exact htriangle.trans (add_le_add
    (bounded_vector_bennett_maximum_optimized hY hp hu hv hYvar) htail)

/-- The `v = 0` endpoint of G.4 is an a.e. assertion about the actual sum. -/
theorem truncated_bennett_maximum_zero_variance {p n : ℕ}
    (T : Fin n → Ω → Vector p)
    (hsecond : ∀ i j, Integrable (fun ω => T i ω j ^ 2) μ)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ 0) :
    sumVector T =ᵐ[μ] 0 := by
  exact sum_ae_eq_zero_of_coordinate_second_moment_budget_zero hsecond hvariance

end
end RectangleCLT.Companion.SplitV4
