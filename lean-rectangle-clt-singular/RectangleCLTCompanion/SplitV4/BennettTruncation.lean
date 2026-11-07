import RectangleCLTCompanion.Statement
import Mathlib.Probability.IdentDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
Actual vector truncation inputs for split-V4 Lemma G.4. The cutoff uses the
maximum norm on `Vector p`; its law stays centrally symmetric. All expectations
used in the tail estimates have genuine Bochner integrability. These lemmas
do not assume a Bennett bound or an expected-maximum estimate.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

set_option autoImplicit false

/-- The truncation in Lemma G.4, including the entire vector at the cutoff. -/
def bennettTruncate {p : ℕ} (u : ℝ) (x : Vector p) : Vector p :=
  if ‖x‖ ≤ u then x else 0

theorem measurable_bennettTruncate {p : ℕ} (u : ℝ) :
    Measurable (bennettTruncate (p := p) u) := by
  exact Measurable.piecewise
    (s := {x : Vector p | ‖x‖ ≤ u})
    (measurableSet_le measurable_norm measurable_const) measurable_id measurable_const

theorem bennettTruncate_neg {p : ℕ} (u : ℝ) (x : Vector p) :
    bennettTruncate u (-x) = -bennettTruncate u x := by
  simp only [bennettTruncate, norm_neg]
  split_ifs <;> simp

theorem norm_bennettTruncate_le {p : ℕ} {u : ℝ} (hu : 0 ≤ u) (x : Vector p) :
    ‖bennettTruncate u x‖ ≤ u := by
  unfold bennettTruncate
  split_ifs with h
  · exact h
  · simpa using hu

theorem abs_bennettTruncate_coordinate_le {p : ℕ} {u : ℝ}
    (hu : 0 ≤ u) (x : Vector p) (j : Fin p) :
    |bennettTruncate u x j| ≤ u := by
  calc
    _ ≤ ‖bennettTruncate u x‖ := by
      simpa only [Real.norm_eq_abs] using norm_le_pi_norm (bennettTruncate u x) j
    _ ≤ u := norm_bennettTruncate_le hu x

theorem bennettTruncate_coordinate_sq_le {p : ℕ} (u : ℝ) (x : Vector p) (j : Fin p) :
    bennettTruncate u x j ^ 2 ≤ x j ^ 2 := by
  unfold bennettTruncate
  split_ifs <;> simp [sq_nonneg]

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}
  {p n : ℕ} {T : Ω → Vector p} {u q : ℝ}

theorem measurable_bennettTruncate_random (hT : Measurable T) :
    Measurable (fun ω => bennettTruncate u (T ω)) :=
  (measurable_bennettTruncate u).comp hT

theorem measurable_bennettTruncate_coordinate (hT : Measurable T) (j : Fin p) :
    Measurable (fun ω => bennettTruncate u (T ω) j) :=
  (measurable_pi_apply j).comp (measurable_bennettTruncate_random hT)

theorem integrable_bennettTruncate [IsFiniteMeasure μ]
    (hT : Measurable T) (hu : 0 ≤ u) :
    Integrable (fun ω => bennettTruncate u (T ω)) μ :=
  (integrable_const u).mono' (measurable_bennettTruncate_random hT).aestronglyMeasurable
    (Filter.Eventually.of_forall (fun ω => norm_bennettTruncate_le hu (T ω)))

theorem integrable_bennettTruncate_coordinate [IsFiniteMeasure μ]
    (hT : Measurable T) (hu : 0 ≤ u) (j : Fin p) :
    Integrable (fun ω => bennettTruncate u (T ω) j) μ := by
  apply (integrable_const u).mono'
    (measurable_bennettTruncate_coordinate hT j).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    simpa only [Real.norm_eq_abs] using abs_bennettTruncate_coordinate_le hu (T ω) j)

/-- Central symmetry of the actual distribution gives central symmetry of
the truncated distribution; no symmetry of individual coordinates is assumed. -/
theorem identDistrib_bennettTruncate_neg
    (hsym : IdentDistrib T (fun ω => -T ω) μ μ) :
    IdentDistrib (fun ω => bennettTruncate u (T ω))
      (fun ω => -bennettTruncate u (T ω)) μ μ := by
  have hh := hsym.comp (measurable_bennettTruncate u)
  change IdentDistrib (fun ω => bennettTruncate u (T ω))
    (fun ω => bennettTruncate u (-T ω)) μ μ at hh
  simpa only [bennettTruncate_neg] using hh

/-- The bounded centrally symmetric truncation is genuinely integrable and
centered, as required by the scalar Bennett input. -/
theorem integral_bennettTruncate_coordinate_eq_zero [IsFiniteMeasure μ]
    (hT : Measurable T) (hu : 0 ≤ u)
    (hsym : IdentDistrib T (fun ω => -T ω) μ μ) (j : Fin p) :
    (∫ ω, bennettTruncate u (T ω) j ∂μ) = 0 := by
  have hi : Integrable (fun ω => bennettTruncate u (T ω) j) μ :=
    integrable_bennettTruncate_coordinate hT hu j
  have hs := (identDistrib_bennettTruncate_neg (u := u) hsym).comp (measurable_pi_apply j)
  have he : (∫ ω, bennettTruncate u (T ω) j ∂μ) =
      ∫ ω, -bennettTruncate u (T ω) j ∂μ := by
    simpa only [Function.comp_apply, Pi.neg_apply] using hs.integral_eq
  rw [integral_neg] at he
  linarith

/-- A common measurable vector cutoff preserves independence over summands. -/
theorem iIndepFun_bennettTruncate {Ts : Fin n → Ω → Vector p}
    (hind : iIndepFun Ts μ) :
    iIndepFun (fun i ω => bennettTruncate u (Ts i ω)) μ :=
  hind.comp (fun _ => bennettTruncate u) (fun _ => measurable_bennettTruncate u)

theorem integrable_bennettTruncate_coordinate_sq
    (hT : Measurable T) (j : Fin p)
    (hsecond : Integrable (fun ω => T ω j ^ 2) μ) :
    Integrable (fun ω => bennettTruncate u (T ω) j ^ 2) μ := by
  apply hsecond.mono' ((measurable_bennettTruncate_coordinate hT j).pow_const 2).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact bennettTruncate_coordinate_sq_le u (T ω) j)

/-- Truncation cannot increase the actual coordinate second moment. -/
theorem integral_bennettTruncate_coordinate_sq_le
    (hT : Measurable T) (j : Fin p)
    (hsecond : Integrable (fun ω => T ω j ^ 2) μ) :
    (∫ ω, bennettTruncate u (T ω) j ^ 2 ∂μ) ≤ ∫ ω, T ω j ^ 2 ∂μ :=
  integral_mono (integrable_bennettTruncate_coordinate_sq hT j hsecond) hsecond
    (fun ω => bennettTruncate_coordinate_sq_le u (T ω) j)

/-- The pointwise omitted-tail estimate for a genuine real exponent q>1. -/
theorem norm_bennettRemainder_le_rpow {p : ℕ} (x : Vector p)
    {u q : ℝ} (hu : 0 < u) (hq : 1 < q) :
    ‖x - bennettTruncate u x‖ ≤ ‖x‖ ^ q / u ^ (q - 1) := by
  by_cases hx : ‖x‖ ≤ u
  · simp only [bennettTruncate, if_pos hx, sub_self, norm_zero]
    exact div_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg hu.le _)
  · have hux : u ≤ ‖x‖ := le_of_lt (lt_of_not_ge hx)
    have hpos : 0 < ‖x‖ := hu.trans_le hux
    have hm : u ^ (q - 1) ≤ ‖x‖ ^ (q - 1) :=
      Real.rpow_le_rpow hu.le hux (by linarith)
    have hf : ‖x‖ * ‖x‖ ^ (q - 1) = ‖x‖ ^ q := by
      calc
        _ = ‖x‖ ^ (1 : ℝ) * ‖x‖ ^ (q - 1) := by rw [Real.rpow_one]
        _ = ‖x‖ ^ ((1 : ℝ) + (q - 1)) := (Real.rpow_add hpos _ _).symm
        _ = _ := by congr 1; ring
    simp only [bennettTruncate, if_neg hx, sub_zero]
    apply (le_div_iff₀ (Real.rpow_pos_of_pos hu _)).mpr
    exact (mul_le_mul_of_nonneg_left hm (norm_nonneg _)).trans_eq hf

theorem integrable_bennettRemainder (hT : Measurable T) (hu : 0 < u) (hq : 1 < q)
    (hmoment : Integrable (fun ω => ‖T ω‖ ^ q) μ) :
    Integrable (fun ω => T ω - bennettTruncate u (T ω)) μ := by
  apply (hmoment.div_const (u ^ (q - 1))).mono'
    (hT.sub (measurable_bennettTruncate_random hT)).aestronglyMeasurable
  exact Filter.Eventually.of_forall (fun ω => norm_bennettRemainder_le_rpow (T ω) hu hq)

/-- A genuine norm q-moment with q>1 also gives integrability of the original
vector, so the expected norm of its sum is an actual finite expectation. -/
theorem integrable_of_bennett_norm_moment [IsFiniteMeasure μ]
    (hT : Measurable T) (hq : 1 < q)
    (hmoment : Integrable (fun ω => ‖T ω‖ ^ q) μ) : Integrable T μ := by
  have hb : Integrable (fun ω => bennettTruncate 1 (T ω)) μ :=
    integrable_bennettTruncate hT (by norm_num : (0 : ℝ) ≤ 1)
  have hr := integrable_bennettRemainder hT (by norm_num : (0 : ℝ) < 1) hq hmoment
  convert hb.add hr using 1
  funext ω
  change T ω = bennettTruncate 1 (T ω) + (T ω - bennettTruncate 1 (T ω))
  rw [← add_sub_assoc, add_sub_cancel_left]

theorem integral_norm_bennettRemainder_le (hT : Measurable T)
    (hu : 0 < u) (hq : 1 < q)
    (hmoment : Integrable (fun ω => ‖T ω‖ ^ q) μ) :
    (∫ ω, ‖T ω - bennettTruncate u (T ω)‖ ∂μ) ≤
      (∫ ω, ‖T ω‖ ^ q ∂μ) / u ^ (q - 1) := by
  calc
    _ ≤ ∫ ω, ‖T ω‖ ^ q / u ^ (q - 1) ∂μ :=
      integral_mono (integrable_bennettRemainder hT hu hq hmoment).norm
        (hmoment.div_const _) (fun ω => norm_bennettRemainder_le_rpow (T ω) hu hq)
    _ = _ := integral_div _ _

/-- The actual expected maximum norm of the omitted sum is bounded by
the sum of the marginal q-moment tails, without coordinate independence. -/
theorem integral_norm_sum_bennettRemainder_le
    {Ts : Fin n → Ω → Vector p} (hT : ∀ i, Measurable (Ts i))
    (hu : 0 < u) (hq : 1 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖Ts i ω‖ ^ q) μ) :
    (∫ ω, ‖∑ i, (Ts i ω - bennettTruncate u (Ts i ω))‖ ∂μ) ≤
      (∑ i, ∫ ω, ‖Ts i ω‖ ^ q ∂μ) / u ^ (q - 1) := by
  have hi (i : Fin n) := integrable_bennettRemainder (hT i) hu hq (hmoment i)
  calc
    _ ≤ ∫ ω, ∑ i, ‖Ts i ω - bennettTruncate u (Ts i ω)‖ ∂μ :=
      integral_mono (integrable_finset_sum Finset.univ (fun i _ => hi i)).norm
        (integrable_finset_sum Finset.univ (fun i _ => (hi i).norm))
        (fun ω => norm_sum_le _ _)
    _ = ∑ i, ∫ ω, ‖Ts i ω - bennettTruncate u (Ts i ω)‖ ∂μ :=
      integral_finset_sum Finset.univ (fun i _ => (hi i).norm)
    _ ≤ ∑ i, (∫ ω, ‖Ts i ω‖ ^ q ∂μ) / u ^ (q - 1) :=
      Finset.sum_le_sum (fun i _ => integral_norm_bennettRemainder_le (hT i) hu hq (hmoment i))
    _ = _ := (Finset.sum_div ..).symm

theorem integral_norm_sum_bennettRemainder_le_budget
    {Ts : Fin n → Ω → Vector p} (hT : ∀ i, Measurable (Ts i))
    (hu : 0 < u) (hq : 1 < q)
    (hmoment : ∀ i, Integrable (fun ω => ‖Ts i ω‖ ^ q) μ)
    (A : ℝ) (hbudget : (∑ i, ∫ ω, ‖Ts i ω‖ ^ q ∂μ) ≤ A ^ q) :
    (∫ ω, ‖∑ i, (Ts i ω - bennettTruncate u (Ts i ω))‖ ∂μ) ≤
      A ^ q / u ^ (q - 1) :=
  (integral_norm_sum_bennettRemainder_le hT hu hq hmoment).trans
    (div_le_div_of_nonneg_right hbudget (Real.rpow_nonneg hu.le _))

/-- Genuine zero second moments force every coordinate to vanish a.e. -/
theorem ae_eq_zero_of_coordinate_second_moments
    (hsecond : ∀ j, Integrable (fun ω => T ω j ^ 2) μ)
    (hzero : ∀ j, (∫ ω, T ω j ^ 2 ∂μ) = 0) : T =ᵐ[μ] 0 := by
  have hj (j : Fin p) : ∀ᵐ ω ∂μ, T ω j = 0 := by
    have hh := (integral_eq_zero_iff_of_nonneg
      (fun ω => sq_nonneg (T ω j)) (hsecond j)).mp (hzero j)
    filter_upwards [hh] with ω hω
    exact sq_eq_zero_iff.mp hω
  filter_upwards [ae_all_iff.mpr hj] with ω hω
  ext j
  exact hω j

/-- The v=0 case of G.4 holds under its actual summed coordinate-second-
moment budget, without independence or an assumption that the sum vanishes. -/
theorem sum_ae_eq_zero_of_coordinate_second_moment_budget_zero
    {Ts : Fin n → Ω → Vector p}
    (hsecond : ∀ i j, Integrable (fun ω => Ts i ω j ^ 2) μ)
    (hbudget : ∀ j, (∑ i, ∫ ω, Ts i ω j ^ 2 ∂μ) ≤ 0) :
    (fun ω => ∑ i, Ts i ω) =ᵐ[μ] 0 := by
  have hz (i : Fin n) : Ts i =ᵐ[μ] 0 := by
    apply ae_eq_zero_of_coordinate_second_moments (hsecond i)
    intro j
    have hn (k : Fin n) : 0 ≤ ∫ ω, Ts k ω j ^ 2 ∂μ :=
      integral_nonneg (fun ω => sq_nonneg _)
    exact le_antisymm
      ((Finset.single_le_sum (fun k _ => hn k) (Finset.mem_univ i)).trans (hbudget j))
      (hn i)
  filter_upwards [ae_all_iff.mpr hz] with ω hω
  simp only [hω, Finset.sum_const_zero, Pi.zero_apply]

end

end RectangleCLT.Companion.SplitV4
