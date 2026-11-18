import GenericChaining
import RectangleCLT.Statement
import RectangleCLTArxivV1.SignedCoordinates
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Probability.Variance

/-!
# Chaining comparisons in the printed proof of Lemma C.2

This file records the admissible-subset convention, metric homogeneity, the
singleton-then-full discrete nets, and the second-moment bound for Dirksen's
base-point term. The logarithm is the paper's `log (e p)`.
-/

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

/-- The nonempty first admissible subset has exactly one member. -/
theorem admissible_first_card {T : Type*} (A : GenericChaining.FiniteNets T) :
    (A.centers 0).card = 1 := by
  have hpos := Finset.card_pos.mpr (A.nonempty 0)
  have hle := A.card_le 0
  simp only [GenericChaining.capacity] at hle
  omega

/-- The exponential functional uses precisely the printed admissible subsets. -/
theorem gamma1_eq_admissible_subsets {T : Type*} (d : T → T → ℝ≥0∞) :
    GenericChaining.gamma1 d = ⨅ A : GenericChaining.FiniteNets T,
      ⨆ t, ∑' k, (2 : ℝ≥0∞) ^ k * ⨅ s : A.centers k, d t s :=
  GenericChaining.gamma_eq_finset _ _

/-- The Gaussian functional uses precisely the printed admissible subsets. -/
theorem gamma2_eq_admissible_subsets {T : Type*} (d : T → T → ℝ≥0∞) :
    GenericChaining.gamma2 d = ⨅ A : GenericChaining.FiniteNets T,
      ⨆ t, ∑' k, ENNReal.ofReal (Real.sqrt 2) ^ k * ⨅ s : A.centers k, d t s :=
  GenericChaining.gamma_eq_finset _ _

/-- The library's Gaussian level weight is the printed `2^(k/2)`. -/
theorem gaussian_level_weight (k : ℕ) :
    ENNReal.ofReal ((2 : ℝ) ^ ((k : ℝ) / 2)) = ENNReal.ofReal (Real.sqrt 2) ^ k := by
  rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg 2), Real.sqrt_eq_rpow,
    ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
  congr 2
  ring

theorem gamma1_metric_homogeneity {T : Type*} [Nonempty T]
    (d : T → T → ℝ≥0) (c : ℝ≥0) :
    (GenericChaining.gamma1 (fun s t => ((c * d s t : ℝ≥0) : ℝ≥0∞))).toReal =
      (c : ℝ) * (GenericChaining.gamma1 (fun s t => (d s t : ℝ≥0∞))).toReal := by
  simp_rw [ENNReal.coe_mul]
  rw [GenericChaining.gamma1, GenericChaining.gamma_mul_nnreal,
    ENNReal.toReal_mul, ENNReal.coe_toReal]
  rfl

theorem gamma2_metric_homogeneity {T : Type*} [Nonempty T]
    (d : T → T → ℝ≥0) (c : ℝ≥0) :
    (GenericChaining.gamma2 (fun s t => ((c * d s t : ℝ≥0) : ℝ≥0∞))).toReal =
      (c : ℝ) * (GenericChaining.gamma2 (fun s t => (d s t : ℝ≥0∞))).toReal :=
  GenericChaining.gamma2_toReal_mul_nnreal _ _

/-- The printed cutoff is the least level at which `2^(2^k)` can contain `m` points. -/
def discreteCutoff (m : ℕ) : ℕ := Nat.clog 2 (Nat.clog 2 m)

theorem discreteCutoff_le_iff (m k : ℕ) :
    discreteCutoff m ≤ k ↔ m ≤ 2 ^ (2 ^ k) := by
  rw [discreteCutoff, ← Nat.le_pow_iff_clog_le (by decide : 1 < 2),
    ← Nat.le_pow_iff_clog_le (by decide : 1 < 2)]

theorem discreteCutoff_pos {m : ℕ} (hm : 3 ≤ m) : 0 < discreteCutoff m := by
  by_contra hnot
  have hzero : discreteCutoff m ≤ 0 := Nat.le_zero.mpr (Nat.eq_zero_of_not_pos hnot)
  have h := (discreteCutoff_le_iff m 0).mp hzero
  norm_num at h
  omega

theorem discreteCutoff_capacity {m : ℕ} (hm : 3 ≤ m) (k : ℕ)
    (hk : discreteCutoff m ≤ k) : m ≤ GenericChaining.capacity k := by
  cases k with
  | zero => have := discreteCutoff_pos hm; omega
  | succ k => exact (discreteCutoff_le_iff m (k + 1)).mp hk

/-- Minimality of the printed cutoff gives the logarithmic geometric-sum bound. -/
theorem discreteCutoff_weight_le_log {m : ℕ} (hm : 3 ≤ m) :
    ((2 ^ discreteCutoff m - 1 : ℕ) : ℝ) ≤ 4 * Real.log (m : ℝ) := by
  let K := discreteCutoff m
  have hK : 0 < K := discreteCutoff_pos hm
  have hprev : 2 ^ (2 ^ (K - 1)) < m := by
    apply Nat.lt_of_not_ge
    intro h
    have hh := (discreteCutoff_le_iff m (K - 1)).mpr h
    change K ≤ K - 1 at hh
    omega
  have hreal : (2 : ℝ) ^ (2 ^ (K - 1)) < (m : ℝ) := by exact_mod_cast hprev
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < 2 ^ (2 ^ (K - 1))) hreal
  rw [Real.log_pow] at hlog
  have hhalf := GenericChaining.log_two_ge_half
  have hpow : 0 ≤ ((2 : ℝ) ^ (K - 1)) := by positivity
  have hcast : ((2 ^ (K - 1) : ℕ) : ℝ) = (2 : ℝ) ^ (K - 1) := by norm_cast
  rw [hcast] at hlog
  have hsucc : K - 1 + 1 = K := Nat.sub_add_cancel hK
  have hdouble : (2 : ℝ) ^ K = 2 * (2 : ℝ) ^ (K - 1) := by
    nth_rw 1 [← hsucc]
    rw [pow_succ]
    ring
  have hsub : ((2 ^ K - 1 : ℕ) : ℝ) ≤ (2 : ℝ) ^ K := by
    exact_mod_cast Nat.sub_le (2 ^ K) 1
  change ((2 ^ K - 1 : ℕ) : ℝ) ≤ _
  nlinarith

/-- An actual admissible-subset witness: the zero base point until the
cutoff, and every original index thereafter. -/
noncomputable def singletonThenFullNets {T : Type*} [Fintype T] [DecidableEq T]
    (t₀ : T) (K : ℕ) (hK : ∀ k, K ≤ k → Fintype.card T ≤ GenericChaining.capacity k) :
    GenericChaining.FiniteNets T where
  centers k := if k < K then {t₀} else Finset.univ
  nonempty k := by
    split
    · exact Finset.singleton_nonempty _
    · exact ⟨t₀, Finset.mem_univ _⟩
  card_le k := by
    split
    · simpa only [Finset.card_singleton] using GenericChaining.capacity_pos k
    · simpa only [Finset.card_univ] using hK k (by omega)

theorem singletonThenFullNets_before {T : Type*} [Fintype T] [DecidableEq T]
    (t₀ : T) (K : ℕ) (hK) {k : ℕ} (hk : k < K) :
    (singletonThenFullNets t₀ K hK).centers k = {t₀} := by
  simp [singletonThenFullNets, hk]

theorem singletonThenFullNets_after {T : Type*} [Fintype T] [DecidableEq T]
    (t₀ : T) (K : ℕ) (hK) {k : ℕ} (hk : K ≤ k) :
    (singletonThenFullNets t₀ K hK).centers k = Finset.univ := by
  simp [singletonThenFullNets, Nat.not_lt.mpr hk]

/-- The checked discrete cutoff bound is applied with the actual least cutoff. -/
theorem gamma1_discrete_cutoff {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (δ : ℝ≥0) (hm : 3 ≤ Fintype.card T) :
    (GenericChaining.gamma1 (GenericChaining.discreteDist (T := T) (δ : ℝ≥0∞))).toReal ≤
      ((2 ^ discreteCutoff (Fintype.card T) - 1 : ℕ) : ℝ) * (δ : ℝ) := by
  have h := GenericChaining.gamma1_discrete_le_cutoff (T := T) (δ : ℝ≥0∞)
    (discreteCutoff (Fintype.card T)) (discreteCutoff_capacity hm)
  have hf : (((2 ^ discreteCutoff (Fintype.card T) - 1 : ℕ) : ℝ≥0∞) * δ) ≠ ⊤ := by
    finiteness
  have hr := ENNReal.toReal_mono hf h
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal] using hr

/-- A dimension-free real logarithmic estimate for the discrete functional. -/
theorem gamma1_discrete_log {T : Type*} [Fintype T] [Nonempty T] [DecidableEq T]
    (δ : ℝ≥0) (hm : 2 ≤ Fintype.card T) :
    (GenericChaining.gamma1 (GenericChaining.discreteDist (T := T) (δ : ℝ≥0∞))).toReal ≤
      4 * (δ : ℝ) * Real.log (Fintype.card T : ℝ) := by
  let m := Fintype.card T
  have hm0 : m ≠ 0 := by dsimp [m]; omega
  have hpow : (2 : ℝ) ^ m.log2 ≤ (m : ℝ) := by exact_mod_cast Nat.log2_self_le hm0
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < 2 ^ m.log2) hpow
  rw [Real.log_pow] at hlog
  have hhalf := GenericChaining.log_two_ge_half
  have hnat : 0 ≤ (m.log2 : ℝ) := Nat.cast_nonneg _
  have hn : (m.log2 : ℝ) ≤ 2 * Real.log (m : ℝ) := by nlinarith
  have h := GenericChaining.gamma1_discrete_le_log2 (T := T) (δ : ℝ≥0∞) hm
  have hf : (((2 * m.log2 : ℕ) : ℝ≥0∞) * δ) ≠ ⊤ := by finiteness
  have hr := ENNReal.toReal_mono hf h
  simp only [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.coe_toReal,
    Nat.cast_mul, Nat.cast_ofNat] at hr
  norm_num at hr
  have hδ := δ.coe_nonneg
  dsimp [m] at *
  nlinarith

@[simp] theorem signedDiscreteMetric_self {p : ℕ} (δ : ℝ≥0) (t : SignedIndex p) :
    signedDiscreteMetric δ t t = 0 := by simp [signedDiscreteMetric]

theorem signedDiscreteMetric_symm {p : ℕ} (δ : ℝ≥0) (s t : SignedIndex p) :
    signedDiscreteMetric δ s t = signedDiscreteMetric δ t s := by
  simp only [signedDiscreteMetric, eq_comm]

theorem signedDiscreteMetric_triangle {p : ℕ} (δ : ℝ≥0) (s t c : SignedIndex p) :
    signedDiscreteMetric δ s t ≤ signedDiscreteMetric δ s c + signedDiscreteMetric δ t c := by
  by_cases hst : s = t
  · subst t
    simp only [signedDiscreteMetric_self]
    positivity
  · by_cases hsc : s = c
    · subst c
      rw [signedDiscreteMetric_self, zero_add, signedDiscreteMetric_symm]
    · simp only [signedDiscreteMetric, hst, hsc, if_false]
      exact le_add_of_nonneg_right (zero_le _)

/-- The signed cardinality contributes at most a universal multiple of the
paper's logarithm, with the case `p = 1` included. -/
theorem signed_card_log_le_dimensionLog {p : ℕ} (hp : 1 ≤ p) :
    Real.log ((2 * p + 1 : ℕ) : ℝ) ≤ 2 * RectangleCLT.dimensionLog p := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hp)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hcard : ((2 * p + 1 : ℕ) : ℝ) ≤ 3 * (p : ℝ) := by push_cast; linarith
  have hlog := Real.log_le_log (by positivity : (0 : ℝ) < ((2 * p + 1 : ℕ) : ℝ)) hcard
  rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) hp0.ne'] at hlog
  have hlog3 : Real.log 3 ≤ 2 :=
    (Real.log_le_iff_le_exp (by norm_num : (0 : ℝ) < 3)).mpr (by
      linarith [Real.add_one_le_exp (2 : ℝ)])
  have hlogp : 0 ≤ Real.log (p : ℝ) := Real.log_nonneg hp1
  rw [RectangleCLT.dimensionLog, Real.log_mul (Real.exp_ne_zero _) hp0.ne', Real.log_exp]
  linarith

/-- The discrete contribution in C2.5 is logarithmic in the original number
of coordinates; no canonical-distance quotient is used. -/
theorem signed_gamma1_discrete_le {p : ℕ} (hp : 1 ≤ p) (δ : ℝ≥0) :
    (GenericChaining.gamma1 (fun s t : SignedIndex p =>
      (signedDiscreteMetric δ s t : ℝ≥0∞))).toReal ≤
        8 * (δ : ℝ) * RectangleCLT.dimensionLog p := by
  simp_rw [signedDiscreteMetric_coe]
  have hcard : 3 ≤ Fintype.card (SignedIndex p) := by rw [signedIndex_card]; omega
  have h := gamma1_discrete_cutoff (T := SignedIndex p) δ hcard
  rw [signedIndex_card] at h
  have hweight := discreteCutoff_weight_le_log (by omega : 3 ≤ 2 * p + 1)
  have hlog := signed_card_log_le_dimensionLog hp
  have hδ := δ.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_right hweight hδ
  nlinarith

/-- The explicit printed singleton-zero then full-signed-index net. -/
noncomputable def signedDiscreteNets {p : ℕ} (hp : 1 ≤ p) :
    GenericChaining.FiniteNets (SignedIndex p) :=
  singletonThenFullNets none (discreteCutoff (2 * p + 1))
    (fun k hk => by
      rw [signedIndex_card]
      exact discreteCutoff_capacity (by omega : 3 ≤ 2 * p + 1) k hk)

theorem signedDiscreteNets_initial {p : ℕ} (hp : 1 ≤ p) {k : ℕ}
    (hk : k < discreteCutoff (2 * p + 1)) : (signedDiscreteNets hp).centers k = {none} :=
  singletonThenFullNets_before _ _ _ hk

theorem signedDiscreteNets_terminal {p : ℕ} (hp : 1 ≤ p) {k : ℕ}
    (hk : discreteCutoff (2 * p + 1) ≤ k) :
    (signedDiscreteNets hp).centers k = Finset.univ :=
  singletonThenFullNets_after _ _ _ hk

/-- Unit second moment bounds the first absolute moment by one. -/
theorem integral_abs_le_one_of_second_moment {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ}
    (hX : Integrable X μ) (hXsq : Integrable (fun ω => X ω ^ 2) μ)
    (hsecond : ∫ ω, X ω ^ 2 ∂μ ≤ 1) : (∫ ω, |X ω| ∂μ) ≤ 1 := by
  have hsq : Integrable (fun ω => |X ω| ^ 2) μ := by simpa only [sq_abs] using hXsq
  have hL2 := (memLp_two_iff_integrable_sq hX.abs.aestronglyMeasurable).mpr hsq
  have hv := variance_nonneg (fun ω => |X ω|) μ
  rw [variance_def' hL2] at hv
  simp only [Pi.pow_apply, sq_abs] at hv
  have hnn : 0 ≤ ∫ ω, |X ω| ∂μ := integral_nonneg (fun ω => abs_nonneg _)
  nlinarith

/-- The two times supremum of first absolute moments in Dirksen is at most
two for the zero and signed coordinates of a unit-second-moment vector. -/
theorem signed_first_absolute_moment_le_one {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (W : Ω → Fin p → ℝ)
    (hW : ∀ j, Integrable (fun ω => W ω j) μ)
    (hWsq : ∀ j, Integrable (fun ω => W ω j ^ 2) μ)
    (hsecond : ∀ j, ∫ ω, W ω j ^ 2 ∂μ ≤ 1) (t : SignedIndex p) :
    (∫ ω, |signedProcess W t ω| ∂μ) ≤ 1 := by
  cases t with
  | none => simp
  | some v =>
    rcases v with ⟨b, j⟩
    have hj := integral_abs_le_one_of_second_moment (hW j) (hWsq j) (hsecond j)
    cases b <;> simpa only [signedProcess, signedCoordinate, abs_neg] using hj

/-- C2.4: Dirksen applied at the actual zero base point, with the Bernstein
scale factors recorded before homogeneity is used. -/
theorem signed_dirksen_expectation {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] (W : Ω → Fin p → ℝ) (δ : ℝ≥0)
    (d₂ : SignedIndex p → SignedIndex p → ℝ≥0)
    (diag₂ : ∀ t, d₂ t t = 0) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (htail : GenericChaining.HasMixedTail μ (signedProcess W)
      (fun s t => 4 * signedDiscreteMetric δ s t) (fun s t => 2 * d₂ s t))
    (hW : ∀ j, Integrable (fun ω => W ω j) μ)
    (hWsq : ∀ j, Integrable (fun ω => W ω j ^ 2) μ)
    (hsecond : ∀ j, ∫ ω, W ω j ^ 2 ∂μ ≤ 1) :
    (∫ ω, ‖W ω‖ ∂μ) ≤
      96 * (GenericChaining.gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        192 * (GenericChaining.gamma1 (fun s t : SignedIndex p =>
          (signedDiscreteMetric δ s t : ℝ≥0∞))).toReal + 2 := by
  have hInt (s t : SignedIndex p) : Integrable
      (fun ω => signedProcess W s ω - signedProcess W t ω) μ :=
    (integrable_signedCoordinate hW s).sub (integrable_signedCoordinate hW t)
  have hD := GenericChaining.dirksen_expectation (signedProcess W)
    (fun s t => 4 * signedDiscreteMetric δ s t) (fun s t => 2 * d₂ s t)
    (fun t => by simp [signedDiscreteMetric_self]) (fun t => by simp [diag₂])
    (fun s t => congrArg (fun z => 4 * z) (signedDiscreteMetric_symm δ s t))
    (fun s t => congrArg (fun z => 2 * z) (symm₂ s t))
    (fun s t c => by
      change 4 * signedDiscreteMetric δ s t ≤ _
      rw [← mul_add]
      exact mul_le_mul_left' (signedDiscreteMetric_triangle δ s t c) 4)
    (fun s t c => by
      change 2 * d₂ s t ≤ _
      rw [← mul_add]
      exact mul_le_mul_left' (tri₂ s t c) 2)
    htail hInt none
  simp_rw [signed_incrementMaximum_eq_norm] at hD
  rw [gamma2_metric_homogeneity, gamma1_metric_homogeneity] at hD
  have hbase : (⨆ t : SignedIndex p, ∫ ω, |signedProcess W t ω - signedProcess W none ω| ∂μ) ≤ 1 := by
    apply ciSup_le
    intro t
    simpa only [signedProcess_none, sub_zero] using
      signed_first_absolute_moment_le_one W hW hWsq hsecond t
  simp only [signedProcess_none, sub_zero] at hbase
  norm_num [GenericChaining.dirksenConstant] at hD
  nlinarith

/-- C2.4–C2.5 combined, retaining the canonical Gaussian chaining term. -/
theorem signed_dirksen_expectation_log {p : ℕ} (hp : 1 ≤ p)
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    (W : Ω → Fin p → ℝ) (δ : ℝ≥0) (d₂ : SignedIndex p → SignedIndex p → ℝ≥0)
    (diag₂ : ∀ t, d₂ t t = 0) (symm₂ : ∀ s t, d₂ s t = d₂ t s)
    (tri₂ : ∀ s t c, d₂ s t ≤ d₂ s c + d₂ t c)
    (htail : GenericChaining.HasMixedTail μ (signedProcess W)
      (fun s t => 4 * signedDiscreteMetric δ s t) (fun s t => 2 * d₂ s t))
    (hW : ∀ j, Integrable (fun ω => W ω j) μ)
    (hWsq : ∀ j, Integrable (fun ω => W ω j ^ 2) μ)
    (hsecond : ∀ j, ∫ ω, W ω j ^ 2 ∂μ ≤ 1) :
    (∫ ω, ‖W ω‖ ∂μ) ≤
      96 * (GenericChaining.gamma2 (fun s t => (d₂ s t : ℝ≥0∞))).toReal +
        1536 * (δ : ℝ) * RectangleCLT.dimensionLog p + 2 := by
  have hD := signed_dirksen_expectation W δ d₂ diag₂ symm₂ tri₂ htail hW hWsq hsecond
  have hdiscrete := signed_gamma1_discrete_le hp δ
  nlinarith

end RectangleCLTArxivV1
