import RectangleCLTCompanion.LowerTwoPoint
import RectangleCLT.GaussianComponentJoinedArray
import RectangleCLT.BoundedIndependentScaling
import RectangleCLT.IndependentCovariance

/-! The genuine iid product arrays used by the lower constructions.
The rows and their coordinates are independent, with exact covariance
normalization. No asymptotic lower bound is assumed or asserted here. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

theorem lowerScalarPi_map_eval {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun z => z i) = ν i := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs,
    ← Set.univ_pi_update_univ, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem lowerScalarPi_iIndepFun {ι : Type*} [Fintype ι]
    (ν : ι → Measure ℝ) [∀ i, IsProbabilityMeasure (ν i)] :
    iIndepFun (fun i (z : ι → ℝ) => z i) (Measure.pi ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map
    (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp_rw [lowerScalarPi_map_eval ν]
  exact Measure.map_id

def lowerRowLaw (B : ℝ) (p : ℕ) : Measure (Vector p) :=
  Measure.pi (fun _ : Fin p => lowerTwoPointLaw B)

instance lowerRowLaw_isProbability (B : ℝ) (p : ℕ) :
    IsProbabilityMeasure (lowerRowLaw B p) := by
  unfold lowerRowLaw
  infer_instance

theorem lowerRowLaw_map_coordinate (B : ℝ) {p : ℕ} (j : Fin p) :
    (lowerRowLaw B p).map (fun x => x j) = lowerTwoPointLaw B :=
  lowerScalarPi_map_eval _ j

theorem lowerRowLaw_integral_coordinate (B : ℝ) {p : ℕ} (j : Fin p)
    (f : ℝ → ℝ) (hf : Measurable f) :
    (∫ x, f (x j) ∂lowerRowLaw B p) = ∫ x, f x ∂lowerTwoPointLaw B := by
  have hm := integral_map (μ := lowerRowLaw B p)
    (measurable_pi_apply j).aemeasurable hf.aestronglyMeasurable
  rw [lowerRowLaw_map_coordinate B j] at hm
  exact hm.symm

theorem lowerRowLaw_integrable_coordinate (B : ℝ) {p : ℕ} (j : Fin p) :
    Integrable (fun x : Vector p => x j) (lowerRowLaw B p) := by
  have hp : MeasurePreserving (fun x : Vector p => x j) (lowerRowLaw B p)
      (lowerTwoPointLaw B) := ⟨measurable_pi_apply j, lowerRowLaw_map_coordinate B j⟩
  exact (hp.integrable_comp (measurable_id.aestronglyMeasurable)).mpr
    (integrable_lowerTwoPointLaw B id)

theorem lowerRowLaw_centered {B : ℝ} (hB : B ≠ 0) {p : ℕ} (j : Fin p) :
    (∫ x, x j ∂lowerRowLaw B p) = 0 := by
  exact (lowerRowLaw_integral_coordinate B j id measurable_id).trans
    (lowerTwoPointLaw_centered hB)

theorem lowerRowLaw_second {B : ℝ} (hB : B ≠ 0) {p : ℕ} (j k : Fin p) :
    (∫ x, x j * x k ∂lowerRowLaw B p) = if j = k then 1 else 0 := by
  classical
  by_cases hjk : j = k
  · subst k
    rw [if_pos rfl]
    have hh := lowerRowLaw_integral_coordinate B j (fun x => x ^ 2)
      (measurable_id.pow_const 2)
    simpa only [pow_two] using hh.trans (lowerTwoPointLaw_second hB)
  · rw [if_neg hjk]
    have hi := (lowerScalarPi_iIndepFun (fun _ : Fin p => lowerTwoPointLaw B)).indepFun hjk
    have hh := hi.integral_mul_of_integrable
      (lowerRowLaw_integrable_coordinate B j) (lowerRowLaw_integrable_coordinate B k)
    change (∫ x, x j * x k ∂lowerRowLaw B p) =
      (∫ x, x j ∂lowerRowLaw B p) * (∫ x, x k ∂lowerRowLaw B p) at hh
    simpa only [lowerRowLaw_centered hB j, lowerRowLaw_centered hB k, mul_zero] using hh

theorem lowerRowLaw_bounded {B : ℝ} (hB : 1 ≤ B) (p : ℕ) :
    ∀ᵐ x ∂lowerRowLaw B p, ‖x‖ ≤ B := by
  have hB0 : 0 ≤ B := by linarith
  have hcoord : ∀ᵐ x ∂lowerRowLaw B p, ∀ j, |x j| ≤ B := by
    apply ae_all_iff.mpr
    intro j
    have hh : ∀ᵐ x ∂(lowerRowLaw B p).map (fun z => z j), |x| ≤ B := by
      rw [lowerRowLaw_map_coordinate]
      exact lowerTwoPointLaw_envelope hB
    exact (ae_map_iff (measurable_pi_apply j).aemeasurable
      (measurableSet_le measurable_id.abs measurable_const)).mp hh
  filter_upwards [hcoord] with x hx
  exact (pi_norm_le_iff_of_nonneg hB0).mpr (fun j => by simpa only [Real.norm_eq_abs] using hx j)

def lowerArrayLaw (B : ℝ) (n p : ℕ) : Measure (Fin n → Vector p) :=
  Measure.pi (fun _ : Fin n => lowerRowLaw B p)

instance lowerArrayLaw_isProbability (B : ℝ) (n p : ℕ) :
    IsProbabilityMeasure (lowerArrayLaw B n p) := by
  constructor
  simp [lowerArrayLaw, Measure.pi_univ]

def lowerRawRows {n p : ℕ} (i : Fin n) (z : Fin n → Vector p) : Vector p := z i

theorem lowerArrayLaw_map_row (B : ℝ) {n p : ℕ} (i : Fin n) :
    (lowerArrayLaw B n p).map (lowerRawRows i) = lowerRowLaw B p :=
  gaussianComponentPi_map_eval _ i

theorem lowerRawRows_boundedIndependent {B : ℝ} (hB : 1 ≤ B) (n p : ℕ) :
    BoundedIndependentHypotheses (lowerArrayLaw B n p) lowerRawRows B := by
  have hBp : 0 < B := by linarith
  exact gaussianComponentPi_boundedIndependent (Equiv.refl (Fin n))
    (fun _ => lowerRowLaw B p) (by linarith)
    (fun _ j => lowerRowLaw_centered hBp.ne' j) (fun _ => lowerRowLaw_bounded hB p)

theorem lowerRawRows_second {B : ℝ} (hB : B ≠ 0) {n p : ℕ}
    (i : Fin n) (j k : Fin p) :
    (∫ z, lowerRawRows i z j * lowerRawRows i z k ∂lowerArrayLaw B n p) =
      if j = k then 1 else 0 := by
  have hm := integral_map (μ := lowerArrayLaw B n p)
    (measurable_pi_apply i).aemeasurable
    (((measurable_pi_apply j).mul (measurable_pi_apply k)).aestronglyMeasurable)
  change (∫ y, y j * y k ∂(lowerArrayLaw B n p).map (lowerRawRows i)) = _ at hm
  rw [lowerArrayLaw_map_row B i] at hm
  exact hm.symm.trans (lowerRowLaw_second hB j k)

def lowerNormalizedRows {n p : ℕ} (i : Fin n) (z : Fin n → Vector p) : Vector p :=
  (1 / Real.sqrt n) • lowerRawRows i z

theorem lowerNormalizedRows_boundedIndependent {B : ℝ} (hB : 1 ≤ B) (n p : ℕ) :
    BoundedIndependentHypotheses (lowerArrayLaw B n p) lowerNormalizedRows
      (B / Real.sqrt n) := by
  have hh := (lowerRawRows_boundedIndependent hB n p).smul_of_nonneg
    (1 / Real.sqrt n) (by positivity)
  simpa only [one_div_mul_eq_div] using hh

theorem lowerNormalizedRows_covariance {B : ℝ} (hB : 1 ≤ B)
    {n p : ℕ} (hn : 1 ≤ n) :
    covariance (lowerArrayLaw B n p) (sumVector (lowerNormalizedRows (n := n) (p := p))) = 1 := by
  classical
  have hBp : 0 < B := by linarith
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hh := (lowerRawRows_boundedIndependent hB n p).covariance_sum_smul (1 / Real.sqrt n)
  change covariance (lowerArrayLaw B n p)
    (sumVector (fun i z => (1 / Real.sqrt n) • lowerRawRows i z)) = _
  ext j k
  rw [hh]
  simp only [Matrix.smul_apply, smul_eq_mul]
  rw [(lowerRawRows_boundedIndependent hB n p).covariance_sum]
  simp_rw [lowerRawRows_second hBp.ne']
  by_cases hjk : j = k
  · subst k
    simp only [if_pos rfl, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one, Matrix.one_apply, div_pow, one_pow,
      Real.sq_sqrt hnpos.le]
    simp [hnpos.ne']
  · simp [hjk, Matrix.one_apply]

end

end RectangleCLT.Companion
