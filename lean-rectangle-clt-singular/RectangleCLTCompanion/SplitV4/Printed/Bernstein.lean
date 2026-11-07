import RectangleCLTCompanion.SplitV4.EnvelopeMaximum
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Layercake
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

/-!
# The classical Bernstein denominator in the printed Split-V4 route

This module adds the exact scalar Bernstein estimate printed in the proof of
G.1.  The older Bennett-based maximum argument is retained.  All bounds below
apply to actual exponential moments, rather than assumed analytic estimates.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4.Printed

noncomputable section

/-- The factorial comparison behind the printed denominator `1 - a / 3`. -/
theorem bernstein_factorial_lower_bound (k : ℕ) :
    (2 : ℝ) * 3 ^ k ≤ ((k + 2).factorial : ℝ) := by
  have h := Nat.factorial_mul_pow_le_factorial (m := 2) (n := k)
  norm_num at h ⊢
  simpa only [Nat.add_comm 2 k] using (show (2 : ℝ) * 3 ^ k ≤ ((2 + k).factorial : ℝ) by exact_mod_cast h)

/-- The full Bernstein bound for the Bennett correction, on its stated range. -/
theorem bennettCorrection_le_bernstein {a : ℝ} (ha : 0 ≤ a) (ha3 : a < 3) :
    bennettCorrection a ≤ a ^ 2 / (2 * (1 - a / 3)) := by
  have hs := Real.summable_pow_div_factorial a
  have hs2 : Summable (fun k : ℕ => a ^ (k + 2) / ((k + 2).factorial : ℝ)) :=
    (summable_nat_add_iff 2).mpr hs
  have he : (∑' k : ℕ, a ^ k / (k.factorial : ℝ)) = Real.exp a := by
    simpa only [Real.exp_eq_exp_ℝ] using (NormedSpace.expSeries_div_hasSum_exp ℝ a).tsum_eq
  have htail : (∑' k : ℕ, a ^ (k + 2) / ((k + 2).factorial : ℝ)) =
      bennettCorrection a := by
    have h := hs.sum_add_tsum_nat_add 2
    rw [he] at h
    norm_num [Finset.sum_range_succ, bennettCorrection] at h ⊢
    linarith
  have hratio0 : 0 ≤ a / 3 := by positivity
  have hratio1 : a / 3 < 1 := by linarith
  have hnorm : ‖a / 3‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hratio0]
  have hgeom : Summable (fun k : ℕ => a ^ 2 / 2 * (a / 3) ^ k) :=
    (summable_geometric_of_norm_lt_one hnorm).mul_left _
  have hterm (k : ℕ) : a ^ (k + 2) / ((k + 2).factorial : ℝ) ≤
      a ^ 2 / 2 * (a / 3) ^ k := by
    have hden : 0 < (2 : ℝ) * 3 ^ k := by positivity
    have h := div_le_div_of_nonneg_left (pow_nonneg ha (k + 2)) hden
      (bernstein_factorial_lower_bound k)
    calc
      _ ≤ a ^ (k + 2) / (2 * 3 ^ k) := h
      _ = _ := by rw [pow_add, div_pow]; ring
  rw [← htail]
  calc
    _ ≤ ∑' k : ℕ, a ^ 2 / 2 * (a / 3) ^ k := tsum_le_tsum hterm hs2 hgeom
    _ = a ^ 2 / 2 * (1 - a / 3)⁻¹ := by
      rw [tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
    _ = _ := by
      have hd : 1 - a / 3 ≠ 0 := ne_of_gt (by linarith)
      field_simp


variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- Exact Bernstein MGF on the entire positive half of the printed range. -/
theorem independent_sum_bernstein_mgf_nonneg {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hXi : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {b t v : ℝ}
    (hb : 0 < b) (ht : 0 ≤ t) (htb : t * b < 3)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, X i ω ≤ b)
    (hv : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (t * ∑ i, X i ω)) μ ∧
    mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp (t ^ 2 * v / (2 * (1 - t * b / 3))) := by
  have hv0 : 0 ≤ v := (Finset.sum_nonneg (fun i _ => integral_nonneg
    (fun ω => sq_nonneg (X i ω)))).trans hv
  have h := independent_sum_bennett_mgf X hX hind hXi hX2 hmean hb ht hbound hv
  refine ⟨h.1, h.2.trans (Real.exp_le_exp.mpr ?_)⟩
  have hc := mul_le_mul_of_nonneg_left
    (bennettCorrection_le_bernstein (mul_nonneg ht hb.le) htb)
    (div_nonneg hv0 (sq_nonneg b))
  have heq : v / b ^ 2 * ((t * b) ^ 2 / (2 * (1 - t * b / 3))) =
      t ^ 2 * v / (2 * (1 - t * b / 3)) := by
    have hcancel : v / b ^ 2 * (t * b) ^ 2 = t ^ 2 * v := by
      field_simp
      <;> ring
    rw [← mul_div_assoc, hcancel]
  exact hc.trans_eq heq

/-- The exact MGF display in G.1, including negative Laplace parameters. -/
theorem independent_sum_bernstein_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ)
    (hXi : ∀ i, Integrable (X i) μ)
    (hX2 : ∀ i, Integrable (fun ω => X i ω ^ 2) μ)
    (hmean : ∀ i, (∫ ω, X i ω ∂μ) = 0) {b t v : ℝ}
    (hb : 0 < b) (htb : |t| * b < 3)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |X i ω| ≤ b)
    (hv : (∑ i, ∫ ω, X i ω ^ 2 ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (t * ∑ i, X i ω)) μ ∧
    mgf (fun ω => ∑ i, X i ω) μ t ≤
      Real.exp (t ^ 2 * v / (2 * (1 - |t| * b / 3))) := by
  rcases le_total 0 t with ht | ht
  · simpa only [abs_of_nonneg ht] using independent_sum_bernstein_mgf_nonneg
      X hX hind hXi hX2 hmean hb ht
      (by simpa only [abs_of_nonneg ht] using htb)
      (fun i => (hbound i).mono (fun _ hω => (le_abs_self _).trans hω)) hv
  · have h := independent_sum_bernstein_mgf_nonneg
      (fun i ω => -X i ω) (fun i => (hX i).neg)
      (hind.comp (fun _ x => -x) (fun _ => measurable_neg))
      (fun i => (hXi i).neg) (fun i => by simpa only [neg_sq] using hX2 i)
      (fun i => by rw [integral_neg, hmean i, neg_zero]) hb (neg_nonneg.mpr ht)
      (by simpa only [abs_of_nonpos ht] using htb)
      (fun i => (hbound i).mono (fun _ hω => (neg_le_abs _).trans hω))
      (by simpa only [neg_sq] using hv)
    simpa only [Finset.sum_neg_distrib, neg_mul_neg, neg_sq, abs_of_nonpos ht, mgf] using h


/-- Integrating the exponential tail, rather than using Jensen, gives the
usual maximum estimate.  The layer-cake identity is used for the genuine
positive excess over `A/t`; no tail integral is an input assumption. -/
theorem expected_le_exp_moment_by_tail_integration (S : Ω → ℝ)
    (hS : Integrable S μ) {t A : ℝ} (ht : 0 < t)
    (he : Integrable (fun ω => Real.exp (t * S ω)) μ)
    (hmgf : mgf S μ t ≤ Real.exp A) :
    (∫ ω, S ω ∂μ) ≤ (A + 1) / t := by
  let a := A / t
  let E : Ω → ℝ := fun ω => max (S ω - a) 0
  have hE : Integrable E μ := (hS.sub (integrable_const a)).sup (integrable_const 0)
  have htail (r : ℝ) (hr : 0 < r) :
      μ.real {ω | r < E ω} ≤ Real.exp (-t * r) := by
    have hs : {ω | r < E ω} ⊆ {ω | a + r ≤ S ω} := by
      intro ω hω
      have hmax : r < S ω - a := (lt_max_iff.mp hω).resolve_right (not_lt.mpr hr.le)
      change a + r ≤ S ω
      linarith
    have h := (measureReal_mono hs).trans
      (measure_ge_le_exp_mul_mgf (a + r) ht.le he)
    have hh := h.trans (mul_le_mul_of_nonneg_left hmgf (Real.exp_nonneg _))
    have heq : Real.exp (-t * (a + r)) * Real.exp A = Real.exp (-t * r) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [a]
      field_simp
      <;> ring
    exact hh.trans_eq heq
  have htailIntegral : (∫ r in Ioi (0 : ℝ), μ.real {ω | r < E ω}) ≤ 1 / t := by
    have h := integral_mono_of_nonneg (ae_of_all _ (fun _ => measureReal_nonneg))
      (integrableOn_exp_mul_Ioi (a := -t) (by linarith) 0)
      ((ae_restrict_mem measurableSet_Ioi).mono (fun r hr => htail r hr))
    simpa only [integral_exp_mul_Ioi (by linarith : -t < 0) 0,
      mul_zero, Real.exp_zero, neg_div_neg_eq, neg_neg] using h
  have hEbound : (∫ ω, E ω ∂μ) ≤ 1 / t := by
    rw [hE.integral_eq_integral_meas_lt (ae_of_all _ (fun ω => le_max_right _ _))]
    exact htailIntegral
  have hu := integral_mono_ae hS ((integrable_const a).add hE)
    (ae_of_all _ (fun ω => by dsimp [E]; linarith [le_max_left (S ω - a) 0]))
  change (∫ ω, S ω ∂μ) ≤ ∫ ω, a + E ω ∂μ at hu
  rw [integral_add (integrable_const a) hE] at hu
  simp only [integral_const, measureReal_univ_eq_one, one_smul] at hu
  calc
    _ ≤ a + ∫ ω, E ω ∂μ := hu
    _ ≤ a + 1 / t := add_le_add_left hEbound a
    _ = _ := by dsimp [a]; ring


/-- Apply scalar Bernstein to the `2p` signed coordinates before taking
an actual exponential moment of their maximum. -/
theorem bounded_vector_bernstein_exp_moment {p n : ℕ} {T : Fin n → Ω → Vector p}
    {u t v : ℝ} (h : BoundedIndependentHypotheses μ T u) (hp : 1 ≤ p)
    (hu : 0 < u) (ht : 0 < t) (htu : t * u < 3)
    (hv : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (t * ‖sumVector T ω‖)) μ ∧
      mgf (fun ω => ‖sumVector T ω‖) μ t ≤
        Real.exp (Real.log (2 * (p : ℝ)) + t ^ 2 * v / (2 * (1 - t * u / 3))) := by
  have hm (j : Fin p) := fun i : Fin n => (measurable_pi_apply j).comp (h.measurable i)
  have hi (i : Fin n) (j : Fin p) : Integrable (fun ω => T i ω j) μ := by
    apply (integrable_const u).mono' (hm j i).aestronglyMeasurable
    simpa only [Real.norm_eq_abs] using h.abs_coordinate_le i j
  have hi2 (i : Fin n) (j : Fin p) : Integrable (fun ω => T i ω j ^ 2) μ :=
    integrable_coordinate_pow_of_bounded h.measurable h.abs_coordinate_le i j 2
  have hplus (j : Fin p) := independent_sum_bernstein_mgf_nonneg
    (fun i ω => T i ω j) (hm j)
    (h.independent.comp (fun _ x => x j) (fun _ => measurable_pi_apply j))
    (fun i => hi i j) (fun i => hi2 i j) (fun i => h.centered i j) hu ht.le htu
    (fun i => (h.abs_coordinate_le i j).mono (fun _ hx => le_trans (le_abs_self _) hx)) (hv j)
  have hminus (j : Fin p) := independent_sum_bernstein_mgf_nonneg
    (fun i ω => -T i ω j) (fun i => (hm j i).neg)
    (h.independent.comp (fun _ x => -x j) (fun _ => (measurable_pi_apply j).neg))
    (fun i => (hi i j).neg) (fun i => by simpa only [neg_sq] using hi2 i j)
    (fun i => by rw [integral_neg, h.centered i j, neg_zero]) hu ht.le htu
    (fun i => (h.abs_coordinate_le i j).mono (fun _ hx => le_trans (neg_le_abs _) hx))
    (by simpa only [neg_sq] using hv j)
  let S := sumVector T
  let c := t ^ 2 * v / (2 * (1 - t * u / 3))
  have he (j : Fin p) : Integrable (fun ω => Real.exp (t * S ω j)) μ ∧
      Integrable (fun ω => Real.exp (t * (-S ω j))) μ := by
    constructor
    · simpa only [S, sumVector, Finset.sum_apply] using (hplus j).1
    · simpa only [S, sumVector, Finset.sum_apply, Finset.sum_neg_distrib] using (hminus j).1
  have hmgf (j : Fin p) : mgf (fun ω => S ω j) μ t ≤ Real.exp c ∧
      mgf (fun ω => -S ω j) μ t ≤ Real.exp c := by
    constructor
    · simpa only [S, sumVector, Finset.sum_apply] using (hplus j).2
    · simpa only [S, sumVector, Finset.sum_apply, Finset.sum_neg_distrib] using (hminus j).2
  have hsum : Integrable (fun ω => ∑ j : Fin p,
      (Real.exp (t * S ω j) + Real.exp (t * (-S ω j)))) μ :=
    integrable_finset_sum _ (fun j _ => (he j).1.add (he j).2)
  have hiNorm : Integrable (fun ω => Real.exp (t * ‖S ω‖)) μ := by
    apply hsum.mono' ((h.measurable_sum.norm.const_mul t).exp.aestronglyMeasurable)
    refine ae_of_all _ (fun ω => ?_)
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_norm_le_signed_coordinate_sum hp (S ω) t
  refine ⟨hiNorm, ?_⟩
  change (∫ ω, Real.exp (t * ‖S ω‖) ∂μ) ≤ _
  calc
    _ ≤ ∫ ω, ∑ j : Fin p, (Real.exp (t * S ω j) + Real.exp (t * (-S ω j))) ∂μ :=
      integral_mono hiNorm hsum (fun ω => exp_norm_le_signed_coordinate_sum hp (S ω) t)
    _ = ∑ j : Fin p, (mgf (fun ω => S ω j) μ t + mgf (fun ω => -S ω j) μ t) := by
      have hsi := integral_finset_sum (Finset.univ : Finset (Fin p))
        (fun j _ => (he j).1.add (he j).2)
      simp only [Pi.add_apply] at hsi
      rw [hsi]
      apply Finset.sum_congr rfl
      intro j _
      exact integral_add (he j).1 (he j).2
    _ ≤ ∑ _j : Fin p, (Real.exp c + Real.exp c) :=
      Finset.sum_le_sum (fun j _ => add_le_add (hmgf j).1 (hmgf j).2)
    _ = (2 * (p : ℝ)) * Real.exp c := by simp; ring
    _ = _ := by
      rw [Real.exp_add, Real.exp_log (by positivity : 0 < 2 * (p : ℝ))]


/-- The `2p`-coordinate Bernstein inequality integrated to obtain the
maximum estimate used in G.1 and E.1.  This proves the printed route in
addition to the preserved Bennett/Jensen route. -/
theorem bounded_vector_bernstein_maximum_by_tail_integration {p n : ℕ}
    {T : Fin n → Ω → Vector p} {U v : ℝ}
    (h : BoundedIndependentHypotheses μ T U) (hp : 1 ≤ p)
    (hU : 0 < U) (hv : 0 ≤ v)
    (hvariance : ∀ j, (∑ i, ∫ ω, T i ω j ^ 2 ∂μ) ≤ v) :
    (∫ ω, ‖sumVector T ω‖ ∂μ) ≤
      3 * (Real.sqrt (v * dimensionLog p) + U * dimensionLog p) := by
  let L := dimensionLog p
  have hL : 0 < L := zero_lt_one.trans_le (log_exp_mul_nat_ge_one hp)
  let r := Real.sqrt (v / L)
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  let D := U + r
  have hD : 0 < D := by dsimp [D]; linarith
  let t := 1 / D
  have ht : 0 < t := one_div_pos.mpr hD
  have htU : t * U ≤ 1 := by
    dsimp [t]
    rw [one_div_mul_eq_div, div_le_one hD]
    dsimp [D]
    linarith
  have hvrel : v = L * r ^ 2 := by
    dsimp [r]
    rw [Real.sq_sqrt (div_nonneg hv hL.le)]
    field_simp
  have hvdiv : v / D ≤ L * r := by
    apply (div_le_iff₀ hD).mpr
    dsimp [D]
    nlinarith [mul_nonneg hU.le (mul_nonneg hL.le hr)]
  have hsqrt : Real.sqrt (v * L) = L * r := by
    apply (Real.sqrt_eq_iff_eq_sq (mul_nonneg hv hL.le) (mul_nonneg hL.le hr)).mpr
    rw [mul_pow]
    rw [hvrel]
    ring
  have hlog : Real.log (2 * (p : ℝ)) ≤ L := by
    apply Real.log_le_log
    · have hp' : (0 : ℝ) < p := by exact_mod_cast (Nat.zero_lt_of_lt hp)
      positivity
    · have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
      exact mul_le_mul_of_nonneg_right he (Nat.cast_nonneg p)
  have hm := bounded_vector_bernstein_exp_moment h hp hU ht (by linarith) hvariance
  have hb := expected_le_exp_moment_by_tail_integration
    (fun ω => ‖sumVector T ω‖) h.integrable_norm_sum ht hm.1 hm.2
  have hL1 : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hden : 0 < 2 * (1 - t * U / 3) := by linarith
  have hfrac : t ^ 2 * v / (2 * (1 - t * U / 3)) ≤ v * t ^ 2 := by
    apply (div_le_iff₀ hden).mpr
    have hvts : 0 ≤ v * t ^ 2 := mul_nonneg hv (sq_nonneg t)
    nlinarith [mul_nonneg hvts (by linarith : 0 ≤ 1 - t * U)]
  calc
    _ ≤ (Real.log (2 * (p : ℝ)) + t ^ 2 * v / (2 * (1 - t * U / 3)) + 1) / t := hb
    _ ≤ (2 * L + v * t ^ 2) / t := div_le_div_of_nonneg_right
      (by linarith) ht.le
    _ = 2 * L * D + v / D := by dsimp [t]; field_simp; ring
    _ ≤ 2 * L * D + L * r := add_le_add_left hvdiv _
    _ ≤ _ := by
      rw [hsqrt]
      dsimp [D]
      nlinarith [mul_nonneg hU.le hL.le]

end
end RectangleCLT.Companion.SplitV4.Printed
