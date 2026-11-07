import RectangleCLTCompanion.SplitV4.BennettMaximum
import RectangleCLTCompanion.SplitV4.CommonPointFourth

/-! A genuine expected maximum for independent nonnegative bounded vectors,
and its fourth-power specialization for the common-point contraction. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem exp_le_chord_of_nonneg_le {b x : ℝ} (hb : 0 < b) (hx : 0 ≤ x) (hxb : x ≤ b) :
    Real.exp (b⁻¹ * x) ≤ 1 + ((Real.exp 1 - 1) / b) * x := by
  have he := exp_le_bennett_quadratic hb (inv_nonneg.mpr hb.le) hxb
  rw [inv_mul_cancel₀ hb.ne'] at he
  have hc := bennettCorrection_nonneg (1 : ℝ)
  have hs : x^2 ≤ b*x := by nlinarith
  have hmul := mul_le_mul_of_nonneg_left hs (div_nonneg hc (sq_nonneg b))
  have hid : b⁻¹*x + (bennettCorrection 1 / b^2) * (b*x) =
      ((Real.exp 1 - 1) / b) * x := by
    unfold bennettCorrection
    field_simp
    ring
  linarith

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]

theorem nonnegative_bounded_mgf {X : Ω → ℝ} (hX : Measurable X) {b : ℝ}
    (hb : 0 < b) (hbound : ∀ᵐ ω ∂μ, 0 ≤ X ω ∧ X ω ≤ b) :
    Integrable (fun ω => Real.exp (b⁻¹ * X ω)) μ ∧
    mgf X μ b⁻¹ ≤ Real.exp (((Real.exp 1 - 1) / b) * ∫ ω, X ω ∂μ) := by
  have hi : Integrable X μ := by
    apply (integrable_const b).mono' hX.aestronglyMeasurable
    filter_upwards [hbound] with ω hω
    simpa only [Real.norm_eq_abs, abs_of_nonneg hω.1] using hω.2
  have he := integrable_exp_mul_of_bounded_above hX (inv_nonneg.mpr hb.le)
    (hbound.mono fun _ h => h.2)
  refine ⟨he, ?_⟩
  change (∫ ω, Real.exp (b⁻¹ * X ω) ∂μ) ≤ _
  have hpoly := integral_mono_ae he
    ((integrable_const (1 : ℝ)).add (hi.const_mul ((Real.exp 1 - 1)/b)))
    (hbound.mono fun _ h => exp_le_chord_of_nonneg_le hb h.1 h.2)
  have hcalc : (∫ ω, 1 + ((Real.exp 1 - 1)/b)*X ω ∂μ) =
      1 + ((Real.exp 1 - 1)/b) * ∫ ω, X ω ∂μ := by
    rw [integral_add (integrable_const (1 : ℝ)) (hi.const_mul _), integral_const_mul]
    simp
  have hscalar := Real.add_one_le_exp (((Real.exp 1 - 1)/b) * (∫ ω, X ω ∂μ))
  exact (hpoly.trans_eq hcalc).trans (by linarith)

theorem independent_nonnegative_sum_mgf {n : ℕ} (X : Fin n → Ω → ℝ)
    (hX : ∀ i, Measurable (X i)) (hind : iIndepFun X μ) {b v : ℝ}
    (hb : 0 < b) (hbound : ∀ i, ∀ᵐ ω ∂μ, 0 ≤ X i ω ∧ X i ω ≤ b)
    (hbudget : (∑ i, ∫ ω, X i ω ∂μ) ≤ v) :
    Integrable (fun ω => Real.exp (b⁻¹ * ∑ i, X i ω)) μ ∧
    mgf (fun ω => ∑ i, X i ω) μ b⁻¹ ≤ Real.exp (((Real.exp 1 - 1)/b) * v) := by
  have he (i : Fin n) := nonnegative_bounded_mgf (hX i) hb (hbound i)
  have hi := hind.integrable_exp_mul_sum hX (s := Finset.univ) (fun i _ => (he i).1)
  refine ⟨by simpa only [Finset.sum_apply] using hi, ?_⟩
  have hfun : (fun ω => ∑ i, X i ω) = ∑ i ∈ (Finset.univ : Finset (Fin n)), X i := by
    ext ω; simp
  rw [hfun, hind.mgf_sum hX Finset.univ]
  calc
    _ ≤ ∏ i : Fin n, Real.exp (((Real.exp 1 - 1)/b) * ∫ ω, X i ω ∂μ) :=
      Finset.prod_le_prod (fun _ _ => mgf_nonneg) (fun i _ => (he i).2)
    _ = Real.exp (((Real.exp 1 - 1)/b) * ∑ i, ∫ ω, X i ω ∂μ) := by
      rw [← Real.exp_sum]; congr 1; rw [Finset.mul_sum]
    _ ≤ _ := Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hbudget
      (div_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)]) hb.le))

/-- No centering or independence of coordinates is needed. Independence
is only over the summands. The variance budget here is a first moment. -/
theorem nonnegative_vector_expected_maximum {p n : ℕ} (hp : 1 ≤ p)
    (U : Fin n → Ω → Vector p) (hU : ∀ i, Measurable (U i)) (hind : iIndepFun U μ)
    {b v : ℝ} (hb : 0 < b) (hv : 0 ≤ v)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ∀ j, 0 ≤ U i ω j ∧ U i ω j ≤ b)
    (hbudget : ∀ j, (∑ i, ∫ ω, U i ω j ∂μ) ≤ v) :
    (∫ ω, ‖sumVector U ω‖ ∂μ) ≤
      b * Real.log (2 * (p : ℝ)) + (Real.exp 1 - 1) * v := by
  have hUi (i : Fin n) : Integrable (U i) μ := by
    apply (integrable_const b).mono' (hU i).aestronglyMeasurable
    filter_upwards [hbound i] with ω hω
    exact (pi_norm_le_iff_of_nonneg hb.le).mpr fun j => by
      rw [Real.norm_eq_abs, abs_of_nonneg (hω j).1]
      exact (hω j).2
  have hS : Measurable (sumVector U) := Finset.measurable_sum _ (fun i _ => hU i)
  have hSi : Integrable (fun ω => ‖sumVector U ω‖) μ :=
    (integrable_finset_sum _ (fun i _ => hUi i)).norm
  have hpos (j : Fin p) := independent_nonnegative_sum_mgf (fun i ω => U i ω j)
    (fun i => (measurable_pi_apply j).comp (hU i))
    (hind.comp (fun _ x => x j) (fun _ => measurable_pi_apply j)) hb
    (fun i => (hbound i).mono fun _ h => h j) (hbudget j)
  have hSnonneg (j : Fin p) : ∀ᵐ ω ∂μ, 0 ≤ sumVector U ω j := by
    filter_upwards [ae_all_iff.mpr hbound] with ω hω
    simpa only [sumVector, Finset.sum_apply] using
      (Finset.sum_nonneg fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) => (hω i j).1)
  have hneg (j : Fin p) : Integrable (fun ω => Real.exp (b⁻¹ * (-sumVector U ω j))) μ ∧
      mgf (fun ω => -sumVector U ω j) μ b⁻¹ ≤
        Real.exp (((Real.exp 1 - 1)/b) * v) := by
    have he := integrable_exp_mul_of_bounded_above
      (((measurable_pi_apply j).comp hS).neg) (inv_nonneg.mpr hb.le)
      ((hSnonneg j).mono fun _ h => neg_nonpos.mpr h)
    refine ⟨he, ?_⟩
    change (∫ ω, Real.exp (b⁻¹ * (-sumVector U ω j)) ∂μ) ≤ _
    have hle : (∫ ω, Real.exp (b⁻¹ * (-sumVector U ω j)) ∂μ) ≤ 1 := by
      apply (integral_mono_ae he (integrable_const (1 : ℝ)) ?_).trans_eq (by simp)
      filter_upwards [hSnonneg j] with ω hω
      exact Real.exp_le_one_iff.mpr (mul_nonpos_of_nonneg_of_nonpos
        (inv_nonneg.mpr hb.le) (neg_nonpos.mpr hω))
    exact hle.trans (Real.one_le_exp (mul_nonneg
      (div_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)]) hb.le) hv))
  have hm := expected_norm_le_log_signed_mgf hp (sumVector U) hS hSi (inv_pos.mpr hb)
    (fun j => ⟨by simpa only [sumVector, Finset.sum_apply] using (hpos j).1, (hneg j).1⟩)
    (fun j => ⟨by simpa only [sumVector, Finset.sum_apply] using (hpos j).2, (hneg j).2⟩)
  convert hm using 1 <;> field_simp <;> ring

/-- The actual fourth-coordinate budget of bounded independent increments.
The maximum is taken after summing the coordinate fourth powers. -/
theorem expected_coordinateFourthBudget_le {p n : ℕ} (hp : 1 ≤ p)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    {h Δ : ℝ} (hh : 0 < h) (hΔ : 0 ≤ Δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ h)
    (hbudget : ∀ j, (∑ i, ∫ ω, Y i ω j ^ 4 ∂μ) ≤ Δ) :
    (∫ ω, coordinateFourthBudget (fun i => Y i ω) ∂μ) ≤
      h^4 * Real.log (2 * (p : ℝ)) + (Real.exp 1 - 1) * Δ := by
  let U : Fin n → Ω → Vector p := fun i ω j => Y i ω j ^ 4
  have hU (i : Fin n) : Measurable (U i) :=
    measurable_pi_lambda _ fun j => ((measurable_pi_apply j).comp (hY i)).pow_const 4
  have hUi : iIndepFun U μ := hind.comp (fun _ x j => x j ^ 4)
    (fun _ => measurable_pi_lambda _ fun j => (measurable_pi_apply j).pow_const 4)
  have hUb (i : Fin n) : ∀ᵐ ω ∂μ, ∀ j, 0 ≤ U i ω j ∧ U i ω j ≤ h^4 := by
    filter_upwards [hbound i] with ω hω j
    refine ⟨by dsimp [U]; positivity, ?_⟩
    have hj : |Y i ω j| ≤ h := (norm_le_pi_norm (Y i ω) j).trans hω
    change Y i ω j ^ 4 ≤ h^4
    calc
      _ = |Y i ω j|^4 := by
        rw [pow_abs]
        exact (abs_of_nonneg (by positivity : 0 ≤ Y i ω j ^ 4)).symm
      _ ≤ _ := pow_le_pow_left₀ (abs_nonneg _) hj 4
  have hres := nonnegative_vector_expected_maximum hp U hU hUi (pow_pos hh 4) hΔ hUb hbudget
  convert hres using 1
  congr 1
  ext ω
  unfold coordinateFourthBudget
  congr 1
  ext j
  simp only [sumVector, Finset.sum_apply, U]

end
end RectangleCLT.Companion.SplitV4
