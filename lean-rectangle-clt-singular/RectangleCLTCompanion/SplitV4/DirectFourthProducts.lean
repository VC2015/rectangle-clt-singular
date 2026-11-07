import RectangleCLTCompanion.SplitV4.DirectRelativeDerivatives

/-! Counting-index fourth-moment bounds for the direct initialization
remainder. Absolute coordinate products are summed only after their four
directions have been integrated; the bound has no summand-count factor. -/

open MeasureTheory
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem abs_four_product_le_fourth_average (a b c d : ℝ) :
    |a*b*c*d| ≤ (a^4+b^4+c^4+d^4)/4 := by
  have hab : |a*b|^2 = a^2*b^2 := by rw [sq_abs, mul_pow]
  have hcd : |c*d|^2 = c^2*d^2 := by rw [sq_abs, mul_pow]
  have hprod : |a*b*c*d| = |a*b| * |c*d| := by simp only [abs_mul]; ring
  rw [hprod]
  nlinarith only [sq_nonneg (a^2-b^2), sq_nonneg (c^2-d^2),
    sq_nonneg (|a*b|-|c*d|), hab, hcd]

theorem integrable_abs_four_product
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g k l : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hl : Measurable l)
    (hf4 : Integrable (fun ω => f ω^4) μ) (hg4 : Integrable (fun ω => g ω^4) μ)
    (hk4 : Integrable (fun ω => k ω^4) μ) (hl4 : Integrable (fun ω => l ω^4) μ) :
    Integrable (fun ω => |f ω*g ω*k ω*l ω|) μ := by
  apply ((((hf4.add hg4).add hk4).add hl4).div_const (4 : ℝ)).mono'
    (((hf.mul hg).mul hk).mul hl).abs.aestronglyMeasurable
  filter_upwards [] with ω
  simpa only [Real.norm_eq_abs, abs_abs, Pi.div_apply, Pi.add_apply] using
    abs_four_product_le_fourth_average (f ω) (g ω) (k ω) (l ω)

theorem integral_abs_four_product_le
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    (f g k l : Ω → ℝ) (hf : Measurable f) (hg : Measurable g)
    (hk : Measurable k) (hl : Measurable l)
    (hf4 : Integrable (fun ω => f ω^4) μ) (hg4 : Integrable (fun ω => g ω^4) μ)
    (hk4 : Integrable (fun ω => k ω^4) μ) (hl4 : Integrable (fun ω => l ω^4) μ) :
    (∫ ω, |f ω*g ω*k ω*l ω| ∂μ) ≤
      ((∫ ω, f ω^4 ∂μ)+(∫ ω, g ω^4 ∂μ)+(∫ ω, k ω^4 ∂μ)+(∫ ω, l ω^4 ∂μ))/4 := by
  have hmajor := (((hf4.add hg4).add hk4).add hl4).div_const (4 : ℝ)
  have hm := integral_mono_ae (integrable_abs_four_product μ f g k l hf hg hk hl hf4 hg4 hk4 hl4)
    hmajor (ae_of_all _ (fun ω => abs_four_product_le_fourth_average (f ω) (g ω) (k ω) (l ω)))
  apply hm.trans_eq
  have he₁ := integral_add ((hf4.add hg4).add hk4) hl4
  have he₂ := integral_add (hf4.add hg4) hk4
  have he₃ := integral_add hf4 hg4
  simp only [Pi.add_apply] at he₁ he₂ he₃
  rw [integral_div]
  simp only [Pi.add_apply]
  rw [he₁, he₂, he₃]

theorem sum_integral_abs_four_product_le_fourth_budget
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (μ : Measure Ω)
    (Y : Fin 4 → Fin n → Ω → ℝ) (hY : ∀ a i, Measurable (Y a i))
    (hY4 : ∀ a i, Integrable (fun ω => Y a i ω^4) μ) {D : ℝ}
    (hbudget : ∀ a, (∑ i, ∫ ω, Y a i ω^4 ∂μ) ≤ D) :
    (∑ i, ∫ ω, |Y 0 i ω*Y 1 i ω*Y 2 i ω*Y 3 i ω| ∂μ) ≤ D := by
  calc
    _ ≤ ∑ i, ((∫ ω, Y 0 i ω^4 ∂μ)+(∫ ω, Y 1 i ω^4 ∂μ)+
        (∫ ω, Y 2 i ω^4 ∂μ)+(∫ ω, Y 3 i ω^4 ∂μ))/4 := by
      apply Finset.sum_le_sum
      intro i _
      exact integral_abs_four_product_le μ _ _ _ _ (hY 0 i) (hY 1 i) (hY 2 i) (hY 3 i)
        (hY4 0 i) (hY4 1 i) (hY4 2 i) (hY4 3 i)
    _ = ((∑ i, ∫ ω, Y 0 i ω^4 ∂μ)+(∑ i, ∫ ω, Y 1 i ω^4 ∂μ)+
        (∑ i, ∫ ω, Y 2 i ω^4 ∂μ)+(∑ i, ∫ ω, Y 3 i ω^4 ∂μ))/4 := by
      simp only [div_eq_mul_inv, add_mul, Finset.sum_add_distrib, Finset.sum_mul]
    _ ≤ D := by linarith only [hbudget 0, hbudget 1, hbudget 2, hbudget 3]

theorem RelativeMomentBounds.sum_integral_coordinate_fourth_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (j : Fin p) :
    (∑ i, ∫ ω, ξ i ω j^4 ∂μ) ≤ s₄ := by
  have hh := h.fourth_upper j (Pi.single j 1)
  rw [matrixQuadratic_smul_eq] at hh
  simp only [matrixQuadratic, Pi.single_apply, ite_mul, mul_ite, one_mul, mul_one,
    zero_mul, mul_zero, Finset.sum_ite_eq, Finset.sum_ite_eq', Finset.mem_univ, if_true] at hh
  rw [hunit j, mul_one] at hh
  change (∑ i, ∫ ω, ξ i ω j^2*(ξ i ω j*ξ i ω j) ∂μ) ≤ s₄ at hh
  convert hh using 1
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [] with ω
  ring

theorem RelativeMomentBounds.integrable_coordinate_fourth
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄) (i : Fin n) (j : Fin p) :
    Integrable (fun ω => ξ i ω j^4) μ := by
  convert h.fourth_integrable i j j j using 1
  funext ω
  ring

theorem RelativeMomentBounds.sum_integral_abs_coordinate_four_product_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (a : Fin 4 → Fin p) :
    (∑ i, ∫ ω, |ξ i ω (a 0)*ξ i ω (a 1)*ξ i ω (a 2)*ξ i ω (a 3)| ∂μ) ≤ s₄ := by
  exact sum_integral_abs_four_product_le_fourth_budget μ (fun k i ω => ξ i ω (a k))
    (fun k i => (measurable_pi_apply (a k)).comp (h.measurable i))
    (fun k i => h.integrable_coordinate_fourth i (a k)) (fun k => h.sum_integral_coordinate_fourth_le hunit (a k))

/-- A coordinate can be selected from either of the two genuine independent
copies. Arbitrary repeated or mixed copy patterns are allowed. -/
def directCopyCoordinate {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (j : Fin p) (b : Bool) (z : Ω × Ω) : ℝ :=
  if b then ξ i z.2 j else ξ i z.1 j

theorem integral_directCopyCoordinate_fourth
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (j : Fin p) (b : Bool) :
    (∫ z : Ω × Ω, directCopyCoordinate ξ i j b z^4 ∂μ.prod μ) = ∫ ω, ξ i ω j^4 ∂μ := by
  cases b
  · simpa only [directCopyCoordinate, Bool.false_eq_true, if_false, measureReal_univ_eq_one, one_smul] using
      (integral_fun_fst (μ := μ) (ν := μ) (fun ω => ξ i ω j^4))
  · simpa only [directCopyCoordinate, if_true, measureReal_univ_eq_one, one_smul] using
      (integral_fun_snd (μ := μ) (ν := μ) (fun ω => ξ i ω j^4))

theorem RelativeMomentBounds.sum_integral_abs_copy_coordinate_four_product_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {s₃ s₄ : ℝ}
    (h : RelativeMomentBounds μ ξ s₃ s₄)
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (a : Fin 4 → Fin p) (b : Fin 4 → Bool) :
    (∑ i, ∫ z, |directCopyCoordinate ξ i (a 0) (b 0) z*
      directCopyCoordinate ξ i (a 1) (b 1) z*directCopyCoordinate ξ i (a 2) (b 2) z*
      directCopyCoordinate ξ i (a 3) (b 3) z| ∂μ.prod μ) ≤ s₄ := by
  apply sum_integral_abs_four_product_le_fourth_budget (μ.prod μ)
    (fun k i z => directCopyCoordinate ξ i (a k) (b k) z)
  · intro k i
    cases hb : b k <;> simp only [directCopyCoordinate, hb, Bool.false_eq_true, if_false, if_true]
    · exact ((measurable_pi_apply (a k)).comp (h.measurable i)).comp measurable_fst
    · exact ((measurable_pi_apply (a k)).comp (h.measurable i)).comp measurable_snd
  · intro k i
    cases hb : b k <;> simp only [directCopyCoordinate, hb, Bool.false_eq_true, if_false, if_true]
    · simpa only [mul_one] using (h.integrable_coordinate_fourth i (a k)).mul_prod
        (integrable_const (1 : ℝ))
    · simpa only [one_mul] using (integrable_const (1 : ℝ) : Integrable (fun _ : Ω => (1 : ℝ)) μ).mul_prod
        (h.integrable_coordinate_fourth i (a k))
  · intro k
    simp_rw [integral_directCopyCoordinate_fourth]
    exact h.sum_integral_coordinate_fourth_le hunit (a k)

end
end RectangleCLT.Companion.SplitV4
