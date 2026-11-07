import RectangleCLTCompanion.SplitV4.CubeContraction
import RectangleCLTCompanion.SplitV4.PairedMoments
import RectangleCLTCompanion.SplitV4.CubeCopySelection
import Mathlib.MeasureTheory.Integral.Prod

/-! Genuine independent-copy symmetrization and the intrinsic conditional
variance budget for the bounded-sum proof in Appendix C. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem integrable_fst_probability {Ω Γ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (F : Ω → E) (hF : Integrable F μ) : Integrable (fun z : Ω × Γ => F z.1) (μ.prod ν) := by
  simpa only [one_smul, Function.comp_def, Prod.swap_prod_mk] using
    ((integrable_const (μ := ν) (1 : ℝ)).smul_prod hF).swap

theorem integrable_snd_probability {Ω Γ E : Type*}
    [MeasurableSpace Ω] [MeasurableSpace Γ] [NormedAddCommGroup E] [NormedSpace ℝ E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (F : Γ → E) (hF : Integrable F ν) : Integrable (fun z : Ω × Γ => F z.2) (μ.prod ν) := by
  simpa only [one_smul] using (integrable_const (μ := μ) (1 : ℝ)).smul_prod hF

/-- Jensen's inequality against a genuine independent copy. All moments
are actual Bochner integrals under the probability measures displayed. -/
theorem integral_norm_center_le_copy {Ω E : Type*} [MeasurableSpace Ω]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (F : Ω → E) (hF : Integrable F μ) :
    (∫ ω, ‖F ω - ∫ z, F z ∂μ‖ ∂μ) ≤
      ∫ z : Ω × Ω, ‖F z.1 - F z.2‖ ∂μ.prod μ := by
  have hd : Integrable (fun z : Ω × Ω => F z.1 - F z.2) (μ.prod μ) :=
    (integrable_fst_probability μ μ F hF).sub (integrable_snd_probability μ μ F hF)
  have hpoint (ω : Ω) : ‖F ω - ∫ z, F z ∂μ‖ ≤ ∫ z, ‖F ω - F z‖ ∂μ := by
    have hi : (∫ z, F ω - F z ∂μ) = F ω - ∫ z, F z ∂μ := by
      rw [integral_sub (integrable_const _) hF, integral_const]
      simp only [measureReal_univ_eq_one, one_smul]
    rw [← hi]
    exact norm_integral_le_integral_norm _
  calc
    _ ≤ ∫ ω, ∫ z, ‖F ω - F z‖ ∂μ ∂μ :=
      integral_mono ((hF.sub (integrable_const _)).norm) hd.norm.integral_prod_left hpoint
    _ = _ := (integral_prod _ hd.norm).symm

def coordinateSquare {p : ℕ} (x : Vector p) : Vector p := fun j => (x j) ^ 2

theorem measurable_coordinateSquare {p : ℕ} : Measurable (coordinateSquare (p := p)) :=
  measurable_pi_lambda _ (fun j => (measurable_pi_apply j).pow_const 2)

theorem norm_coordinateSquare_le {p : ℕ} (x : Vector p) :
    ‖coordinateSquare x‖ ≤ ‖x‖ ^ 2 := by
  apply (pi_norm_le_iff_of_nonneg (sq_nonneg ‖x‖)).mpr
  intro j
  have hj := norm_le_pi_norm x j
  simp only [Real.norm_eq_abs] at hj
  change |(x j) ^ 2| ≤ ‖x‖ ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (x j)) hj 2

theorem integrable_coordinateSquare_of_bound {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Ω → Vector p)
    (hY : Measurable Y) {η : ℝ} (_hη : 0 ≤ η) (hbound : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ η) :
    Integrable (fun ω => coordinateSquare (Y ω)) μ := by
  apply (integrable_const (η ^ 2)).mono' (measurable_coordinateSquare.comp hY).aestronglyMeasurable
  filter_upwards [hbound] with ω hω
  exact (norm_coordinateSquare_le _).trans (pow_le_pow_left₀ (norm_nonneg _) hω 2)

/-- The squared half-difference of genuine independent centered copies
has exactly half the original second moment. -/
theorem integral_half_copy_sq {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ)
    (hX : Integrable X μ) (hX₂ : Integrable (fun ω => (X ω) ^ 2) μ)
    (hcenter : (∫ ω, X ω ∂μ) = 0) :
    (∫ z : Ω × Ω, ((X z.1 - X z.2) / 2) ^ 2 ∂μ.prod μ) =
      (1 / 2 : ℝ) * ∫ ω, (X ω) ^ 2 ∂μ := by
  have hf := integrable_fst_probability μ μ (fun ω => (X ω) ^ 2) hX₂
  have hs := integrable_snd_probability μ μ (fun ω => (X ω) ^ 2) hX₂
  have hm := hX.mul_prod hX
  have he (z : Ω × Ω) : ((X z.1 - X z.2) / 2) ^ 2 =
      (1 / 4 : ℝ) * ((X z.1) ^ 2 + (X z.2) ^ 2 - 2 * (X z.1 * X z.2)) := by ring
  have hsub : (∫ z : Ω × Ω, (X z.1) ^ 2 + (X z.2) ^ 2 - 2 * (X z.1 * X z.2) ∂μ.prod μ) =
      (∫ z : Ω × Ω, (X z.1) ^ 2 + (X z.2) ^ 2 ∂μ.prod μ) -
        ∫ z : Ω × Ω, 2 * (X z.1 * X z.2) ∂μ.prod μ := by
    exact integral_sub (hf.add hs) (hm.const_mul 2)
  have hadd : (∫ z : Ω × Ω, (X z.1) ^ 2 + (X z.2) ^ 2 ∂μ.prod μ) =
      (∫ z : Ω × Ω, (X z.1) ^ 2 ∂μ.prod μ) +
        ∫ z : Ω × Ω, (X z.2) ^ 2 ∂μ.prod μ := integral_add hf hs
  simp_rw [he]
  rw [integral_const_mul, hsub, hadd, integral_const_mul]
  have hfst : (∫ z : Ω × Ω, (X z.1) ^ 2 ∂μ.prod μ) = ∫ ω, (X ω) ^ 2 ∂μ := by
    rw [integral_prod _ hf]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
  have hsnd : (∫ z : Ω × Ω, (X z.2) ^ 2 ∂μ.prod μ) = ∫ ω, (X ω) ^ 2 ∂μ := by
    rw [integral_prod _ hs]
    simp only [integral_const, measureReal_univ_eq_one, one_smul]
  have hmul : (∫ z : Ω × Ω, X z.1 * X z.2 ∂μ.prod μ) = 0 := by
    rw [integral_prod _ hm]
    simp only [integral_const_mul, hcenter, mul_zero, integral_zero]
  rw [hfst, hsnd, hmul]
  ring

def cubeSignedVectorSum {p n : ℕ} (Y : Fin n → Vector p) (x : Kane.Cube n) : Vector p :=
  ∑ i, cubeSign x i • Y i

theorem norm_cubeSign_smul {p n : ℕ} (x : Kane.Cube n) (i : Fin n) (y : Vector p) :
    ‖cubeSign x i • y‖ = ‖y‖ := by
  cases hx : x i <;> simp [cubeSign, hx]

theorem norm_cubeSignedVectorSum_le {p n : ℕ} (Y : Fin n → Vector p) (x : Kane.Cube n) :
    ‖cubeSignedVectorSum Y x‖ ≤ ∑ i, ‖Y i‖ := by
  exact (norm_sum_le _ _).trans_eq (Finset.sum_congr rfl (fun i _ => norm_cubeSign_smul x i _))

theorem measurable_cubeSignedVectorSum {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) :
    Measurable (fun z : Ω × Kane.Cube n => cubeSignedVectorSum (fun i => Y i z.1) z.2) := by
  apply Finset.measurable_sum
  intro i _
  exact ((measurable_of_finite (fun x : Kane.Cube n => cubeSign x i)).comp measurable_snd).smul
    ((hY i).comp measurable_fst)

theorem integrable_cubeSignedVectorSum {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → Vector p)
    (hY : ∀ i, Measurable (Y i)) (hYi : ∀ i, Integrable (Y i) μ) :
    Integrable (fun z : Ω × Kane.Cube n => cubeSignedVectorSum (fun i => Y i z.1) z.2)
      (μ.prod (cubeUniformLaw n)) := by
  have hi : Integrable (fun ω => ∑ i, ‖Y i ω‖) μ :=
    integrable_finset_sum _ (fun i _ => (hYi i).norm)
  apply (integrable_fst_probability μ (cubeUniformLaw n) _ hi).mono'
    (measurable_cubeSignedVectorSum Y hY).aestronglyMeasurable
  exact ae_of_all _ (fun z => norm_cubeSignedVectorSum_le _ _)

theorem integral_signed_copy_difference_le_twice {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → Vector p)
    (hYi : ∀ i, Integrable (Y i) μ) (x : Kane.Cube n) :
    (∫ z : Ω × Ω, ‖cubeSignedVectorSum (fun i => Y i z.1 - Y i z.2) x‖ ∂μ.prod μ) ≤
      2 * ∫ ω, ‖cubeSignedVectorSum (fun i => Y i ω) x‖ ∂μ := by
  have hS : Integrable (fun ω => cubeSignedVectorSum (fun i => Y i ω) x) μ :=
    integrable_finset_sum _ (fun i _ => by
      simpa only [Pi.smul_apply] using (hYi i).smul (cubeSign x i))
  have hf := integrable_fst_probability μ μ _ hS
  have hs := integrable_snd_probability μ μ _ hS
  have he (z : Ω × Ω) : cubeSignedVectorSum (fun i => Y i z.1 - Y i z.2) x =
      cubeSignedVectorSum (fun i => Y i z.1) x - cubeSignedVectorSum (fun i => Y i z.2) x := by
    simp only [cubeSignedVectorSum, smul_sub, Finset.sum_sub_distrib]
  simp_rw [he]
  calc
    _ ≤ ∫ z : Ω × Ω, (‖cubeSignedVectorSum (fun i => Y i z.1) x‖ +
        ‖cubeSignedVectorSum (fun i => Y i z.2) x‖) ∂μ.prod μ :=
      integral_mono (hf.sub hs).norm (hf.norm.add hs.norm) (fun z => norm_sub_le _ _)
    _ = _ := by
      rw [integral_add hf.norm hs.norm, integral_prod _ hf.norm, integral_prod _ hs.norm]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      ring

/-- Actual Rademacher symmetrization of independent vector summands. -/
theorem independent_sum_norm_symmetrization {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Y : Fin n → Ω → Vector p)
    (hY : ∀ i, Measurable (Y i)) (hind : iIndepFun Y μ)
    (hYi : ∀ i, Integrable (Y i) μ) :
    (∫ ω, ‖(∑ i, Y i ω) - ∫ z, ∑ i, Y i z ∂μ‖ ∂μ) ≤
      2 * ∫ z : Ω × Kane.Cube n, ‖cubeSignedVectorSum (fun i => Y i z.1) z.2‖
        ∂μ.prod (cubeUniformLaw n) := by
  have hS : Integrable (fun ω => ∑ i, Y i ω) μ := integrable_finset_sum _ (fun i _ => hYi i)
  have hf := integrable_fst_probability μ μ _ hS
  have hs := integrable_snd_probability μ μ _ hS
  have hdiff : Integrable (fun z : Ω × Ω => ‖∑ i, (Y i z.1 - Y i z.2)‖) (μ.prod μ) := by
    simpa only [Finset.sum_sub_distrib] using (hf.sub hs).norm
  have hF : Measurable (fun a : Fin n → Vector p => ‖∑ i, a i‖) :=
    measurable_cubeArraySum.norm
  obtain ⟨hcopy, heq⟩ := uniformCubeSignedDifference_test_transport μ Y hY hind
    (fun a => ‖∑ i, a i‖) hF hdiff
  have hsign := (integrable_cubeSignedVectorSum μ Y hY hYi).norm
  calc
    _ ≤ ∫ z : Ω × Ω, ‖(∑ i, Y i z.1) - ∑ i, Y i z.2‖ ∂μ.prod μ :=
      integral_norm_center_le_copy μ _ hS
    _ = ∫ z : Ω × Ω, ‖∑ i, (Y i z.1 - Y i z.2)‖ ∂μ.prod μ := by
      simp only [Finset.sum_sub_distrib]
    _ = ∫ x, ∫ z : Ω × Ω, ‖cubeSignedVectorSum (fun i => Y i z.1 - Y i z.2) x‖
        ∂μ.prod μ ∂cubeUniformLaw n := by
      exact heq.symm.trans (integral_prod_symm _ hcopy)
    _ ≤ ∫ x, 2 * ∫ ω, ‖cubeSignedVectorSum (fun i => Y i ω) x‖ ∂μ ∂cubeUniformLaw n := by
      apply integral_mono hcopy.integral_prod_right (hsign.integral_prod_right.const_mul 2)
      exact integral_signed_copy_difference_le_twice μ Y hYi
    _ = _ := by
      rw [integral_const_mul, ← integral_prod_symm _ hsign]

/-- The conditional row-square fluctuation is controlled by the same
Rademacher expected norm. This is the intrinsic `8η` budget in Appendix C,
proved from independence and the coefficient bound. -/
theorem independent_square_sum_fluctuation_le {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hind : iIndepFun Y μ) {η : ℝ} (hη : 0 ≤ η)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ η) :
    (∫ ω, ‖(∑ i, coordinateSquare (Y i ω)) -
      ∫ z, ∑ i, coordinateSquare (Y i z) ∂μ‖ ∂μ) ≤
      8 * η * ∫ z : Ω × Kane.Cube n, ‖cubeSignedVectorSum (fun i => Y i z.1) z.2‖
        ∂μ.prod (cubeUniformLaw n) := by
  have hYi (i : Fin n) : Integrable (Y i) μ :=
    (integrable_const η).mono' (hY i).aestronglyMeasurable (hbound i)
  let H : Fin n → Ω → Vector p := fun i ω => coordinateSquare (Y i ω)
  have hH (i : Fin n) : Measurable (H i) := measurable_coordinateSquare.comp (hY i)
  have hHi (i : Fin n) : Integrable (H i) μ :=
    integrable_coordinateSquare_of_bound μ _ (hY i) hη (hbound i)
  have hHind : iIndepFun H μ := hind.comp (fun _ => coordinateSquare) (fun _ => measurable_coordinateSquare)
  have hsignY := (integrable_cubeSignedVectorSum μ Y hY hYi).norm
  have hsignH := (integrable_cubeSignedVectorSum μ H hH hHi).norm
  have hc : (∫ z : Ω × Kane.Cube n, ‖cubeSignedVectorSum (fun i => H i z.1) z.2‖
      ∂μ.prod (cubeUniformLaw n)) ≤
      4 * η * ∫ z : Ω × Kane.Cube n, ‖cubeSignedVectorSum (fun i => Y i z.1) z.2‖
        ∂μ.prod (cubeUniformLaw n) := by
    rw [integral_prod _ hsignH, integral_prod _ hsignY, ← integral_const_mul]
    apply integral_mono_ae hsignH.integral_prod_left (hsignY.integral_prod_left.const_mul _)
    have hall : ∀ᵐ ω ∂μ, ∀ i, ‖Y i ω‖ ≤ η := ae_all_iff.mpr hbound
    filter_upwards [hall] with ω hω
    exact integral_cube_square_contraction_vector (fun i => Y i ω) η hη hω
  have hs := independent_sum_norm_symmetrization μ H hH hHind hHi
  change (∫ ω, ‖(∑ i, H i ω) - ∫ z, ∑ i, H i z ∂μ‖ ∂μ) ≤ _
  linarith

/-- The bad conditional-variance event is bounded using its actual
supremum-norm fluctuation, with no coordinate independence. -/
theorem probability_bad_rows_le_norm_fluctuation {Ω : Type*} [MeasurableSpace Ω]
    {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (Q : Ω → Vector p)
    (hQi : Integrable Q μ) (v : ℝ) (hv : 0 < v)
    (hmean : ∀ j, (∫ ω, Q ω ∂μ) j = v / 2) :
    μ.real {ω | ¬∀ j, v / 4 ≤ Q ω j} ≤
      (4 / v) * ∫ ω, ‖Q ω - ∫ z, Q z ∂μ‖ ∂μ := by
  have hsubset : {ω | ¬∀ j, v / 4 ≤ Q ω j} ⊆
      {ω | v / 4 ≤ ‖Q ω - ∫ z, Q z ∂μ‖} := by
    intro ω hω
    obtain ⟨j, hj⟩ := not_forall.mp hω
    have hj' : Q ω j < v / 4 := lt_of_not_ge hj
    have ha := norm_le_pi_norm (Q ω - ∫ z, Q z ∂μ) j
    simp only [Pi.sub_apply, hmean, Real.norm_eq_abs] at ha
    have hs : Q ω j - v / 2 ≤ 0 := by linarith
    rw [abs_of_nonpos hs] at ha
    change v / 4 ≤ _
    linarith
  have hmarkov := mul_meas_ge_le_integral_of_nonneg
    (μ := μ) (ae_of_all _ (fun ω => norm_nonneg (Q ω - ∫ z, Q z ∂μ)))
    ((hQi.sub (integrable_const _)).norm) (v / 4)
  have hb : (v / 4) * μ.real {ω | ¬∀ j, v / 4 ≤ Q ω j} ≤
      ∫ ω, ‖Q ω - ∫ z, Q z ∂μ‖ ∂μ :=
    (mul_le_mul_of_nonneg_left (measureReal_mono hsubset) (by positivity)).trans hmarkov
  have hd : μ.real {ω | ¬∀ j, v / 4 ≤ Q ω j} ≤
      (4 * ∫ ω, ‖Q ω - ∫ z, Q z ∂μ‖ ∂μ) / v := by
    apply (le_div_iff₀ hv).mpr
    nlinarith [hb]
  convert hd using 1
  ring

theorem measurable_cubePairDifference {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) :
    Measurable (fun z : Ω × Ω => cubePairDifference ξ z i) :=
  ((hξ i |>.comp measurable_fst).sub (hξ i |>.comp measurable_snd)).const_smul (1 / 2 : ℝ)

theorem cubePairDifference_bound {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {η : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (i : Fin n) :
    ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖cubePairDifference ξ z i‖ ≤ η := by
  have hm := measurable_cubePairDifference ξ h.measurable i
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hm.norm measurable_const)).mpr
  filter_upwards [h.bounded i] with ω hω
  filter_upwards [h.bounded i] with ω' hω'
  change ‖(1 / 2 : ℝ) • (ξ i ω - ξ i ω')‖ ≤ η
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have := norm_sub_le (ξ i ω) (ξ i ω')
  linarith

def cubeConditionalRowSquares {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (z : Ω × Ω) : Vector p :=
  ∑ i, coordinateSquare (cubePairDifference ξ z i)

theorem measurable_cubeConditionalRowSquares {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) :
    Measurable (cubeConditionalRowSquares ξ) :=
  Finset.measurable_sum _ (fun i _ => measurable_coordinateSquare.comp (measurable_cubePairDifference ξ hξ i))

theorem integrable_cubeConditionalRowSquares {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {η : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) :
    Integrable (cubeConditionalRowSquares ξ) (μ.prod μ) := by
  apply integrable_finset_sum
  intro i _
  exact integrable_coordinateSquare_of_bound (μ.prod μ) _ (measurable_cubePairDifference ξ h.measurable i)
    h.delta_nonneg (cubePairDifference_bound μ ξ h i)

/-- The conditional squared rows have the exact genuine mean `v/2`. -/
theorem integral_cubeConditionalRowSquares_coordinate {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (j : Fin p) :
    (∫ z, cubeConditionalRowSquares ξ z ∂μ.prod μ) j = v / 2 := by
  have hcoord (i : Fin n) (k : Fin p) : ∀ᵐ ω ∂μ, |ξ i ω k| ≤ η := by
    filter_upwards [h.bounded i] with ω hω
    exact (norm_le_pi_norm (ξ i ω) k).trans hω
  have hΔcoord (i : Fin n) (k : Fin p) :
      ∀ᵐ z : Ω × Ω ∂μ.prod μ, |cubePairDifference ξ z i k| ≤ η := by
    filter_upwards [cubePairDifference_bound μ ξ h i] with z hz
    exact (norm_le_pi_norm (cubePairDifference ξ z i) k).trans hz
  have hi := integrable_cubeConditionalRowSquares μ ξ h
  have he := (ContinuousLinearMap.proj j : Vector p →L[ℝ] ℝ).integral_comp_comm hi
  change (∫ z, cubeConditionalRowSquares ξ z j ∂μ.prod μ) =
    (∫ z, cubeConditionalRowSquares ξ z ∂μ.prod μ) j at he
  rw [← he]
  simp only [cubeConditionalRowSquares, coordinateSquare, Finset.sum_apply]
  rw [integral_finset_sum Finset.univ (fun i _ =>
    integrable_coordinate_pow_of_bounded (fun i => measurable_cubePairDifference ξ h.measurable i)
      hΔcoord i j 2)]
  have hmoment (i : Fin n) : (∫ z : Ω × Ω, (cubePairDifference ξ z i j) ^ 2 ∂μ.prod μ) =
      (1 / 2 : ℝ) * ∫ ω, (ξ i ω j) ^ 2 ∂μ := by
    have hXi : Integrable (fun ω => ξ i ω j) μ := by
      simpa only [pow_one] using integrable_coordinate_pow_of_bounded h.measurable hcoord i j 1
    simpa only [cubePairDifference, Pi.smul_apply, Pi.sub_apply, smul_eq_mul,
      div_eq_mul_inv, one_div, mul_comm, one_mul] using
      integral_half_copy_sq μ (fun ω => ξ i ω j) hXi
        (integrable_coordinate_pow_of_bounded h.measurable hcoord i j 2) (h.centered i j)
  simp_rw [hmoment]
  rw [← Finset.mul_sum,
    coordinate_second_moments_eq_covariance_of_bounded μ ξ h.measurable h.independent hcoord h.centered j,
    hdiag j]
  ring

def cubePairIntrinsicBudget {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : ℝ :=
  ∫ z : (Ω × Ω) × Kane.Cube n,
    ‖cubeSignedVectorSum (cubePairDifference ξ z.1) z.2‖ ∂(μ.prod μ).prod (cubeUniformLaw n)

theorem cubePairIntrinsicBudget_nonneg {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : 0 ≤ cubePairIntrinsicBudget μ ξ :=
  integral_nonneg (fun _ => norm_nonneg _)

theorem iIndepFun_cubePairDifference {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ) :
    iIndepFun (fun i z => cubePairDifference ξ z i) (μ.prod μ) :=
  (iIndepFun_pairedArray μ ξ hξ hind).comp (fun _ z => (1 / 2 : ℝ) • (z.1 - z.2))
    (fun _ => (measurable_fst.sub measurable_snd).const_smul (1 / 2 : ℝ))

/-- The Rademacher conditional norm reduces to the genuine half-copy
norm, by joint sign-swap invariance of independent observations. -/
theorem cubePairIntrinsicBudget_eq_half_copy {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hξi : ∀ i, Integrable (ξ i) μ) :
    cubePairIntrinsicBudget μ ξ =
      (1 / 2 : ℝ) * ∫ z : Ω × Ω, ‖(∑ i, ξ i z.1) - ∑ i, ξ i z.2‖ ∂μ.prod μ := by
  have hS : Integrable (fun ω => ∑ i, ξ i ω) μ := integrable_finset_sum _ (fun i _ => hξi i)
  have hd : Integrable (fun z : Ω × Ω => ∑ i, (ξ i z.1 - ξ i z.2)) (μ.prod μ) := by
    simpa only [Finset.sum_sub_distrib] using
      (integrable_fst_probability μ μ _ hS).sub (integrable_snd_probability μ μ _ hS)
  have hFi : Integrable (fun z : Ω × Ω => ‖(1 / 2 : ℝ) • ∑ i, (ξ i z.1 - ξ i z.2)‖)
      (μ.prod μ) := by
    simpa only [Pi.smul_apply] using (hd.smul (1 / 2 : ℝ)).norm
  obtain ⟨_, heq⟩ := uniformCubeSignedDifference_test_transport μ ξ hξ hind
    (fun a => ‖(1 / 2 : ℝ) • ∑ i, a i‖) (measurable_cubeArraySum.const_smul (1 / 2 : ℝ)).norm hFi
  have hp (z : (Ω × Ω) × Kane.Cube n) :
      cubeSignedVectorSum (cubePairDifference ξ z.1) z.2 =
        (1 / 2 : ℝ) • ∑ i, cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2) := by
    simp only [cubeSignedVectorSum, cubePairDifference, Finset.smul_sum]
    apply Finset.sum_congr rfl
    intro i _
    exact smul_comm _ _ _
  calc
    _ = ∫ z : (Ω × Ω) × Kane.Cube n,
        ‖(1 / 2 : ℝ) • ∑ i, cubeSign z.2 i • (ξ i z.1.1 - ξ i z.1.2)‖
          ∂(μ.prod μ).prod (cubeUniformLaw n) := integral_congr_ae (ae_of_all _ (fun z => congrArg norm (hp z)))
    _ = _ := heq
    _ = _ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2),
        Finset.sum_sub_distrib, integral_const_mul]

theorem cubePairIntrinsicBudget_le_norm_sum {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (hind : iIndepFun ξ μ)
    (hξi : ∀ i, Integrable (ξ i) μ) :
    cubePairIntrinsicBudget μ ξ ≤ ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := by
  rw [cubePairIntrinsicBudget_eq_half_copy μ ξ hξ hind hξi]
  have hS : Integrable (fun ω => ∑ i, ξ i ω) μ := integrable_finset_sum _ (fun i _ => hξi i)
  have hf := integrable_fst_probability μ μ _ hS
  have hs := integrable_snd_probability μ μ _ hS
  have hbound : (∫ z : Ω × Ω, ‖(∑ i, ξ i z.1) - ∑ i, ξ i z.2‖ ∂μ.prod μ) ≤
      2 * ∫ ω, ‖∑ i, ξ i ω‖ ∂μ := by
    calc
      _ ≤ ∫ z : Ω × Ω, (‖∑ i, ξ i z.1‖ + ‖∑ i, ξ i z.2‖) ∂μ.prod μ :=
        integral_mono (hf.sub hs).norm (hf.norm.add hs.norm) (fun z => norm_sub_le _ _)
      _ = _ := by
        rw [integral_add hf.norm hs.norm, integral_prod _ hf.norm, integral_prod _ hs.norm]
        simp only [integral_const, measureReal_univ_eq_one, one_smul]
        ring
  linarith

/-- The manuscript's exceptional conditional-variance probability, with
the intrinsic paired expected norm retained. -/
theorem cube_pair_bad_variance_probability_le {Ω : Type*} [MeasurableSpace Ω]
    {p n : ℕ} [NeZero p] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) :
    (μ.prod μ).real {z | ¬∀ j, v / 4 ≤ cubeConditionalRowSquares ξ z j} ≤
      (32 * η / v) * cubePairIntrinsicBudget μ ξ := by
  have hfluc := independent_square_sum_fluctuation_le (μ.prod μ)
    (fun i z => cubePairDifference ξ z i) (measurable_cubePairDifference ξ h.measurable)
    (iIndepFun_cubePairDifference μ ξ h.measurable h.independent)
    h.delta_nonneg (cubePairDifference_bound μ ξ h)
  have hbad := probability_bad_rows_le_norm_fluctuation (μ.prod μ) (cubeConditionalRowSquares ξ)
    (integrable_cubeConditionalRowSquares μ ξ h) v hv
    (integral_cubeConditionalRowSquares_coordinate μ ξ h hdiag)
  have hpos : 0 ≤ 4 / v := by positivity
  calc
    _ ≤ _ := hbad
    _ ≤ (4 / v) * (8 * η * cubePairIntrinsicBudget μ ξ) :=
      mul_le_mul_of_nonneg_left hfluc hpos
    _ = _ := by ring

end

end RectangleCLT.Companion.SplitV4
