import RectangleCLTCompanion.SplitV4.LocalizedShiftComparison

/-! A localized signed-shift comparison for actual scalar distribution
functions. Only the separate pairs `A,U` and `G,V` are independent. Local
CDF approximation and local Gaussian curvature suffice; large signed
shifts are paid for by their genuine second moments. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

def localRealCDFDistance {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (A : Ω → ℝ) (ν : Measure Γ) (G : Γ → ℝ) (t r : ℝ) : ℝ :=
  sSup (Set.range (fun x : {x : ℝ // |x - t| ≤ r} => |realCDF μ A x - realCDF ν G x|))

theorem realCDF_difference_le_one
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (G : Γ → ℝ) (x : ℝ) :
    |realCDF μ A x - realCDF ν G x| ≤ 1 := by
  apply abs_le.mpr
  have hA0 := realCDF_nonneg μ A x
  have hA1 := realCDF_le_one μ A x
  have hG0 := realCDF_nonneg ν G x
  have hG1 := realCDF_le_one ν G x
  constructor <;> linarith

theorem localRealCDFDistance_le_iff
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (G : Γ → ℝ)
    (t r ε : ℝ) (hr : 0 ≤ r) :
    localRealCDFDistance μ A ν G t r ≤ ε ↔
      ∀ x, |x - t| ≤ r → |realCDF μ A x - realCDF ν G x| ≤ ε := by
  have hb : BddAbove (Set.range (fun x : {x : ℝ // |x - t| ≤ r} =>
      |realCDF μ A x - realCDF ν G x|)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨x, rfl⟩
    exact realCDF_difference_le_one μ A ν G x
  have hmem : |t - t| ≤ r := by simpa using hr
  have hne : (Set.range (fun x : {x : ℝ // |x - t| ≤ r} =>
      |realCDF μ A x - realCDF ν G x|)).Nonempty :=
    ⟨_, ⟨⟨t, hmem⟩, rfl⟩⟩
  constructor
  · intro h x hx
    exact (le_csSup hb (Set.mem_range_self (⟨x, hx⟩ : {x : ℝ // |x - t| ≤ r}))).trans h
  · intro h
    apply csSup_le hne
    rintro y ⟨x, rfl⟩
    exact h x x.property

def localShiftComparisonCost (B r d : ℝ) : ℝ := B / 2 + 2 / r ^ 2 + |d| / r

/-- A local CDF error extends to an arbitrary signed shift with the
pointwise second-moment penalty `y²/r²`. No tail probability is assumed. -/
theorem local_cdf_shift_pointwise_bound
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (G : Γ → ℝ)
    {t r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hCDF : ∀ x, |x - t| ≤ r → |realCDF μ A x - realCDF ν G x| ≤ ε) (y : ℝ) :
    |realCDF μ A (t - y) - realCDF ν G (t - y)| ≤ ε + y ^ 2 / r ^ 2 := by
  by_cases hy : |y| ≤ r
  · have hx : |(t - y) - t| ≤ r := by simpa only [sub_sub_cancel_left, abs_neg] using hy
    exact (hCDF _ hx).trans (le_add_of_nonneg_right (div_nonneg (sq_nonneg _) (sq_nonneg _)))
  · have hsq : r ^ 2 ≤ y ^ 2 := by
      have hh := pow_le_pow_left₀ hr.le (le_of_not_ge hy) 2
      simpa only [sq_abs] using hh
    have h1 : 1 ≤ y ^ 2 / r ^ 2 := (le_div_iff₀ (sq_pos_of_pos hr)).mpr (by simpa using hsq)
    exact (realCDF_difference_le_one μ A ν G _).trans (h1.trans (le_add_of_nonneg_left hε))

theorem local_shift_convolution_error_bound
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G : Γ → ℝ) (hA : Measurable A) (hU : Measurable U)
    (hind : IndepFun A U μ) (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    {t r ε : ℝ} (hr : 0 < r) (hε : 0 ≤ ε)
    (hCDF : ∀ x, |x - t| ≤ r → |realCDF μ A x - realCDF ν G x| ≤ ε) :
    |μ.real {ω | A ω + U ω ≤ t} - ∫ ω, realCDF ν G (t - U ω) ∂μ| ≤
      ε + (∫ ω, U ω ^ 2 ∂μ) / r ^ 2 := by
  have hiA := integrable_realCDF_shift μ μ A U hU t
  have hiG := integrable_realCDF_shift μ ν G U hU t
  rw [independent_shift_cdf μ A U hA hU hind t, ← integral_sub hiA hiG]
  have hh := integral_mono_ae (hiA.sub hiG).abs
    ((integrable_const ε).add (hU2.div_const (r ^ 2)))
    (ae_of_all _ (fun ω => local_cdf_shift_pointwise_bound μ A ν G hr hε hCDF (U ω)))
  have he := integral_add (integrable_const ε) (hU2.div_const (r ^ 2))
  simp only [Pi.add_apply, integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul,
    integral_div] at he
  exact abs_integral_le_integral_abs.trans (hh.trans_eq he)

/-- Genuine expectation Taylor error under local curvature. The CDF's
bounded range pays for shifts leaving the tested threshold window. -/
theorem expected_cdf_shift_taylor_error_local
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (G : Γ → ℝ) (hF : ContDiff ℝ 2 (realCDF ν G))
    {B r t : ℝ} (hB0 : 0 ≤ B) (hr : 0 < r)
    (hB : ∀ x, |x - t| ≤ r → |deriv (deriv (realCDF ν G)) x| ≤ B)
    (U : Ω → ℝ) (hU : Measurable U) (hU2 : Integrable (fun ω => U ω ^ 2) μ) :
    |(∫ ω, realCDF ν G (t - U ω) ∂μ) - realCDF ν G t +
      deriv (realCDF ν G) t * (∫ ω, U ω ∂μ)| ≤
      localShiftTaylorCost B r (deriv (realCDF ν G) t) * ∫ ω, U ω ^ 2 ∂μ := by
  have hiF := integrable_realCDF_shift μ ν G U hU t
  have hiU := integrable_shift_of_second_moment μ U hU hU2
  have hi₀ : Integrable (fun ω => realCDF ν G (t - U ω) - realCDF ν G t) μ :=
    hiF.sub (integrable_const _)
  have hiR : Integrable (fun ω => realCDF ν G (t - U ω) - realCDF ν G t +
      deriv (realCDF ν G) t * U ω) μ := hi₀.add (hiU.const_mul _)
  have he : (∫ ω, realCDF ν G (t - U ω) - realCDF ν G t +
      deriv (realCDF ν G) t * U ω ∂μ) =
      (∫ ω, realCDF ν G (t - U ω) ∂μ) - realCDF ν G t +
        deriv (realCDF ν G) t * ∫ ω, U ω ∂μ := by
    rw [integral_add hi₀ (hiU.const_mul _), integral_sub hiF (integrable_const _), integral_const_mul]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  rw [← he]
  calc
    _ ≤ ∫ ω, |realCDF ν G (t - U ω) - realCDF ν G t +
        deriv (realCDF ν G) t * U ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, localShiftTaylorCost B r (deriv (realCDF ν G) t) * U ω ^ 2 ∂μ :=
      integral_mono_ae hiR.abs (hU2.const_mul _)
        (ae_of_all _ (fun ω => shifted_taylor_bound_local_global (realCDF ν G) hF hB0 hr
          (realCDF_nonneg ν G) (realCDF_le_one ν G) hB (U ω)))
    _ = _ := integral_const_mul _ _

/-- Local signed-shift comparison with exactly the independent pairs of
F.2 and genuine second moments. The error and curvature are needed only
on the window `|x-t|≤r`; the tails cost `second moment / r²`. -/
theorem independent_local_shift_comparison
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G V : Γ → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hG : Measurable G) (hV : Measurable V)
    (hAU : IndepFun A U μ) (hGV : IndepFun G V ν)
    (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) ν)
    (hF : ContDiff ℝ 2 (realCDF ν G)) {B ε r t : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 ≤ ε) (hr : 0 < r)
    (hB : ∀ x, |x - t| ≤ r → |deriv (deriv (realCDF ν G)) x| ≤ B)
    (hCDF : ∀ x, |x - t| ≤ r → |realCDF μ A x - realCDF ν G x| ≤ ε) :
    |μ.real {ω | A ω + U ω ≤ t} - ν.real {ω | G ω + V ω ≤ t} -
      deriv (realCDF ν G) t * ((∫ ω, V ω ∂ν) - ∫ ω, U ω ∂μ)| ≤
      ε + localShiftComparisonCost B r (deriv (realCDF ν G) t) *
        ((∫ ω, U ω ^ 2 ∂μ) + ∫ ω, V ω ^ 2 ∂ν) := by
  have happrox := local_shift_convolution_error_bound μ ν A U G hA hU hAU hU2 hr hε hCDF
  have hTaylorU := expected_cdf_shift_taylor_error_local μ ν G hF hB0 hr hB U hU hU2
  have hTaylorV := expected_cdf_shift_taylor_error_local ν ν G hF hB0 hr hB V hV hV2
  rw [independent_shift_cdf ν G V hG hV hGV t]
  let Iu := ∫ ω, realCDF ν G (t - U ω) ∂μ
  let Iv := ∫ ω, realCDF ν G (t - V ω) ∂ν
  let Ru := Iu - realCDF ν G t + deriv (realCDF ν G) t * ∫ ω, U ω ∂μ
  let Rv := Iv - realCDF ν G t + deriv (realCDF ν G) t * ∫ ω, V ω ∂ν
  have hraw : |μ.real {ω | A ω + U ω ≤ t} - Iv -
      deriv (realCDF ν G) t * ((∫ ω, V ω ∂ν) - ∫ ω, U ω ∂μ)| ≤
      ε + (∫ ω, U ω ^ 2 ∂μ) / r ^ 2 +
        localShiftTaylorCost B r (deriv (realCDF ν G) t) * (∫ ω, U ω ^ 2 ∂μ) +
        localShiftTaylorCost B r (deriv (realCDF ν G) t) * (∫ ω, V ω ^ 2 ∂ν) := by
    calc
      _ = |(μ.real {ω | A ω + U ω ≤ t} - Iu) + Ru - Rv| := by
        congr 1
        dsimp only [Ru, Rv]
        ring
      _ ≤ |μ.real {ω | A ω + U ω ≤ t} - Iu| + |Ru| + |Rv| :=
        (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
      _ ≤ _ := add_le_add (add_le_add happrox hTaylorU) hTaylorV
  have hp : 0 ≤ (∫ ω, V ω ^ 2 ∂ν) / r ^ 2 :=
    div_nonneg (integral_nonneg (fun _ => sq_nonneg _)) (sq_nonneg _)
  exact hraw.trans (by
    unfold localShiftComparisonCost localShiftTaylorCost
    simp only [div_eq_mul_inv] at hp ⊢
    nlinarith)

theorem independent_local_shift_comparison_of_local_distance
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G V : Γ → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hG : Measurable G) (hV : Measurable V)
    (hAU : IndepFun A U μ) (hGV : IndepFun G V ν)
    (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) ν)
    (hF : ContDiff ℝ 2 (realCDF ν G)) {B ε r t : ℝ}
    (hB0 : 0 ≤ B) (hε : 0 ≤ ε) (hr : 0 < r)
    (hB : ∀ x, |x - t| ≤ r → |deriv (deriv (realCDF ν G)) x| ≤ B)
    (hCDF : localRealCDFDistance μ A ν G t r ≤ ε) :
    |μ.real {ω | A ω + U ω ≤ t} - ν.real {ω | G ω + V ω ≤ t} -
      deriv (realCDF ν G) t * ((∫ ω, V ω ∂ν) - ∫ ω, U ω ∂μ)| ≤
      ε + localShiftComparisonCost B r (deriv (realCDF ν G) t) *
        ((∫ ω, U ω ^ 2 ∂μ) + ∫ ω, V ω ^ 2 ∂ν) :=
  independent_local_shift_comparison μ ν A U G V hA hU hG hV hAU hGV hU2 hV2 hF hB0 hε hr hB
    ((localRealCDFDistance_le_iff μ A ν G t r ε hr.le).mp hCDF)

end
end RectangleCLT.Companion.SplitV4
