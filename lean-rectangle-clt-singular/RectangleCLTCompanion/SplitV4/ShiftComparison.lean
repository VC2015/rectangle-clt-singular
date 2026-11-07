import RectangleCLT.TranslationTaylor
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Probability.Independence.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! Lemma F.2: comparison of independently shifted variables. The two
independence assumptions concern the separate pairs only. Shift laws may
have either sign and need not be centered. All moments are genuine Bochner
integrals under actual probability laws. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def realCDF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Ω → ℝ) (t : ℝ) : ℝ :=
  μ.real {ω | A ω ≤ t}

theorem realCDF_nonneg {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A : Ω → ℝ) (t : ℝ) :
    0 ≤ realCDF μ A t := measureReal_nonneg

theorem realCDF_le_one {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Ω → ℝ) (t : ℝ) : realCDF μ A t ≤ 1 := measureReal_le_one

theorem realCDF_monotone {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → ℝ) : Monotone (realCDF μ A) := by
  intro x y hxy
  exact measureReal_mono (fun ω hω => hω.trans hxy)

theorem measurable_realCDF {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (A : Ω → ℝ) : Measurable (realCDF μ A) := (realCDF_monotone μ A).measurable

theorem integrable_realCDF_shift
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (G : Γ → ℝ) (U : Ω → ℝ) (hU : Measurable U) (t : ℝ) :
    Integrable (fun ω => realCDF ν G (t - U ω)) μ := by
  apply (integrable_const (1 : ℝ)).mono'
    (((measurable_realCDF ν G).comp (measurable_const.sub hU)).aestronglyMeasurable)
  exact ae_of_all _ (fun ω => by
    change ‖realCDF ν G (t - U ω)‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (realCDF_nonneg ν G _)]
    exact realCDF_le_one ν G _)

theorem integrable_shift_of_second_moment
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (U : Ω → ℝ) (hU : Measurable U) (hU2 : Integrable (fun ω => U ω ^ 2) μ) : Integrable U μ := by
  apply ((integrable_const (1 : ℝ)).add hU2).mono' hU.aestronglyMeasurable
  apply ae_of_all
  intro ω
  rw [Real.norm_eq_abs]
  change |U ω| ≤ 1 + U ω ^ 2
  have ha := sq_abs (U ω)
  nlinarith [sq_nonneg (|U ω| - 1 / 2)]

/-- The exact scalar Taylor estimate used in F.2. The signed shift `y`
is unrestricted; the derivative bound is on the actual second derivative. -/
theorem shifted_taylor_bound (F : ℝ → ℝ) (hF : ContDiff ℝ 2 F) (B : ℝ)
    (hB : ∀ x, |deriv (deriv F) x| ≤ B) (t y : ℝ) :
    |F (t - y) - F t + deriv F t * y| ≤ (B / 2) * y ^ 2 := by
  have hF1 : ContDiff ℝ 1 (deriv F) := (contDiff_succ_iff_deriv.mp hF).2.2
  have hD := hF.differentiable (by norm_num)
  have hD1 := hF1.differentiable (by norm_num)
  let f : ℝ → ℝ := fun r => F (t - r * y)
  have hfc : ContDiff ℝ 2 f := hF.comp (contDiff_const.sub (contDiff_id.mul contDiff_const))
  have hd (r : ℝ) : HasDerivAt f (-y * deriv F (t - r * y)) r := by
    convert (hD (t - r * y)).hasDerivAt.comp r
      (((hasDerivAt_id r).mul_const y).const_sub t) using 1
    dsimp only [f]
    ring
  have hd1 (r : ℝ) : HasDerivAt (fun z => -y * deriv F (t - z * y))
      (y ^ 2 * deriv (deriv F) (t - r * y)) r := by
    convert ((hD1 (t - r * y)).hasDerivAt.comp r
      (((hasDerivAt_id r).mul_const y).const_sub t)).const_mul (-y) using 1
    ring
  have he1 : deriv f = fun r => -y * deriv F (t - r * y) := funext (fun r => (hd r).deriv)
  have he2 (r : ℝ) : iteratedDeriv 2 f r = y ^ 2 * deriv (deriv F) (t - r * y) := by
    simp only [iteratedDeriv_succ, iteratedDeriv_zero]
    rw [he1]
    exact (hd1 r).deriv
  obtain ⟨r, _, hrem⟩ := taylor1_mean_remainder hfc
  have heq : F (t - y) - F t + deriv F t * y =
      (y ^ 2 * deriv (deriv F) (t - r * y)) / 2 := by
    rw [he2, iteratedDeriv_one, he1] at hrem
    norm_num only [f, one_mul, zero_mul, sub_zero] at hrem
    linarith
  rw [heq, abs_div, abs_mul, abs_of_nonneg (sq_nonneg y),
    abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  calc
    _ ≤ (y ^ 2 * B) / 2 := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hB _) (sq_nonneg _)) (by norm_num)
    _ = _ := by ring

/-- Independence gives the actual shifted CDF as a convolution. The
observation and shift may be dependent on variables outside this pair. -/
theorem independent_shift_cdf
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A U : Ω → ℝ) (hA : Measurable A) (hU : Measurable U) (hind : IndepFun A U μ) (t : ℝ) :
    μ.real {ω | A ω + U ω ≤ t} = ∫ ω, realCDF μ A (t - U ω) ∂μ := by
  letI : IsProbabilityMeasure (μ.map A) := isProbabilityMeasure_map hA.aemeasurable
  letI : IsProbabilityMeasure (μ.map U) := isProbabilityMeasure_map hU.aemeasurable
  let L : Set (ℝ × ℝ) := {z | z.1 + z.2 ≤ t}
  let I : ℝ × ℝ → ℝ := L.indicator (fun _ => 1)
  have hL : MeasurableSet L := measurableSet_le (measurable_fst.add measurable_snd) measurable_const
  have hI : Measurable I := measurable_const.indicator hL
  have hi : Integrable I ((μ.map A).prod (μ.map U)) := (integrable_const (1 : ℝ)).indicator hL
  have hEV : MeasurableSet {ω | A ω + U ω ≤ t} := measurableSet_le (hA.add hU) measurable_const
  have hlaw := (indepFun_iff_map_prod_eq_prod_map_map hA.aemeasurable hU.aemeasurable).mp hind
  have hfixed (u : ℝ) : (∫ a, I (a, u) ∂μ.map A) = realCDF μ A (t - u) := by
    have heq : (fun a : ℝ => I (a, u)) = (Set.Iic (t - u)).indicator (fun _ => (1 : ℝ)) := by
      funext a
      simp only [I, L, Set.indicator, Set.mem_setOf_eq, Set.mem_Iic, le_sub_iff_add_le]
    rw [heq, integral_indicator_const (1 : ℝ) measurableSet_Iic, smul_eq_mul, mul_one]
    change ((μ.map A) (Set.Iic (t - u))).toReal = (μ {ω | A ω ≤ t - u}).toReal
    rw [Measure.map_apply hA measurableSet_Iic]
    rfl
  calc
    _ = ∫ ω, I (A ω, U ω) ∂μ := by
      change μ.real {ω | A ω + U ω ≤ t} =
        ∫ ω, {ω | A ω + U ω ≤ t}.indicator (fun _ => (1 : ℝ)) ω ∂μ
      rw [integral_indicator_const (1 : ℝ) hEV, smul_eq_mul, mul_one]
    _ = ∫ z, I z ∂μ.map (fun ω => (A ω, U ω)) :=
      (integral_map (hA.prodMk hU).aemeasurable hI.aestronglyMeasurable).symm
    _ = ∫ z, I z ∂(μ.map A).prod (μ.map U) := by rw [hlaw]
    _ = ∫ u, ∫ a, I (a, u) ∂μ.map A ∂μ.map U := integral_prod_symm _ hi
    _ = ∫ u, realCDF μ A (t - u) ∂μ.map U := integral_congr_ae (ae_of_all _ hfixed)
    _ = _ := integral_map hU.aemeasurable
      (((measurable_realCDF μ A).comp (measurable_const.sub measurable_id)).aestronglyMeasurable)

def realCDFDistance {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) (A : Ω → ℝ) (ν : Measure Γ) (G : Γ → ℝ) : ℝ :=
  sSup (Set.range (fun t => |realCDF μ A t - realCDF ν G t|))

theorem realCDFDistance_le_iff
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (A : Ω → ℝ)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (G : Γ → ℝ) (ε : ℝ) :
    realCDFDistance μ A ν G ≤ ε ↔ ∀ t, |realCDF μ A t - realCDF ν G t| ≤ ε := by
  have hb : BddAbove (Set.range (fun t => |realCDF μ A t - realCDF ν G t|)) := by
    refine ⟨1, ?_⟩
    rintro y ⟨t, rfl⟩
    apply abs_le.mpr
    have hA₀ := realCDF_nonneg μ A t
    have hA₁ := realCDF_le_one μ A t
    have hG₀ := realCDF_nonneg ν G t
    have hG₁ := realCDF_le_one ν G t
    constructor <;> linarith
  constructor
  · intro hs t
    exact (le_csSup hb (Set.mem_range_self t)).trans hs
  · intro h
    exact csSup_le (Set.range_nonempty _) (by rintro y ⟨t, rfl⟩; exact h t)

theorem expected_cdf_shift_taylor_error
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (G : Γ → ℝ) (hF : ContDiff ℝ 2 (realCDF ν G)) (B : ℝ)
    (hB : ∀ x, |deriv (deriv (realCDF ν G)) x| ≤ B)
    (U : Ω → ℝ) (hU : Measurable U) (hU2 : Integrable (fun ω => U ω ^ 2) μ) (t : ℝ) :
    |(∫ ω, realCDF ν G (t - U ω) ∂μ) - realCDF ν G t +
      deriv (realCDF ν G) t * (∫ ω, U ω ∂μ)| ≤ (B / 2) * ∫ ω, U ω ^ 2 ∂μ := by
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
    rw [integral_add hi₀ (hiU.const_mul _), integral_sub hiF (integrable_const _),
      integral_const_mul]
    simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul]
  rw [← he]
  calc
    _ ≤ ∫ ω, |realCDF ν G (t - U ω) - realCDF ν G t +
        deriv (realCDF ν G) t * U ω| ∂μ := abs_integral_le_integral_abs
    _ ≤ ∫ ω, (B / 2) * U ω ^ 2 ∂μ :=
      integral_mono_ae hiR.abs (hU2.const_mul _)
        (ae_of_all _ (fun ω => shifted_taylor_bound (realCDF ν G) hF B hB t (U ω)))
    _ = _ := integral_const_mul _ _

theorem shift_convolution_error_bound
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G : Γ → ℝ) (hA : Measurable A) (hU : Measurable U)
    (hind : IndepFun A U μ) {ε : ℝ}
    (hCDF : ∀ x, |realCDF μ A x - realCDF ν G x| ≤ ε) (t : ℝ) :
    |μ.real {ω | A ω + U ω ≤ t} - (∫ ω, realCDF ν G (t - U ω) ∂μ)| ≤ ε := by
  have hiA := integrable_realCDF_shift μ μ A U hU t
  have hiG := integrable_realCDF_shift μ ν G U hU t
  rw [independent_shift_cdf μ A U hA hU hind t, ← integral_sub hiA hiG]
  calc
    _ ≤ ∫ ω, |realCDF μ A (t - U ω) - realCDF ν G (t - U ω)| ∂μ :=
      abs_integral_le_integral_abs
    _ ≤ ∫ _ω : Ω, ε ∂μ :=
      integral_mono_ae (hiA.sub hiG).abs (integrable_const _)
        (ae_of_all _ (fun ω => hCDF (t - U ω)))
    _ = ε := by simp

/-- Lemma F.2 with any uniform bound on the actual second derivative. The
two independent pairs may live on different probability spaces; in
particular no four-way independence, centered shift, or sign restriction
on either shift occurs in the contract. -/
theorem independent_shift_comparison_of_second_derivative_bound
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G V : Γ → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hG : Measurable G) (hV : Measurable V)
    (hAU : IndepFun A U μ) (hGV : IndepFun G V ν)
    (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) ν)
    (hF : ContDiff ℝ 2 (realCDF ν G)) (B ε : ℝ) (_hε : 0 ≤ ε)
    (hB : ∀ x, |deriv (deriv (realCDF ν G)) x| ≤ B)
    (hCDF : realCDFDistance μ A ν G ≤ ε) (t : ℝ) :
    |μ.real {ω | A ω + U ω ≤ t} - ν.real {ω | G ω + V ω ≤ t} -
      deriv (realCDF ν G) t * ((∫ ω, V ω ∂ν) - ∫ ω, U ω ∂μ)| ≤
      ε + (B / 2) * ((∫ ω, U ω ^ 2 ∂μ) + ∫ ω, V ω ^ 2 ∂ν) := by
  have happrox := shift_convolution_error_bound μ ν A U G hA hU hAU
    ((realCDFDistance_le_iff μ A ν G ε).mp hCDF) t
  have hTaylorU := expected_cdf_shift_taylor_error μ ν G hF B hB U hU hU2 t
  have hTaylorV := expected_cdf_shift_taylor_error ν ν G hF B hB V hV hV2 t
  rw [independent_shift_cdf ν G V hG hV hGV t]
  let Iu := ∫ ω, realCDF ν G (t - U ω) ∂μ
  let Iv := ∫ ω, realCDF ν G (t - V ω) ∂ν
  let Ru := Iu - realCDF ν G t + deriv (realCDF ν G) t * ∫ ω, U ω ∂μ
  let Rv := Iv - realCDF ν G t + deriv (realCDF ν G) t * ∫ ω, V ω ∂ν
  calc
    _ = |(μ.real {ω | A ω + U ω ≤ t} - Iu) + Ru - Rv| := by
      congr 1
      dsimp only [Ru, Rv]
      ring
    _ ≤ |μ.real {ω | A ω + U ω ≤ t} - Iu| + |Ru| + |Rv| :=
      (abs_sub _ _).trans (add_le_add_right (abs_add _ _) _)
    _ ≤ ε + (B / 2) * (∫ ω, U ω ^ 2 ∂μ) + (B / 2) * (∫ ω, V ω ^ 2 ∂ν) :=
      add_le_add (add_le_add happrox hTaylorU) hTaylorV
    _ = _ := by ring

/-- The supremum norm of the actual second derivative. When the second derivative is bounded,
this is the usual least uniform bound `||F''||_infty`; its
least-upper-bound characterization below relates it to the universal-B API. -/
def secondDerivativeSupNorm (F : ℝ → ℝ) : ℝ :=
  sSup (Set.range (fun x => |deriv (deriv F) x|))

theorem secondDerivativeSupNorm_le_iff (F : ℝ → ℝ)
    (hbounded : BddAbove (Set.range (fun x => |deriv (deriv F) x|))) (B : ℝ) :
    secondDerivativeSupNorm F ≤ B ↔ ∀ x, |deriv (deriv F) x| ≤ B := by
  constructor
  · intro h x
    exact (le_csSup hbounded (Set.mem_range_self x)).trans h
  · intro h
    exact csSup_le (Set.range_nonempty _) (by rintro y ⟨x, rfl⟩; exact h x)

/-- The whole current Lemma F.2, with the actual CDF, actual independent
shift probabilities, and the least uniform second-derivative bound. -/
theorem independent_shift_comparison
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (A U : Ω → ℝ) (G V : Γ → ℝ)
    (hA : Measurable A) (hU : Measurable U) (hG : Measurable G) (hV : Measurable V)
    (hAU : IndepFun A U μ) (hGV : IndepFun G V ν)
    (hU2 : Integrable (fun ω => U ω ^ 2) μ)
    (hV2 : Integrable (fun ω => V ω ^ 2) ν)
    (hF : ContDiff ℝ 2 (realCDF ν G))
    (hbounded : BddAbove (Set.range (fun x => |deriv (deriv (realCDF ν G)) x|)))
    (ε : ℝ) (hε : 0 ≤ ε) (hCDF : realCDFDistance μ A ν G ≤ ε) (t : ℝ) :
    |μ.real {ω | A ω + U ω ≤ t} - ν.real {ω | G ω + V ω ≤ t} -
      deriv (realCDF ν G) t * ((∫ ω, V ω ∂ν) - ∫ ω, U ω ∂μ)| ≤
      ε + (1 / 2 : ℝ) * secondDerivativeSupNorm (realCDF ν G) *
        ((∫ ω, U ω ^ 2 ∂μ) + ∫ ω, V ω ^ 2 ∂ν) := by
  have hB : ∀ x, |deriv (deriv (realCDF ν G)) x| ≤ secondDerivativeSupNorm (realCDF ν G) :=
    (secondDerivativeSupNorm_le_iff (realCDF ν G) hbounded _).mp le_rfl
  have h := independent_shift_comparison_of_second_derivative_bound μ ν A U G V
    hA hU hG hV hAU hGV hU2 hV2 hF (secondDerivativeSupNorm (realCDF ν G)) ε hε hB hCDF t
  convert h using 1
  ring

end

end RectangleCLT.Companion.SplitV4
