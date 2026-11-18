import RectangleCLTCompanion.SubexponentialBernstein

/-! The printed residual displacement in Appendix D.1. The exponential
moment and union bound are applied to residual sums at cutoff `4K log(en)`. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open scoped BigOperators
noncomputable section

theorem residual_tail_printed {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {K u s : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (hs : 0 ≤ s) :
    μ.real {ω | s < |clipResidual (K*u) (X ω)|} ≤ 2*Real.exp (-u-s/K) := by
  have hK := h.scale_pos
  have hsub : {ω | s < |clipResidual (K*u) (X ω)|} ⊆
      {ω | K*u+s ≤ |X ω|} := by
    intro ω hω
    dsimp only [Set.mem_setOf_eq] at hω ⊢
    rw [abs_clipResidual _ _ (mul_nonneg h.scale_pos.le hu)] at hω
    have hh : s < |X ω|-K*u := by
      by_contra hn
      exact (not_le_of_gt hω) (max_le hs (le_of_not_gt hn))
    linarith
  have ht := measure_ge_le_exp_mul_mgf (X := fun ω => |X ω|) (t := 1/K)
    (K*u+s) (by positivity) (by simpa only [one_div_mul_eq_div] using h.integrable_exp)
  simp only [mgf,one_div_mul_eq_div] at ht
  apply (measureReal_mono hsub).trans (ht.trans ?_)
  calc
    _ ≤ Real.exp (-(1/K)*(K*u+s))*2 :=
      mul_le_mul_of_nonneg_left h.integral_exp_le (Real.exp_nonneg _)
    _ = _ := by
      have he : -(1/K)*(K*u+s) = -u-s/K := by field_simp [hK.ne']; ring
      rw [he,mul_comm]

theorem clipResidual_pow_le_exp {K u : ℝ} (hK : 0 < K) (hu : 0 ≤ u)
    (k : ℕ) (hk : 1 ≤ k) (x : ℝ) :
    |clipResidual (K*u) x|^k ≤ (k.factorial:ℝ)*K^k*Real.exp (-u)*Real.exp (|x|/K) := by
  have hT : 0 ≤ K*u := mul_nonneg hK.le hu
  by_cases hx : |x| ≤ K*u
  · rw [clipResidual_eq_zero hx,abs_zero,zero_pow (by omega : k ≠ 0)]
    positivity
  · let r := |clipResidual (K*u) x|
    have hr : 0 ≤ r := abs_nonneg _
    have hre : r = |x|-K*u := abs_clipResidual_eq_sub hT (lt_of_not_ge hx)
    have hfac : (0:ℝ) < k.factorial := by exact_mod_cast Nat.factorial_pos k
    have hh := (div_le_iff₀ hfac).mp (Real.pow_div_factorial_le_exp (r/K) (by positivity) k)
    have hm := mul_le_mul_of_nonneg_right hh (pow_nonneg hK.le k)
    have he : Real.exp (r/K) = Real.exp (-u)*Real.exp (|x|/K) := by
      rw [hre,sub_div,mul_div_cancel_left₀ u hK.ne',Real.exp_sub,Real.exp_neg]
      ring
    have hp : (r/K)^k*K^k = r^k := by rw [←mul_pow,div_mul_cancel₀ _ hK.ne']
    rw [hp,he] at hm
    dsimp only [r] at hm
    nlinarith

theorem residual_power_moment_printed {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Ω → ℝ} {K u : ℝ}
    (h : ExponentialMomentBound μ X K) (hu : 0 ≤ u) (k : ℕ) (hk : 1 ≤ k) :
    Integrable (fun ω => |clipResidual (K*u) (X ω)|^k) μ ∧
      (∫ ω, |clipResidual (K*u) (X ω)|^k ∂μ) ≤ 2*(k.factorial:ℝ)*K^k*Real.exp (-u) := by
  have hK := h.scale_pos
  let C := (k.factorial:ℝ)*K^k*Real.exp (-u)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hm : Measurable (fun ω => |clipResidual (K*u) (X ω)|^k) :=
    (((clipResidual_continuous _).measurable.comp h.measurable).abs).pow_const k
  have hi : Integrable (fun ω => |clipResidual (K*u) (X ω)|^k) μ := by
    apply (h.integrable_exp.const_mul C).mono' hm.aestronglyMeasurable
    apply ae_of_all
    intro ω
    simpa only [Real.norm_eq_abs,abs_pow,abs_abs] using
      (clipResidual_pow_le_exp h.scale_pos hu k hk (X ω))
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ ω, C*Real.exp (|X ω|/K) ∂μ :=
      integral_mono hi (h.integrable_exp.const_mul C)
        (fun ω => clipResidual_pow_le_exp h.scale_pos hu k hk (X ω))
    _ = C*(∫ ω, Real.exp (|X ω|/K) ∂μ) := integral_const_mul _ _
    _ ≤ C*2 := mul_le_mul_of_nonneg_left h.integral_exp_le hC
    _ = _ := by dsimp [C]; ring

theorem subexponentialTailFactor_le_inv_four_mul {n : ℕ} (hn : 1 ≤ n) :
    subexponentialTailFactor n ≤ 1/(4*(n:ℝ)) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hnR
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have heq : Real.exp (dimensionLog n) = Real.exp 1 * (n:ℝ) :=
    Real.exp_log (mul_pos (Real.exp_pos _) hn0)
  have hb : 2*(n:ℝ) ≤ Real.exp (dimensionLog n) := by rw [heq]; nlinarith
  have hb2 : (2:ℝ) ≤ Real.exp (dimensionLog n) := by nlinarith
  have hden : 4*(n:ℝ) ≤ Real.exp (2*dimensionLog n) := by
    rw [show 2*dimensionLog n = dimensionLog n+dimensionLog n by ring,Real.exp_add]
    nlinarith [mul_le_mul hb hb2 (by norm_num : (0:ℝ) ≤ 2) (Real.exp_nonneg (dimensionLog n))]
  unfold subexponentialTailFactor
  rw [show -2*dimensionLog n = -(2*dimensionLog n) by ring,Real.exp_neg]
  simpa only [one_div] using one_div_le_one_div_of_le (show 0 < 4*(n:ℝ) by positivity) hden

theorem four_n_tail_le_quarter {n : ℕ} (hn : 1 ≤ n) :
    4*(n:ℝ)*Real.exp (-(4*dimensionLog n)) ≤ 1/4 := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  let f := subexponentialTailFactor n
  have hf : 0 ≤ f := subexponentialTailFactor_nonneg n
  have hfbound : f ≤ 1/(4*(n:ℝ)) := subexponentialTailFactor_le_inv_four_mul hn
  have hmul : 4*(n:ℝ)*f ≤ 1 := by
    have hh := (le_div_iff₀ (by positivity : 0 < 4*(n:ℝ))).mp hfbound
    nlinarith
  have hquarter : f ≤ 1/4 := hfbound.trans
    (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 4) (by nlinarith))
  have hexp : Real.exp (-(4*dimensionLog n)) = f^2 := by
    dsimp [f,subexponentialTailFactor]
    rw [←Real.exp_nat_mul]
    congr 1
    ring
  rw [hexp]
  nlinarith [mul_le_mul_of_nonneg_right hmul hf]

theorem subexponentialUnionLog_le_two {n p : ℕ} (hn : 1 ≤ n) (hp : 1 ≤ p) :
    subexponentialUnionLog n p ≤ 2*dimensionLog n*dimensionLog p := by
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hp0 : (0:ℝ) < p := by exact_mod_cast hp
  have hln : 0 ≤ Real.log (n:ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  have hlp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp)
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1:ℝ)]
  have he2 : (4:ℝ) ≤ Real.exp 2 := by
    rw [show (2:ℝ) = 1+1 by norm_num,Real.exp_add]
    nlinarith
  have hfour : Real.log (4:ℝ) ≤ 2 := by
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 4) he2
    simpa only [Real.log_exp] using hh
  have heq : subexponentialUnionLog n p = Real.log (4:ℝ)+Real.log (n:ℝ)+Real.log (p:ℝ) := by
    rw [subexponentialUnionLog,Real.log_mul (mul_ne_zero (by norm_num) hn0.ne') hp0.ne',
      Real.log_mul (by norm_num) hn0.ne']
  rw [heq,dimensionLog_eq_one_add_log hn,dimensionLog_eq_one_add_log hp]
  nlinarith [mul_nonneg hln hlp]

def printedResidualRadius (n p : ℕ) (K : ℝ) : ℝ :=
    2*K*subexponentialUnionLog n p/Real.sqrt (n:ℝ)

theorem normalized_residual_tail_printed {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {n p : ℕ}
    {X : Fin n → Ω → Vector p} {K : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hn : 1 ≤ n) (hp : 1 ≤ p) :
    μ.real {ω | printedResidualRadius n p K <
      ‖sumVector (normalizedResidualRows μ X (K*(4*dimensionLog n))) ω‖} ≤ 1/(4*(n:ℝ)) := by
  have hnR : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hpR : (1:ℝ) ≤ p := by exact_mod_cast hp
  have hn0 : (0:ℝ) < n := zero_lt_one.trans_le hnR
  have hp0 : (0:ℝ) < p := zero_lt_one.trans_le hpR
  have hK : 0 ≤ K := zero_le_one.trans h.one_le_scale
  let s := subexponentialUnionLog n p
  have hslo : (3/4:ℝ) ≤ s := by
    have hnp := one_le_mul_of_one_le_of_one_le hnR hpR
    have hh := Real.log_le_log (by norm_num : (0:ℝ) < 4)
      (show (4:ℝ) ≤ 4*(n:ℝ)*(p:ℝ) by nlinarith)
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0:ℝ) < 4)
    norm_num at hl
    exact hl.trans hh
  have hu : 0 ≤ 4*dimensionLog n := mul_nonneg (by norm_num)
    (zero_le_one.trans (log_exp_mul_nat_ge_one hn))
  have hsmall := four_n_tail_le_quarter hn
  have hrad : K*(s+4*(n:ℝ)*Real.exp (-(4*dimensionLog n)))/Real.sqrt (n:ℝ) ≤
      printedResidualRadius n p K := by
    unfold printedResidualRadius
    apply div_le_div_of_nonneg_right _ (Real.sqrt_nonneg _)
    dsimp only [s]
    nlinarith [mul_le_mul_of_nonneg_left (show s+4*(n:ℝ)*Real.exp (-(4*dimensionLog n)) ≤ 2*s by linarith) hK]
  have ht := normalized_exp_residual_tail hn h hu (show 0 ≤ s by linarith)
  apply (measureReal_mono (show {ω | printedResidualRadius n p K <
      ‖sumVector (normalizedResidualRows μ X (K*(4*dimensionLog n))) ω‖} ⊆
      {ω | K*(s+4*(n:ℝ)*Real.exp (-(4*dimensionLog n)))/Real.sqrt (n:ℝ) <
      ‖sumVector (normalizedResidualRows μ X (K*(4*dimensionLog n))) ω‖} from
      fun _ hω => lt_of_le_of_lt hrad hω)).trans (ht.trans_eq ?_)
  dsimp [s,subexponentialUnionLog]
  rw [Real.exp_neg,Real.exp_log (by positivity)]
  field_simp [hn0.ne',hp0.ne']
  ring

theorem printedResidualRadius_le_archive {n p : ℕ} {K : ℝ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) (hK : 0 ≤ K) :
    printedResidualRadius n p K ≤ subexponentialResidualRadius n p K := by
  have hs := (subexponentialUnionLog_pos hn hp).le
  have hh : 0 ≤ K*subexponentialUnionLog n p/Real.sqrt (n:ℝ) := by positivity
  have ht : 0 ≤ 8*K*subexponentialTailFactor n*Real.sqrt (subexponentialUnionLog n p) := by
    unfold subexponentialTailFactor; positivity
  unfold printedResidualRadius subexponentialResidualRadius
  rw [show 2*K*subexponentialUnionLog n p/Real.sqrt (n:ℝ) =
    2*(K*subexponentialUnionLog n p/Real.sqrt (n:ℝ)) by ring]
  rw [show 4*K*subexponentialUnionLog n p/Real.sqrt (n:ℝ) =
    4*(K*subexponentialUnionLog n p/Real.sqrt (n:ℝ)) by ring]
  linarith

end
end RectangleCLTArxivV1
