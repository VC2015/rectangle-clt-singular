import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic

/-! Genuine scalar jets used in the all-order logistic derivative envelope. -/
open Filter
open scoped Topology BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def reciprocalOnePlus (t : ℝ) : ℝ := 1/(1+t)
def reciprocalOnePlusJet (k : ℕ) (t : ℝ) : ℝ :=
  (-1 : ℝ)^k*(k.factorial : ℝ)/(1+t)^(k+1)

theorem hasDerivAt_reciprocalOnePlusJet (k : ℕ) {t : ℝ} (ht : -1 < t) :
    HasDerivAt (reciprocalOnePlusJet k) (reciprocalOnePlusJet (k+1) t) t := by
  have hb : 1+t ≠ 0 := ne_of_gt (by linarith : 0 < 1+t)
  have hh := ((((hasDerivAt_const t (1 : ℝ)).add (hasDerivAt_id t)).pow (k+1)).inv
    (pow_ne_zero _ hb)).const_mul ((-1 : ℝ)^k*(k.factorial : ℝ))
  convert hh using 1
  dsimp [reciprocalOnePlusJet]
  simp only [Nat.add_sub_cancel, Nat.factorial_succ, Nat.cast_mul, Nat.cast_add, Nat.cast_one, pow_succ]
  field_simp
  ring

theorem iteratedDeriv_reciprocalOnePlus (k : ℕ) {t : ℝ} (ht : -1 < t) :
    iteratedDeriv k reciprocalOnePlus t = reciprocalOnePlusJet k t := by
  induction k generalizing t with
  | zero => simp [reciprocalOnePlus,reciprocalOnePlusJet]
  | succ k ih =>
    rw [iteratedDeriv_succ]
    have he : iteratedDeriv k reciprocalOnePlus =ᶠ[𝓝 t] reciprocalOnePlusJet k := by
      filter_upwards [eventually_gt_nhds ht] with y hy
      exact ih hy
    rw [he.deriv_eq]
    exact (hasDerivAt_reciprocalOnePlusJet k ht).deriv

theorem abs_reciprocalOnePlusJet (k : ℕ) {t : ℝ} (ht : -1 < t) :
    |reciprocalOnePlusJet k t| = (k.factorial : ℝ)/(1+t)^(k+1) := by
  unfold reciprocalOnePlusJet
  rw [abs_div,abs_mul,abs_pow,abs_neg,abs_one,one_pow,one_mul,
    abs_of_nonneg (Nat.cast_nonneg _),abs_of_pos (pow_pos (by linarith : 0 < 1+t) _)]

theorem iteratedDeriv_realExp (k : ℕ) (t : ℝ) : iteratedDeriv k Real.exp t = Real.exp t := by
  simpa only [one_mul,one_pow] using congrFun (_root_.iteratedDeriv_exp_const_mul k 1) t

theorem iteratedFDeriv_reciprocalOnePlus_apply (k : ℕ) {t : ℝ} (ht : -1 < t) (v : Fin k → ℝ) :
    iteratedFDeriv ℝ k reciprocalOnePlus t v = (∏ i, v i)*reciprocalOnePlusJet k t := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,iteratedDeriv_reciprocalOnePlus k ht]
  rfl

theorem iteratedFDeriv_realExp_apply (k : ℕ) (t : ℝ) (v : Fin k → ℝ) :
    iteratedFDeriv ℝ k Real.exp t v = Real.exp t * ∏ i, v i := by
  rw [iteratedFDeriv_apply_eq_iteratedDeriv_mul_prod,iteratedDeriv_realExp]
  simp only [smul_eq_mul,mul_comm]

theorem iteratedFDeriv_exp_linear_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (L : E →L[ℝ] ℝ) (b : ℝ) (k : ℕ) (x : E) (z : Fin k → E) :
    iteratedFDeriv ℝ k (fun y => Real.exp (L y+b)) x z = Real.exp (L x+b)*∏ i, L (z i) := by
  have hc : ContDiff ℝ ⊤ (fun t : ℝ => Real.exp (t+b)) := Real.contDiff_exp.comp (contDiff_id.add contDiff_const)
  have hh := congrArg (fun J => J z) (L.iteratedFDeriv_comp_right hc x (i := k) le_top)
  dsimp only [Function.comp_def] at hh
  rw [hh]
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply]
  rw [iteratedFDeriv_comp_add_right,iteratedFDeriv_realExp_apply]

end
end RectangleCLT.Companion.SplitV4
