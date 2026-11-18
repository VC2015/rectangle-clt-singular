import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Tactic

/-! Scalar absorption of the proved cubic matrix family budgets. -/
namespace RectangleCLTArxivV1
noncomputable section
set_option autoImplicit false

theorem linear_and_dyadic_budget_le_power {a b c d : ℝ}
    (ha : 0≤a) (hb : 0≤b) (hc : 0≤c) (hd : 0≤d) (K : ℕ) :
    a*((K:ℝ)+2)+b+c*((K:ℝ)+1)+d*2^K≤(4+a+b+c+d)^(K+2) := by
  let A := a+b+c+d
  let C := 4+a+b+c+d
  have hA : 0≤A := by dsimp [A]; positivity
  have hC : 4≤C := by dsimp [C]; linarith
  have hC0 : 0≤C := by linarith
  have hpow : 1≤(2:ℝ)^K := one_le_pow₀ (by norm_num)
  have hk : 1≤(K:ℝ)+2 := by
    linarith [show (0:ℝ)≤(K:ℝ) from Nat.cast_nonneg K]
  have hfac : 1≤((K:ℝ)+2)*2^K := one_le_mul_of_one_le_of_one_le hk hpow
  have hka : (K:ℝ)+2≤((K:ℝ)+2)*2^K := le_mul_of_one_le_right (by positivity) hpow
  have hkb : (K:ℝ)+1≤((K:ℝ)+2)*2^K := (by linarith : (K:ℝ)+1≤(K:ℝ)+2).trans hka
  have hkd : (2:ℝ)^K≤((K:ℝ)+2)*2^K := le_mul_of_one_le_left (by positivity) hk
  have h1 := mul_le_mul_of_nonneg_left hka ha
  have h2 := mul_le_mul_of_nonneg_left hfac hb
  have h3 := mul_le_mul_of_nonneg_left hkb hc
  have h4 := mul_le_mul_of_nonneg_left hkd hd
  have hs : a*((K:ℝ)+2)+b+c*((K:ℝ)+1)+d*2^K≤A*(((K:ℝ)+2)*2^K) := by
    dsimp [A]
    nlinarith only [h1,h2,h3,h4]
  have hkpow : ∀ k : ℕ,(k:ℝ)+2≤(2:ℝ)^(k+1) := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      rw [pow_succ]
      push_cast
      nlinarith
  have hkp := mul_le_mul_of_nonneg_right (hkpow K) (by positivity : 0≤(2:ℝ)^K)
  have he : (2:ℝ)^(K+1)*(2:ℝ)^K=2*(4:ℝ)^K := by
    rw [pow_succ]
    calc
      _ = 2*((2:ℝ)^K*(2:ℝ)^K) := by ring
      _ = _ := by rw [←mul_pow]; norm_num
  rw [he] at hkp
  have hC2 : 2*A≤C^2 := by dsimp [C,A]; nlinarith [sq_nonneg (a+b+c+d)]
  have hpowC : (4:ℝ)^K≤C^K := pow_le_pow_left₀ (by norm_num) hC K
  calc
    _ ≤ A*(((K:ℝ)+2)*2^K) := hs
    _ ≤ A*(2*4^K) := mul_le_mul_of_nonneg_left hkp hA
    _ = (2*A)*4^K := by ring
    _ ≤ C^2*C^K := mul_le_mul hC2 hpowC (by positivity) (by positivity)
    _ = _ := by rw [pow_add]; dsimp [C]; ring

def supplementalHCubicTraceConstant : ℝ := 32768*Real.exp (3/2 : ℝ)*Real.exp 128

def supplementalHCubicMatrixConstant (C₀ : ℝ) : ℝ :=
  4+48*Real.exp 16*C₀+4*C₀+4*(Real.exp (13/2 : ℝ)+8)*C₀+supplementalHCubicTraceConstant*C₀

theorem supplementalHCubicMatrixConstant_pos {C₀ : ℝ} (hC₀ : 0≤C₀) :
    0<supplementalHCubicMatrixConstant C₀ := by
  unfold supplementalHCubicMatrixConstant supplementalHCubicTraceConstant
  positivity

theorem supplementalH_cubic_matrix_bracket_le_power {C₀ : ℝ} (hC₀ : 0≤C₀) (K : ℕ) :
    48*Real.exp 16*((K:ℝ)+2)*C₀+4*C₀+
      4*(Real.exp (13/2 : ℝ)+8)*((K:ℝ)+1)*C₀+
      2^K*(32768*Real.exp (3/2 : ℝ)*Real.exp 128)*C₀ ≤
      supplementalHCubicMatrixConstant C₀^(K+2) := by
  have hh := linear_and_dyadic_budget_le_power
    (a:=48*Real.exp 16*C₀) (b:=4*C₀)
    (c:=4*(Real.exp (13/2 : ℝ)+8)*C₀) (d:=supplementalHCubicTraceConstant*C₀)
    (by positivity) (by positivity) (by positivity)
    (by unfold supplementalHCubicTraceConstant; positivity) K
  convert hh using 1 <;> simp only [supplementalHCubicMatrixConstant,supplementalHCubicTraceConstant] <;> ring

end
end RectangleCLTArxivV1
