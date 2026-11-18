import RectangleCLTArxivV1.SupplementalHCubicConstant

/-! Universal scalar absorption for the actual pair matrix costs. -/
namespace RectangleCLTArxivV1
noncomputable section
set_option autoImplicit false

def supplementalHPairMatrixConstant (C₀ D₀ D₁ D₂ : ℝ) : ℝ :=
  4+4*(D₀+2*Real.pi*C₀)+2*D₁+D₂

theorem supplementalHPairMatrixConstant_ge_four {C₀ D₀ D₁ D₂ : ℝ}
    (hC₀ : 0≤C₀) (hD₀ : 0≤D₀) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂) :
    4≤supplementalHPairMatrixConstant C₀ D₀ D₁ D₂ := by
  unfold supplementalHPairMatrixConstant
  have hp : 0≤2*Real.pi*C₀ := by positivity
  linarith

theorem supplementalH_pair_matrix_bracket_le_power {C₀ D₀ D₁ D₂ : ℝ}
    (hC₀ : 0≤C₀) (hD₀ : 0≤D₀) (hD₁ : 0≤D₁) (hD₂ : 0≤D₂) (K : ℕ) :
    2*D₁+4*(D₀+2*Real.pi*C₀)*((K:ℝ)+3)+(2:ℝ)^K*D₂ ≤
      supplementalHPairMatrixConstant C₀ D₀ D₁ D₂^(K+3) := by
  have hpow : (2:ℝ)^K≤(2:ℝ)^(K+1) := le_mul_of_one_le_right (by positivity) (by norm_num)
  have hp := linear_and_dyadic_budget_le_power
    (a := 4*(D₀+2*Real.pi*C₀)) (b := 2*D₁) (c := 0) (d := D₂)
    (by positivity) (by positivity) (by norm_num) hD₂ (K+1)
  have hstep := mul_le_mul_of_nonneg_right hpow hD₂
  calc
    _ ≤ 4*(D₀+2*Real.pi*C₀)*((K:ℝ)+3)+2*D₁+0*((K:ℝ)+2)+D₂*(2:ℝ)^(K+1) := by nlinarith only [hstep]
    _ ≤ supplementalHPairMatrixConstant C₀ D₀ D₁ D₂^(K+3) := by
      convert hp using 1 <;> simp only [Nat.cast_add,Nat.cast_one,Nat.add_assoc,
        show (1:ℝ)+2=3 by norm_num,show (1:ℝ)+1=2 by norm_num,
        show (1:ℕ)+2=3 by decide,supplementalHPairMatrixConstant] <;> ring

end
end RectangleCLTArxivV1
