import RectangleCLTArxivV1.LowerUnmaskedWidthRegime

/-! Actual amplitude-parametrized unmasked observations, with a harmless
finite-prefix fallback. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Filter RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section
set_option autoImplicit false

def lowerUnmaskedParameters (θ a : ℝ) : SymmetricFamilyParameters :=
  if h : 0 < θ ∧ 1 ≤ a ∧ θ*a^2 < 1/2 then
    { theta := θ
      pi := 1
      amplitude := a
      theta_pos := h.1
      theta_le_one := by
        have ha : 1 ≤ a^2 := by nlinarith [h.2.1]
        have hθ : θ ≤ θ*a^2 := by nlinarith
        linarith [h.2.2]
      pi_pos := by norm_num
      pi_le_one := le_rfl
      amplitude_pos := zero_lt_one.trans_le h.2.1
      variance_lt_half := by simpa only [mul_one] using h.2.2 }
  else unmaskedUnitParameters (1/4) (by norm_num) (by norm_num)

theorem lowerUnmaskedParameters_pi (θ a : ℝ) : (lowerUnmaskedParameters θ a).pi = 1 := by
  unfold lowerUnmaskedParameters
  split_ifs <;> rfl

theorem lowerUnmaskedParameters_theta {θ a : ℝ}
    (hθ : 0 < θ) (ha : 1 ≤ a) (hv : θ*a^2 < 1/2) :
    (lowerUnmaskedParameters θ a).theta = θ := by
  have h : 0 < θ ∧ 1 ≤ a ∧ θ*a^2 < 1/2 := ⟨hθ,ha,hv⟩
  simp only [lowerUnmaskedParameters,dif_pos h]

theorem lowerUnmaskedParameters_amplitude {θ a : ℝ}
    (hθ : 0 < θ) (ha : 1 ≤ a) (hv : θ*a^2 < 1/2) :
    (lowerUnmaskedParameters θ a).amplitude = a := by
  have h : 0 < θ ∧ 1 ≤ a ∧ θ*a^2 < 1/2 := ⟨hθ,ha,hv⟩
  simp only [lowerUnmaskedParameters,dif_pos h]

def lowerUnmaskedSequence (a : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) : SymmetricFamilyParameters :=
  lowerUnmaskedParameters (Real.log (m n : ℝ)/(2*n)) (a n)

theorem lowerUnmaskedSequence_pi (a : ℕ → ℝ) (m : ℕ → ℕ) (n : ℕ) :
    (lowerUnmaskedSequence a m n).pi = 1 := lowerUnmaskedParameters_pi _ _

end
end RectangleCLTArxivV1
