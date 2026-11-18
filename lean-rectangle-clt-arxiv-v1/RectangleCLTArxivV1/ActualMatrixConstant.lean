import RectangleCLTArxivV1.SupplementalHCubicConstant
import RectangleCLTArxivV1.SupplementalHPairMatrixEstimate

/-! A single numerical matrix constant, fixed before all dimensions,
arrays, normals, base laws and cutoff choices. -/
namespace RectangleCLTArxivV1
noncomputable section
set_option autoImplicit false

def actualMatrixConstant (C₀ : ℝ) : ℝ :=
  max 1 (max (supplementalHCubicMatrixConstant C₀) (supplementalHPairPhysicalMatrixConstant C₀))

theorem actualMatrixConstant_ge_one (C₀ : ℝ) : 1≤actualMatrixConstant C₀ := le_max_left _ _

theorem actualMatrixConstant_ge_cubic (C₀ : ℝ) :
    supplementalHCubicMatrixConstant C₀≤actualMatrixConstant C₀ :=
  (le_max_left _ _).trans (le_max_right _ _)

theorem actualMatrixConstant_ge_pair (C₀ : ℝ) :
    supplementalHPairPhysicalMatrixConstant C₀≤actualMatrixConstant C₀ :=
  (le_max_right _ _).trans (le_max_right _ _)

theorem actualMatrix_cubic_power_le {C₀ : ℝ} (hC₀ : 0≤C₀) (k : ℕ) :
    supplementalHCubicMatrixConstant C₀^k≤actualMatrixConstant C₀^k :=
  pow_le_pow_left₀ (supplementalHCubicMatrixConstant_pos hC₀).le (actualMatrixConstant_ge_cubic C₀) k

theorem actualMatrix_pair_power_le {C₀ : ℝ} (hC₀ : 0≤C₀) (k : ℕ) :
    supplementalHPairPhysicalMatrixConstant C₀^k≤actualMatrixConstant C₀^k :=
  pow_le_pow_left₀ ((by norm_num : (0:ℝ)≤4).trans (supplementalHPairPhysicalMatrixConstant_ge_four hC₀))
    (actualMatrixConstant_ge_pair C₀) k

end
end RectangleCLTArxivV1
