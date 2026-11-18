import RectangleCLTArxivV1.SupplementalHCubicMatrixMain
import RectangleCLTArxivV1.SupplementalHCubicConstant

/-! The checked single-face cubic matrix proposition with a universal
constant depending only on the fixed concentration constant C0. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem proposition_H1_cubic_matrix {p n K : ℕ} (hp : 1≤p)
    (ν : Measure (Vector (n+1))) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin (n+1)) ℝ) {C₀ δ κ σ : ℝ}
    (hC₀ : 0<C₀) (hδ : 0≤δ) (hκ : 0<κ) (hσ : 0<σ)
    (hunit : ∀ j,vectorNormSq (A j)=1) (hδh : δ≤s.bandwidth)
    (hc : IntrinsicRectangleConcentration (ν.map (fun x => A.mulVec x)) C₀ δ κ)
    (hδσ : δ*Real.sqrt (dimensionLog p)≤σ) :
    (∫ x, ∑ α : Fin (K+1) → Face p, symmetricNuclearNorm
      (supplementalHCubicSelectorScore s (σ • A) (A.mulVec x) α (selectorFaceNormal A (α 0))) ∂ν) ≤
      supplementalHCubicMatrixConstant C₀^(K+2)*s.bandwidth*κ*
        dimensionLog p*Real.sqrt (dimensionLog p) := by
  let L := dimensionLog p
  let R := Real.sqrt L
  let Z := s.bandwidth*κ*L*R
  have hL : 1≤L := log_exp_mul_nat_ge_one hp
  have hR : 1≤R := Real.one_le_sqrt.mpr hL
  have hLR : 1≤L*R := one_le_mul_of_one_le_of_one_le hL hR
  have hh : 0<s.bandwidth := s.bandwidth_pos
  have hZ : 0≤Z := by dsimp [Z]; positivity
  have h4 : 4*C₀*s.bandwidth*κ≤4*C₀*Z := by
    have ht := le_mul_of_one_le_right (show 0≤4*C₀*s.bandwidth*κ by positivity) hLR
    exact ht.trans_eq (by dsimp [Z]; ring)
  have hcor : (Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*(4*C₀*s.bandwidth*κ)*L ≤
      4*(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*C₀*Z := by
    have ht := le_mul_of_one_le_right
      (show 0≤(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*(4*C₀*s.bandwidth*κ)*L by positivity) hR
    exact ht.trans_eq (by dsimp [Z]; ring)
  have hb := intrinsicRectangleConcentration_cubicMatrix_raw (K := K) hp ν s A hC₀ hδ hκ hσ hunit hδh hc hδσ
  calc
    _ ≤ 48*Real.exp 16*((K:ℝ)+2)*C₀*s.bandwidth*κ*L*R+
        (4*C₀*Z+4*(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*C₀*Z)+
        (2:ℝ)^K*((32768*Real.exp ((3:ℝ)/2))*Real.exp 128*C₀*κ*s.bandwidth*L*R) :=
      hb.trans (add_le_add_right (add_le_add_left (add_le_add h4 hcor) _) _)
    _ = (48*Real.exp 16*((K:ℝ)+2)*C₀+4*C₀+
        4*(Real.exp (13/2:ℝ)+8)*((K:ℝ)+1)*C₀+
        2^K*(32768*Real.exp (3/2:ℝ)*Real.exp 128)*C₀)*Z := by dsimp [Z]; ring
    _ ≤ supplementalHCubicMatrixConstant C₀^(K+2)*Z :=
      mul_le_mul_of_nonneg_right (supplementalH_cubic_matrix_bracket_le_power hC₀.le K) hZ
    _ = _ := by dsimp [Z,R,L]; ring

end
end RectangleCLTArxivV1
