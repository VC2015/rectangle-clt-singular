import RectangleCLTArxivV1.SupplementalGSeededPatterns

/-! Actual half-Gaussian scale conditions in the late-time H application. -/
namespace RectangleCLTArxivV1
open RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem hFourth_seed_scale_range {δ L h t : ℝ}
    (hδ : 0 ≤ δ) (hL : 1 ≤ L) (hh : 0 < h) (hband : 2*δ ≤ h)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hsmall : L*h^2 ≤ 1/4) :
    0 < seededSplitGaussianScale (L*h^2) t ∧
      δ*Real.sqrt L ≤ seededSplitGaussianScale (L*h^2) t ∧
        seededSplitGaussianScale (L*h^2) t ≤ 1 := by
  have hLp : 0 < L := zero_lt_one.trans_le hL
  have hε : 0 < L*h^2 := mul_pos hLp (sq_pos_of_pos hh)
  have hpos : 0 < t+L*h^2 := add_pos_of_nonneg_of_pos ht.1 hε
  have hσ : 0 < seededSplitGaussianScale (L*h^2) t := Real.sqrt_pos.mpr (half_pos hpos)
  refine ⟨hσ, ?_, ?_⟩
  · have hsquare : 2*δ^2 ≤ h^2 := by nlinarith [sq_nonneg δ]
    have hvar : δ^2*L ≤ (t+L*h^2)/2 := by
      nlinarith [mul_le_mul_of_nonneg_right hsquare hLp.le,ht.1]
    have hs := Real.sqrt_le_sqrt hvar
    simpa only [Real.sqrt_mul (sq_nonneg δ),Real.sqrt_sq hδ,seededSplitGaussianScale] using hs
  · change Real.sqrt ((t+L*h^2)/2) ≤ 1
    exact Real.sqrt_le_iff.mpr ⟨by norm_num, by linarith [ht.2]⟩

theorem hFourth_normalized_seed_scale_range {p : ℕ} (hp : 1 ≤ p)
    (s : FaceSmoother p) {δ t : ℝ} (hδ : 0 ≤ δ) (hband : 2*δ ≤ s.bandwidth)
    (ht : t ∈ Set.Icc (0:ℝ) 1) (hsmall : dimensionLog p*s.bandwidth^2 ≤ 1/4) :
    0 < seededSplitGaussianScale (dimensionLog p*s.bandwidth^2) t ∧
      δ*Real.sqrt (dimensionLog p) ≤ seededSplitGaussianScale (dimensionLog p*s.bandwidth^2) t ∧
        seededSplitGaussianScale (dimensionLog p*s.bandwidth^2) t ≤ 1 :=
  hFourth_seed_scale_range hδ (log_exp_mul_nat_ge_one hp) s.bandwidth_pos hband ht hsmall

end
end RectangleCLTArxivV1
