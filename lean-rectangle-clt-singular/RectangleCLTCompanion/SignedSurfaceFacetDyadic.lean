import RectangleCLTCompanion.SignedSurfaceFacetTube
import RectangleCLTCompanion.SignedSurfaceShells
import RectangleCLTCompanion.SignedSurfaceTubes

/-! A ready-to-sum singleton surface bound on the actual dyadic partition.
The Gamma factor `a+1` is retained without a face-count factor. -/

open MeasureTheory

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

theorem facet_surface_dyadic_shell_le_image_probability
    {p : ℕ} (hp : 1 ≤ p) (a : ℕ) (S : CompatibleFaceTuple p 1) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hactive : ∀ i, S.face i ∈ s.faces) {σ : ℝ} (hσ : 0 < σ)
    (r : Vector p) (n : ℕ) :
    (∫ z in dyadicShell (fourFaceProjectionRadius (σ • A)) n,
      s.F ((σ • A).mulVec z + r) ^ (a + 1) *
        s.pi ((σ • A).mulVec z + r) (S.face 0) *
          (1 + fourFaceProjectionRadius (σ • A) z ^ 2) ∂standardGaussian p) ≤
      (16 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 /
        (((a : ℝ) + 1) * σ)) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r (dyadicShell (fourFaceProjectionRadius (σ • A)) n)
            (facetTubeCoefficients σ (tubeRadius (dyadicRadius n)))) := by
  have hband : 0 < s.bandwidth := s.bandwidth_pos
  let R := dyadicRadius n
  have hR : 1 ≤ R := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hR0 : 0 ≤ R := zero_le_one.trans hR
  have hε : 0 < tubeRadius R := tubeRadius_pos hR0
  have hh := facet_surface_shell_le_image_probability hp a S s A hdiag r
    (measurableSet_dyadicShell _ (measurable_fourFaceProjectionRadius _) n)
    hσ hε hR0 (tubeRadius_le_one hR0) (mul_tubeRadius_le_one hR0)
    (fun z hz => hz.1) hactive
  have hc : 4 * Real.exp ((3 : ℝ) / 2) * (1 + R ^ 2) / tubeRadius R ≤
      16 * Real.exp ((3 : ℝ) / 2) * R ^ 3 := by
    simp only [tubeRadius, div_inv_eq_mul]
    have hs : 1 + R ^ 2 ≤ 2 * R ^ 2 := by nlinarith
    have ht : 1 + R ≤ 2 * R := by linarith
    calc
      _ ≤ (4 * Real.exp ((3 : ℝ) / 2) * (2 * R ^ 2)) * (2 * R) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hs (by positivity)) ht
          (by linarith) (by positivity)
      _ = _ := by ring
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  have hcoef : 4 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * (1 + R ^ 2) /
      (((a : ℝ) + 1) * σ * tubeRadius R) ≤
      16 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * R ^ 3 / (((a : ℝ) + 1) * σ) := by
    calc
      _ = (s.bandwidth / (((a : ℝ) + 1) * σ)) *
          (4 * Real.exp ((3 : ℝ) / 2) * (1 + R ^ 2) / tubeRadius R) := by
        field_simp [ha, hσ.ne', hε.ne']
        ring
      _ ≤ (s.bandwidth / (((a : ℝ) + 1) * σ)) *
          (16 * Real.exp ((3 : ℝ) / 2) * R ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef measureReal_nonneg)

end
end RectangleCLT.Companion.SignedSurface
