import RectangleCLTCompanion.SignedSurfaceTransport
import RectangleCLT.GaussianTubeDomination

/-! Uniform actual Gaussian density-ratio bounds on localized arbitrary
tube domains. All estimates use only the active normal-span radius. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

theorem density_ratio_short_shift_le {p : ℕ} (z d : Vector p)
    (hinner : faceDot d z ≤ 1) (hnorm : ‖projectionEuclideanVector d‖ ≤ 1) :
    standardGaussianDensity p z / standardGaussianDensity p (z + d) ≤
      Real.exp ((3 : ℝ) / 2) := by
  have hsq : vectorNormSq d ≤ 1 := by
    rw [← projectionEuclideanVector_norm_sq]
    nlinarith [norm_nonneg (projectionEuclideanVector d)]
  have hexp : Real.exp (-(3 : ℝ) / 2) ≤
      Real.exp (-faceDot d z - vectorNormSq d / 2) := by
    apply Real.exp_le_exp.mpr
    linarith
  have hlower := mul_le_mul_of_nonneg_left hexp (standardGaussianDensity_pos p z).le
  rw [← standardGaussianDensity_translate] at hlower
  have hm := mul_le_mul_of_nonneg_left hlower (Real.exp_nonneg ((3 : ℝ) / 2))
  have hc : Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2) = 1 := by
    rw [← Real.exp_add]
    norm_num
  have hleft : Real.exp ((3 : ℝ) / 2) * (standardGaussianDensity p z *
      Real.exp (-(3 : ℝ) / 2)) = standardGaussianDensity p z := by
    calc
      _ = (Real.exp ((3 : ℝ) / 2) * Real.exp (-(3 : ℝ) / 2)) * standardGaussianDensity p z := by ring
      _ = _ := by rw [hc, one_mul]
  rw [hleft] at hm
  exact (div_le_iff₀ (standardGaussianDensity_pos p (z + d))).mpr (by linarith)

/-- Source localization implies a uniform bound for the actual transported
ratio. The ambient Gaussian covariance may be singular. -/
theorem ratioWeightOf_le_exp_three_halves {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq0 : 0 < q) (hq : q ≤ 4) {R ε : ℝ} (_hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius A z ≤ R)
    (hD : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S A).mulVec c)‖ ≤ ε)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    ratioWeightOf S s A r B D (fun _ => 1) ze ≤
      Real.exp ((3 : ℝ) / 2) * (imageEventOf S s A r B D).indicator (fun _ => 1) ze := by
  by_cases hz : ze ∈ imageEventOf S s A r B D
  · have hzmem := hz
    obtain ⟨h0, he, w, hw, hm⟩ := hz
    have hpre : imagePreimage S s A (r, ze) = w := by
      change inverse (normalMatrix S A) s.bandwidth ze.2.1 (activeOffsets S s r)
        (Sum.elim ze.1 (fun i => ze.2.2 (S.face i))) = _
      rw [← hm, inverse_map _ s.bandwidth_pos.ne' h0.ne' hd]
    have hy := congrArg (base : Coordinates p q → Vector p) hm
    rw [base_map] at hy
    change base w + (normalMatrix S A).mulVec (tube w) = ze.1 at hy
    have hspan := normalMatrix_mulVec_mem_normalSpan S A (tube w)
    have hbound := S.abs_faceDot_normalSpan_le_projectionRadius A hq0 hq hspan (base w)
    have hinner : faceDot ((normalMatrix S A).mulVec (tube w)) (base w) ≤ 1 := by
      exact (le_abs_self _).trans (hbound.trans
        ((mul_le_mul (hD _ hw.2.1) (hB _ hw.1)
          (fourFaceProjectionRadius_nonneg A _) hε).trans (by nlinarith [hRε])))
    have hr := density_ratio_short_shift_le (base w) ((normalMatrix S A).mulVec (tube w))
      hinner ((hD _ hw.2.1).trans hε1)
    rw [hy] at hr
    simpa only [ratioWeightOf, Set.indicator_of_mem hzmem, hpre, mul_one] using hr
  · simp only [ratioWeightOf, Set.indicator_of_not_mem hz, mul_zero, le_refl]

end
end RectangleCLT.Companion.SignedSurface
