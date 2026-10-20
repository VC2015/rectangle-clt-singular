import RectangleCLTCompanion.SignedSurfaceDomination

/-! Actual transported short-tube ratios with a nonnegative source weight.
The source weight is bounded only on its localized source domain. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

theorem ratioWeightOf_nonneg {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ)) (g : Vector p → ℝ)
    (hg : ∀ z, 0 ≤ g z) (ze : Vector p × (ℝ × (Face p → ℝ))) :
    0 ≤ ratioWeightOf S s A r B D g ze := by
  apply Set.indicator_nonneg
  intro _ _
  exact mul_nonneg (div_nonneg (standardGaussianDensity_pos _ _).le
    (standardGaussianDensity_pos _ _).le) (hg _)

theorem ratioWeightOf_le_exp_three_halves_mul {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (B : Set (Vector p)) (D : Set (Fin q → ℝ))
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq0 : 0 < q) (hq : q ≤ 4) {R ε C : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius A z ≤ R)
    (hD : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S A).mulVec c)‖ ≤ ε)
    (g : Vector p → ℝ) (hC : 0 ≤ C) (hg : ∀ z ∈ B, g z ≤ C)
    (ze : Vector p × (ℝ × (Face p → ℝ))) :
    ratioWeightOf S s A r B D g ze ≤
      Real.exp ((3 : ℝ) / 2) * C * (imageEventOf S s A r B D).indicator (fun _ => 1) ze := by
  have hbound := ratioWeightOf_le_exp_three_halves S s A r B D hd hq0 hq hR hε hε1 hRε hB hD ze
  by_cases hz : ze ∈ imageEventOf S s A r B D
  · have hpre := ((imageEventOf_iff_preimage S s A r B D hd ze).mp hz).2.2.1
    have hratio0 : 0 ≤ standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
        standardGaussianDensity p ze.1 :=
      div_nonneg (standardGaussianDensity_pos _ _).le (standardGaussianDensity_pos _ _).le
    have hmul := mul_le_mul_of_nonneg_left (hg _ hpre) hratio0
    have hbound' : standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
        standardGaussianDensity p ze.1 ≤ Real.exp ((3 : ℝ) / 2) := by
      simpa only [ratioWeightOf, Set.indicator_of_mem hz, mul_one] using hbound
    calc
      _ ≤ (standardGaussianDensity p (base (imagePreimage S s A (r, ze))) /
          standardGaussianDensity p ze.1) * C := by
        simpa only [ratioWeightOf, Set.indicator_of_mem hz] using hmul
      _ ≤ Real.exp ((3 : ℝ) / 2) * C := mul_le_mul_of_nonneg_right hbound' hC
      _ = _ := by rw [Set.indicator_of_mem hz, mul_one]
  · simp only [ratioWeightOf, Set.indicator_of_not_mem hz, mul_zero, le_refl]

theorem lintegral_ratioWeightOf_le_exp_three_halves_mul {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    {B : Set (Vector p)} {D : Set (Fin q → ℝ)}
    (hBm : MeasurableSet B) (hDm : MeasurableSet D)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq0 : 0 < q) (hq : q ≤ 4) {R ε C : ℝ} (hR : 0 ≤ R) (hε : 0 ≤ ε)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius A z ≤ R)
    (hD : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S A).mulVec c)‖ ≤ ε)
    (g : Vector p → ℝ) (hC : 0 ≤ C) (hg : ∀ z ∈ B, g z ≤ C)
    (μ : Measure (Vector p × (ℝ × (Face p → ℝ)))) :
    (∫⁻ ze, ENNReal.ofReal (ratioWeightOf S s A r B D g ze) ∂μ) ≤
      ENNReal.ofReal (Real.exp ((3 : ℝ) / 2) * C) * μ (imageEventOf S s A r B D) := by
  have hE : MeasurableSet (imageEventOf S s A r B D) :=
    (measurableSet_imageEventOf_joint S s A hBm hDm hd).preimage
      (measurable_const.prodMk measurable_id)
  have hpoint (ze : Vector p × (ℝ × (Face p → ℝ))) :
      ENNReal.ofReal (ratioWeightOf S s A r B D g ze) ≤
        (imageEventOf S s A r B D).indicator
          (fun _ => ENNReal.ofReal (Real.exp ((3 : ℝ) / 2) * C)) ze := by
    have hh := ratioWeightOf_le_exp_three_halves_mul S s A r B D hd hq0 hq hR hε hε1 hRε hB hD
      g hC hg ze
    by_cases hz : ze ∈ imageEventOf S s A r B D
    · simpa only [Set.indicator_of_mem hz, mul_one] using ENNReal.ofReal_le_ofReal hh
    · simp only [ratioWeightOf, Set.indicator_of_not_mem hz, ENNReal.ofReal_zero, le_refl]
  exact (lintegral_mono hpoint).trans_eq (lintegral_indicator_const hE _)

end
end RectangleCLT.Companion.SignedSurface
