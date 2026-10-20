import RectangleCLTCompanion.SignedSurfacePairTube
import RectangleCLTCompanion.SignedSurfaceWeightedDomination
import RectangleCLTCompanion.SignedSurfaceGammaTubeIntegration
import RectangleCLTCompanion.SignedSurfaceRadius
import RectangleCLTCompanion.SignedSurfaceShells
import RectangleCLTCompanion.SignedSurfaceTubes

/-! Actual two-face Gamma-tube bounds, retaining the paired determinant
factor and all Gamma shape factors. No correlation-gap premise is used. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def pairShellMoment {p : ℕ} (a : ℕ) (S : CompatibleFaceTuple p 2)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ)
    (r : Vector p) (B : Set (Vector p)) : ℝ :=
  ∫ z in B, gammaFaceKernel a (s.weights ((σ • A).mulVec z + r)) (activeFaces S) *
    fourFaceProjectionRadius (σ • A) z ∂standardGaussian p

theorem pairShellMoment_nonneg {p : ℕ} (a : ℕ) (S : CompatibleFaceTuple p 2)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ)
    (r : Vector p) (B : Set (Vector p)) : 0 ≤ pairShellMoment a S s A σ r B := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (gammaFaceKernel_nonneg a _ _) (fourFaceProjectionRadius_nonneg _ _)

/-- Exact source normalization followed by the true common-experiment
probability bound. The active Gram determinant may be arbitrarily small. -/
theorem pairShellMoment_tube_bound {p : ℕ} (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ ε R : ℝ}
    (hσ : 0 < σ) (hε : 0 < ε) (hε1 : ε ≤ 1) (hR : 0 ≤ R) (hRε : R * ε ≤ 1)
    (r : Vector p) {B : Set (Vector p)} (hBm : MeasurableSet B)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius (σ • A) z ≤ R) :
    (((a : ℝ) + 1) * ((a : ℝ) + 2) * σ ^ 2 * ε ^ 2 *
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
      Real.sqrt (S.gram (A * A.transpose)).det / (16 * s.bandwidth ^ 2)) *
      pairShellMoment a S s A σ r B ≤
      (Real.exp ((3 : ℝ) / 2) * R) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r B (pairTubeCoefficients S A σ ε)) := by
  let D := pairTubeCoefficients S A σ ε
  let K := fourFaceProjectionRadius (σ • A)
  have hdpos : 0 < ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det := by
    rw [normalMatrix_scaled_gram_det]
    positivity
  have hd : IsUnit ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det :=
    isUnit_iff_ne_zero.mpr hdpos.ne'
  have hDm : MeasurableSet D := pairCoefficientDomain_measurable _ _ σ ε
  have hKgi : Integrable K (standardGaussian p) := by
    have hi := (integrable_fourFaceProjectionRadius_moment hp (σ • A) 1).1.sub
      (integrable_const (1 : ℝ))
    convert hi using 1
    funext z
    simp [K]
  have hDnorm : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S (σ • A)).mulVec c)‖ ≤ ε :=
    fun c hc => pairTubeCoefficients_displacement_le S A hdiag hdet σ hε.le hc
  have hi := lintegral_ratioWeightOf_le_exp_three_halves_mul S s (σ • A) r hBm hDm hd
    (by decide) (by decide) hR hε.le hε1 hRε hB hDnorm K hR hB
    ((standardGaussian p).prod (gammaRectangleLaw p a))
  rw [lintegral_ratioWeightOf_eq_gammaFaceKernel a S s (σ • A) r hBm hDm K
    (measurable_fourFaceProjectionRadius _) hKgi (fourFaceProjectionRadius_nonneg _) hactive hd hdpos.le,
    gamma_face_factor_two] at hi
  have hI : 0 ≤ pairShellMoment a S s A σ r B := pairShellMoment_nonneg a S s A σ r B
  have hpre : 0 ≤
      (((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det / s.bandwidth ^ 2) *
        (((a : ℝ) + 1) * ((a : ℝ) + 2)) * pairShellMoment a S s A σ r B := by positivity
  have hreal := ENNReal.toReal_mono
    (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)) hi
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hpre,
    ENNReal.toReal_ofReal (mul_nonneg (Real.exp_nonneg _) hR)] at hreal
  change (volume : Measure (Fin 2 → ℝ)).real D *
      (ENNReal.ofReal ((((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det /
        s.bandwidth ^ 2) * (((a : ℝ) + 1) * ((a : ℝ) + 2)) *
        pairShellMoment a S s A σ r B)).toReal ≤ _ at hreal
  rw [ENNReal.toReal_ofReal hpre] at hreal
  have hleft : (volume : Measure (Fin 2 → ℝ)).real D *
      ((((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det / s.bandwidth ^ 2) *
        (((a : ℝ) + 1) * ((a : ℝ) + 2)) * pairShellMoment a S s A σ r B) =
      (((a : ℝ) + 1) * ((a : ℝ) + 2) * σ ^ 2 * ε ^ 2 *
        ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det / (16 * s.bandwidth ^ 2)) *
        pairShellMoment a S s A σ r B := by
    calc
      _ = (((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det *
          (volume : Measure (Fin 2 → ℝ)).real D) / s.bandwidth ^ 2 *
            (((a : ℝ) + 1) * ((a : ℝ) + 2)) * pairShellMoment a S s A σ r B := by ring
      _ = _ := by rw [pairTube_gram_mul_volume S A hdiag hdet hσ hε.le]; ring
  rw [hleft] at hreal
  exact hreal

/-- The paired ridge contribution in the actual tangent-score identity.
Its Gamma factor `a+2` cancels against the source normalization. -/
def pairSurfacePenalty {p : ℕ} (a : ℕ) (S : CompatibleFaceTuple p 2)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ)
    (r : Vector p) (B : Set (Vector p)) : ℝ :=
  (((a : ℝ) + 2) * σ / s.bandwidth) *
    ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
      Real.sqrt (S.gram (A * A.transpose)).det * pairShellMoment a S s A σ r B

theorem pair_surface_shell_le_image_probability {p : ℕ} (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (r : Vector p) {B : Set (Vector p)} (hBm : MeasurableSet B)
    {σ ε R : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius (σ • A) z ≤ R)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hdet : 0 < (S.gram (A * A.transpose)).det) :
    pairSurfacePenalty a S s A σ r B ≤
      (16 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * R /
        (((a : ℝ) + 1) * σ * ε ^ 2)) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r B (pairTubeCoefficients S A σ ε)) := by
  have hband : 0 < s.bandwidth := s.bandwidth_pos
  have hh := pairShellMoment_tube_bound hp a S s A hdiag hactive hdet
    hσ hε hε1 hR hRε r hBm hB
  let factor : ℝ := 16 * s.bandwidth / (((a : ℝ) + 1) * σ * ε ^ 2)
  have hfactor : 0 ≤ factor := by dsimp [factor]; positivity
  have hm := mul_le_mul_of_nonneg_left hh hfactor
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  have hleft : factor *
      ((((a : ℝ) + 1) * ((a : ℝ) + 2) * σ ^ 2 * ε ^ 2 *
        ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det / (16 * s.bandwidth ^ 2)) *
        pairShellMoment a S s A σ r B) = pairSurfacePenalty a S s A σ r B := by
    dsimp [factor, pairSurfacePenalty]
    field_simp [ha, hσ.ne', hε.ne', s.bandwidth_pos.ne']
    ring
  rw [hleft] at hm
  exact hm.trans_eq (by dsimp [factor]; ring)


/-- A ready-to-sum dyadic form, with a universal cubic shell cost. -/
theorem pair_surface_dyadic_shell_le_image_probability {p : ℕ} (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hdet : 0 < (S.gram (A * A.transpose)).det) {σ : ℝ} (hσ : 0 < σ)
    (r : Vector p) (n : ℕ) :
    pairSurfacePenalty a S s A σ r (dyadicShell (fourFaceProjectionRadius (σ • A)) n) ≤
      (64 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * dyadicRadius n ^ 3 /
        (((a : ℝ) + 1) * σ)) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r (dyadicShell (fourFaceProjectionRadius (σ • A)) n)
            (pairTubeCoefficients S A σ (tubeRadius (dyadicRadius n)))) := by
  have hband : 0 < s.bandwidth := s.bandwidth_pos
  let R := dyadicRadius n
  have hR : 1 ≤ R := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hR0 : 0 ≤ R := by linarith
  have hε : 0 < tubeRadius R := tubeRadius_pos hR0
  have hh := pair_surface_shell_le_image_probability hp a S s A hdiag r
    (measurableSet_dyadicShell _ (measurable_fourFaceProjectionRadius _) n)
    hσ hε hR0 (tubeRadius_le_one hR0) (mul_tubeRadius_le_one hR0)
    (fun z hz => hz.1) hactive hdet
  have hc : 16 * Real.exp ((3 : ℝ) / 2) * R / tubeRadius R ^ 2 ≤
      64 * Real.exp ((3 : ℝ) / 2) * R ^ 3 := by
    simp only [tubeRadius, inv_pow, div_inv_eq_mul]
    have hs : (1 + R) ^ 2 ≤ (2 * R) ^ 2 := by nlinarith
    calc
      _ ≤ (16 * Real.exp ((3 : ℝ) / 2) * R) * (2 * R) ^ 2 :=
        mul_le_mul_of_nonneg_left hs (by positivity)
      _ = _ := by ring
  have ha : (a : ℝ) + 1 ≠ 0 := by positivity
  have hcoef : 16 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * R /
      (((a : ℝ) + 1) * σ * tubeRadius R ^ 2) ≤
      64 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * R ^ 3 / (((a : ℝ) + 1) * σ) := by
    calc
      _ = (s.bandwidth / (((a : ℝ) + 1) * σ)) *
          (16 * Real.exp ((3 : ℝ) / 2) * R / tubeRadius R ^ 2) := by
        field_simp [ha, hσ.ne', hε.ne']
        ring
      _ ≤ (s.bandwidth / (((a : ℝ) + 1) * σ)) *
          (64 * Real.exp ((3 : ℝ) / 2) * R ^ 3) :=
        mul_le_mul_of_nonneg_left hc (by positivity)
      _ = _ := by ring
  exact hh.trans (mul_le_mul_of_nonneg_right hcoef (measureReal_nonneg))

end
end RectangleCLT.Companion.SignedSurface
