import RectangleCLTCompanion.SignedSurfacePairTube
import RectangleCLTCompanion.SignedSurfaceGammaTubeIntegration
import RectangleCLTCompanion.SignedSurfaceWeightedDomination
import RectangleCLTCompanion.SignedSurfaceRadius

/-! The actual one-face tube coefficient interval, with exact volume and
Gram cancellation. The Gaussian factor may be singular. -/

open MeasureTheory RectangleCLT.GaussianTube Set
open scoped BigOperators ENNReal InnerProductSpace

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def facetTubeCoefficients (σ ε : ℝ) : Set (Fin 1 → ℝ) :=
  Set.Icc (fun _ => ε / (4 * σ)) (fun _ => ε / (2 * σ))

theorem facetTubeCoefficients_measurable (σ ε : ℝ) :
    MeasurableSet (facetTubeCoefficients σ ε) := measurableSet_Icc

theorem facetTubeCoefficients_volume {σ ε : ℝ} (hσ : 0 < σ) :
    (volume : Measure (Fin 1 → ℝ)) (facetTubeCoefficients σ ε) =
      ENNReal.ofReal (ε / (4 * σ)) := by
  rw [facetTubeCoefficients, Real.volume_Icc_pi]
  simp only [Fin.prod_univ_one]
  congr 1
  field_simp
  ring

theorem facetTubeCoefficients_real_volume {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε) :
    (volume : Measure (Fin 1 → ℝ)).real (facetTubeCoefficients σ ε) = ε / (4 * σ) := by
  rw [measureReal_def, facetTubeCoefficients_volume hσ, ENNReal.toReal_ofReal]
  positivity

theorem facetTubeCoefficients_positive {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 < ε)
    {c : Fin 1 → ℝ} (hc : c ∈ facetTubeCoefficients σ ε) (i : Fin 1) : 0 < c i :=
  (div_pos hε (by positivity : 0 < 4 * σ)).trans_le (hc.1 i)

theorem facet_normalMatrix_scaled_gram_det {p : ℕ} (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1) (σ : ℝ) :
    ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det = σ ^ 2 := by
  rw [normalMatrix_scaled_gram_det, Matrix.det_fin_one, S.gram_diagonal hdiag 0,
    pow_one, mul_one]

theorem facet_normalMatrix_scaled_gram_isUnit {p : ℕ} (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : 0 < σ) :
    IsUnit ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det := by
  rw [facet_normalMatrix_scaled_gram_det S A hdiag]
  exact isUnit_iff_ne_zero.mpr (pow_ne_zero 2 hσ.ne')

theorem facetTube_displacement_eq {p : ℕ} (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (c : Fin 1 → ℝ) :
    projectionEuclideanVector ((normalMatrix S (σ • A)).mulVec c) =
      (σ * c 0) • euclideanNormal A (S.face 0) := by
  ext j
  change ((normalMatrix S (σ • A)).mulVec c) j =
    (σ * c 0) * (signedRowNormal A (S.face 0)) j
  simp only [normalMatrix, Matrix.mulVec, dotProduct, Fin.sum_univ_one,
    Matrix.smul_apply, smul_eq_mul, signedRowNormal]
  ring

theorem facetTubeCoefficients_displacement_le {p : ℕ} (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ ε : ℝ} (hσ : 0 < σ) (hε : 0 ≤ ε) {c : Fin 1 → ℝ}
    (hc : c ∈ facetTubeCoefficients σ ε) :
    ‖projectionEuclideanVector ((normalMatrix S (σ • A)).mulVec c)‖ ≤ ε := by
  have hc0 : 0 ≤ c 0 := (div_nonneg hε (by positivity : 0 ≤ 4 * σ)).trans (hc.1 0)
  rw [facetTube_displacement_eq, norm_smul, euclideanNormal_unit A hdiag,
    Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hσ.le hc0), mul_one]
  have hh := mul_le_mul_of_nonneg_left (hc.2 0) hσ.le
  have heq : σ * (ε / (2 * σ)) = ε / 2 := by
    field_simp
    ring
  rw [heq] at hh
  linarith

theorem activeFaces_singleton {p : ℕ} (S : CompatibleFaceTuple p 1) :
    activeFaces S = {S.face 0} := by
  ext f
  simp only [activeFaces, Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    exact congrArg S.face (Subsingleton.elim i 0)
  · intro hf
    exact ⟨0, hf.symm⟩

theorem gammaFaceKernel_singleton {p : ℕ} (a : ℕ) (S : CompatibleFaceTuple p 1)
    (s : FaceSmoother p) (x : Vector p) :
    gammaFaceKernel a (s.weights x) (activeFaces S) = s.F x ^ (a + 1) * s.pi x (S.face 0) := by
  rw [gammaFaceKernel, activeFaces_singleton, Finset.prod_singleton]
  rfl

/-- Actual Gamma-clock one-face transport bound on a localized source set.
All normal Gram and coefficient-volume factors are canceled explicitly. -/
theorem facet_gamma_kernel_integral_le_image_probability
    {p : ℕ} (a : ℕ) (S : CompatibleFaceTuple p 1) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (r : Vector p) {B : Set (Vector p)} (hBm : MeasurableSet B)
    {σ ε R C : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius (σ • A) z ≤ R)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (g : Vector p → ℝ) (hgm : Measurable g) (hgi : Integrable g (standardGaussian p))
    (hg0 : ∀ z, 0 ≤ g z) (hC : 0 ≤ C) (hg : ∀ z ∈ B, g z ≤ C) :
    (∫ z in B, s.F ((σ • A).mulVec z + r) ^ (a + 1) *
      s.pi ((σ • A).mulVec z + r) (S.face 0) * g z ∂standardGaussian p) ≤
      (4 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * C /
        (((a : ℝ) + 1) * σ * ε)) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r B (facetTubeCoefficients σ ε)) := by
  let μ := (standardGaussian p).prod (gammaRectangleLaw p a)
  let E := imageEventOf S s (σ • A) r B (facetTubeCoefficients σ ε)
  let J := ∫ z in B, s.F ((σ • A).mulVec z + r) ^ (a + 1) *
    s.pi ((σ • A).mulVec z + r) (S.face 0) * g z ∂standardGaussian p
  have hJ : 0 ≤ J := integral_nonneg (fun z => mul_nonneg
    (mul_nonneg (pow_nonneg (s.F_pos _).le _) ((s.weights _).pi_nonneg _)) (hg0 z))
  have hd := facet_normalMatrix_scaled_gram_isUnit S A hdiag hσ
  have hgram : 0 ≤ ((normalMatrix S (σ • A)).transpose * normalMatrix S (σ • A)).det := by
    rw [facet_normalMatrix_scaled_gram_det S A hdiag]
    positivity
  have hid := lintegral_ratioWeightOf_eq_gammaFaceKernel a S s (σ • A) r hBm
    (facetTubeCoefficients_measurable σ ε) g hgm hgi hg0 hactive hd hgram
  rw [facetTubeCoefficients_volume hσ, facet_normalMatrix_scaled_gram_det S A hdiag,
    pow_one, gamma_face_factor_one] at hid
  simp_rw [gammaFaceKernel_singleton] at hid
  have hle := lintegral_ratioWeightOf_le_exp_three_halves_mul S s (σ • A) r hBm
    (facetTubeCoefficients_measurable σ ε) hd (by norm_num) (by norm_num)
    hR hε.le hε1 hRε hB
    (fun c hc => facetTubeCoefficients_displacement_le S A hdiag hσ hε.le hc)
    g hC hg μ
  rw [hid] at hle
  have hfin : ENNReal.ofReal (Real.exp ((3 : ℝ) / 2) * C) * μ E ≠ ∞ := by
    dsimp [μ]
    finiteness
  have hh := ENNReal.toReal_mono hfin hle
  change (ENNReal.ofReal (ε / (4 * σ)) *
    ENNReal.ofReal ((σ ^ 2 / s.bandwidth) * ((a : ℝ) + 1) * J)).toReal ≤
      (ENNReal.ofReal (Real.exp ((3 : ℝ) / 2) * C) * μ E).toReal at hh
  have hv0 : 0 ≤ ε / (4 * σ) := by positivity
  have hs0 : 0 ≤ (σ ^ 2 / s.bandwidth) * ((a : ℝ) + 1) * J := by
    exact mul_nonneg (mul_nonneg (div_nonneg (sq_nonneg _) s.bandwidth_pos.le) (by positivity)) hJ
  have hEC : 0 ≤ Real.exp ((3 : ℝ) / 2) * C := mul_nonneg (Real.exp_nonneg _) hC
  simp only [ENNReal.toReal_mul, ENNReal.toReal_ofReal hv0, ENNReal.toReal_ofReal hs0,
    ENNReal.toReal_ofReal hEC] at hh
  have hcoeff : (ε / (4 * σ)) * ((σ ^ 2 / s.bandwidth) * ((a : ℝ) + 1) * J) =
      (((a : ℝ) + 1) * σ * ε / (4 * s.bandwidth)) * J := by
    field_simp [hσ.ne', s.bandwidth_pos.ne']
    ring
  rw [hcoeff] at hh
  have hcpos : 0 < ((a : ℝ) + 1) * σ * ε / (4 * s.bandwidth) := by
    exact div_pos (mul_pos (mul_pos (by positivity) hσ) hε)
      (mul_pos (by norm_num) s.bandwidth_pos)
  calc
    J ≤ (Real.exp ((3 : ℝ) / 2) * C * (μ E).toReal) /
        (((a : ℝ) + 1) * σ * ε / (4 * s.bandwidth)) :=
      (le_div_iff₀ hcpos).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by
      change _ = (4 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * C /
        (((a : ℝ) + 1) * σ * ε)) * (μ E).toReal
      have ha : (a : ℝ) + 1 ≠ 0 := by positivity
      field_simp [hσ.ne', hε.ne', s.bandwidth_pos.ne', ha]
      ring

/-- The nonnegative one-face Hermite penalty used by the signed surface
formula, localized by the common four-face projection radius. -/
def facetSurfacePenalty {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (z : Vector p) : ℝ :=
  1 + fourFaceProjectionRadius A z ^ 2

theorem facetHermite_abs_le_penalty {p : ℕ} (S : CompatibleFaceTuple p 1)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {σ : ℝ} (hσ : σ ≠ 0) (z : Vector p) :
    |faceDot (signedRowNormal A (S.face 0)) z ^ 2 - 1| ≤ facetSurfacePenalty (σ • A) z := by
  have hu : euclideanNormal A (S.face 0) ∈ S.normalSpan (σ • A) := by
    rw [normalSpan_smul S A hσ]
    exact Submodule.subset_span ⟨0, rfl⟩
  have hb := unit_active_span_coordinate_le S (σ • A) (by norm_num) (by norm_num)
    (euclideanNormal A (S.face 0)) hu (euclideanNormal_unit A hdiag _) z
  have heq : ⟪euclideanNormal A (S.face 0), projectionEuclideanVector z⟫_ℝ =
      faceDot (signedRowNormal A (S.face 0)) z := by
    simp [euclideanNormal, projectionEuclideanVector, PiLp.inner_apply, faceDot, mul_comm]
  rw [heq] at hb
  have hs : faceDot (signedRowNormal A (S.face 0)) z ^ 2 ≤
      fourFaceProjectionRadius (σ • A) z ^ 2 := by
    simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hb 2
  calc
    _ ≤ |faceDot (signedRowNormal A (S.face 0)) z ^ 2| + |(1 : ℝ)| := abs_sub _ _
    _ = faceDot (signedRowNormal A (S.face 0)) z ^ 2 + 1 := by
      rw [abs_of_nonneg (sq_nonneg _), abs_one]
    _ ≤ facetSurfacePenalty (σ • A) z := by
      dsimp [facetSurfacePenalty]
      linarith

theorem facetSurfacePenalty_integrable {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) : Integrable (facetSurfacePenalty A) (standardGaussian p) := by
  have hi := (integrable_fourFaceProjectionRadius_moment hp A 2).1
  apply hi.mono'
    ((measurable_const.add ((measurable_fourFaceProjectionRadius A).pow_const 2)).aestronglyMeasurable)
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    nlinarith [fourFaceProjectionRadius_nonneg A z]

/-- Actual per-shell facet estimate with its retained Gamma factor `a+1`.
The right-hand event is the genuine image in the common experiment. -/
theorem facet_surface_shell_le_image_probability
    {p : ℕ} (hp : 1 ≤ p) (a : ℕ) (S : CompatibleFaceTuple p 1) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (r : Vector p) {B : Set (Vector p)} (hBm : MeasurableSet B)
    {σ ε R : ℝ} (hσ : 0 < σ) (hε : 0 < ε) (hR : 0 ≤ R)
    (hε1 : ε ≤ 1) (hRε : R * ε ≤ 1)
    (hB : ∀ z ∈ B, fourFaceProjectionRadius (σ • A) z ≤ R)
    (hactive : ∀ i, S.face i ∈ s.faces) :
    (∫ z in B, s.F ((σ • A).mulVec z + r) ^ (a + 1) *
      s.pi ((σ • A).mulVec z + r) (S.face 0) *
        (1 + fourFaceProjectionRadius (σ • A) z ^ 2) ∂standardGaussian p) ≤
      (4 * Real.exp ((3 : ℝ) / 2) * s.bandwidth * (1 + R ^ 2) /
        (((a : ℝ) + 1) * σ * ε)) *
        ((standardGaussian p).prod (gammaRectangleLaw p a)).real
          (imageEventOf S s (σ • A) r B (facetTubeCoefficients σ ε)) := by
  apply facet_gamma_kernel_integral_le_image_probability a S s A hdiag r hBm
    hσ hε hR hε1 hRε hB hactive (facetSurfacePenalty (σ • A))
    (measurable_const.add ((measurable_fourFaceProjectionRadius _).pow_const 2))
    (facetSurfacePenalty_integrable hp _) (fun z => by dsimp [facetSurfacePenalty]; positivity)
    (by positivity)
  intro z hz
  dsimp [facetSurfacePenalty]
  nlinarith [hB z hz, fourFaceProjectionRadius_nonneg (σ • A) z]

end
end RectangleCLT.Companion.SignedSurface
