import RectangleCLTCompanion.SignedSurfaceScoreExpansion
import RectangleCLTCompanion.SignedSurfacePairBound
import RectangleCLTCompanion.SignedSurfaceFacetTube
import RectangleCLTCompanion.SignedSurfaceIndexing
import RectangleCLTCompanion.SignedSurfacePowerMajorant

/-! Actual averaging over an arbitrary independent base probability law.
Gaussian polynomial domination discharges all joint integrability; the base
law itself needs no moment assumption. -/

open MeasureTheory
open RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {p : ℕ} (μ : Measure (Vector p)) [IsProbabilityMeasure μ]

/-- The true product-law kernel is integrable on every measurable Gaussian
source subset, uniformly over an arbitrary base probability law. -/
theorem integrable_averaged_gamma_kernel (s : FaceSmoother p) (a : ℕ)
    (S : Finset (Face p)) (A : Matrix (Fin p) (Fin p) ℝ)
    (g : Vector p → ℝ) (hg : Integrable g (standardGaussian p)) (B : Set (Vector p)) :
    Integrable (fun rz : Vector p × Vector p =>
      gammaFaceKernel a (s.weights (A.mulVec rz.2 + rz.1)) S * g rz.2)
        (μ.prod ((standardGaussian p).restrict B)) := by
  have hgB : Integrable g ((standardGaussian p).restrict B) := hg.mono_measure Measure.restrict_le_self
  have hprod : Integrable (fun rz : Vector p × Vector p => g rz.2)
      (μ.prod ((standardGaussian p).restrict B)) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Vector p => (1 : ℝ)) μ).mul_prod hgB
  have hw : Continuous (fun rz : Vector p × Vector p =>
      gammaFaceKernel a (s.weights (A.mulVec rz.2 + rz.1)) S) :=
    (continuous_gammaFaceKernel s a S).comp (by fun_prop)
  exact hprod.bdd_mul hw.aestronglyMeasurable ⟨1, fun rz => by
    rw [Real.norm_eq_abs, abs_of_nonneg (gammaFaceKernel_nonneg _ _ _)]
    exact gammaFaceKernel_le_one _ _ _⟩

theorem integrable_base_gamma_kernel_integral (s : FaceSmoother p) (a : ℕ)
    (S : Finset (Face p)) (A : Matrix (Fin p) (Fin p) ℝ)
    (g : Vector p → ℝ) (hg : Integrable g (standardGaussian p)) (B : Set (Vector p)) :
    Integrable (fun r => ∫ z in B,
      gammaFaceKernel a (s.weights (A.mulVec z + r)) S * g z ∂standardGaussian p) μ :=
  (integrable_averaged_gamma_kernel μ s a S A g hg B).integral_prod_left

/-- Countable source-shell summation commutes with actual base averaging,
proved by partitioning the product probability space itself. -/
theorem averaged_gamma_kernel_hasSum_dyadicShell (s : FaceSmoother p) (a : ℕ)
    (S : Finset (Face p)) (A : Matrix (Fin p) (Fin p) ℝ)
    (g : Vector p → ℝ) (hg : Integrable g (standardGaussian p)) :
    HasSum (fun n => ∫ r, ∫ z in dyadicShell (fourFaceProjectionRadius A) n,
        gammaFaceKernel a (s.weights (A.mulVec z + r)) S * g z ∂standardGaussian p ∂μ)
      (∫ r, ∫ z, gammaFaceKernel a (s.weights (A.mulVec z + r)) S * g z
        ∂standardGaussian p ∂μ) := by
  let F : Vector p × Vector p → ℝ := fun rz =>
    gammaFaceKernel a (s.weights (A.mulVec rz.2 + rz.1)) S * g rz.2
  have hF : Integrable F (μ.prod (standardGaussian p)) := by
    simpa only [Measure.restrict_univ] using integrable_averaged_gamma_kernel μ s a S A g hg Set.univ
  have hs := hasSum_integral_dyadicShell (μ.prod (standardGaussian p))
    (fun rz => fourFaceProjectionRadius A rz.2)
    ((measurable_fourFaceProjectionRadius A).comp measurable_snd) F hF
  have hset (n : ℕ) : dyadicShell (fun rz : Vector p × Vector p => fourFaceProjectionRadius A rz.2) n =
      Set.univ ×ˢ dyadicShell (fourFaceProjectionRadius A) n := by
    ext rz
    simp only [dyadicShell, Set.mem_setOf_eq, Set.mem_prod, Set.mem_univ, true_and]
  have hint (n : ℕ) : (∫ rz in dyadicShell
      (fun rz : Vector p × Vector p => fourFaceProjectionRadius A rz.2) n, F rz
        ∂μ.prod (standardGaussian p)) =
      ∫ r, ∫ z in dyadicShell (fourFaceProjectionRadius A) n,
        gammaFaceKernel a (s.weights (A.mulVec z + r)) S * g z ∂standardGaussian p ∂μ := by
    rw [hset, setIntegral_prod F hF.integrableOn]
    simp only [Measure.restrict_univ, F]
  have hfull : (∫ rz, F rz ∂μ.prod (standardGaussian p)) =
      ∫ r, ∫ z, gammaFaceKernel a (s.weights (A.mulVec z + r)) S * g z
        ∂standardGaussian p ∂μ := integral_prod _ hF
  simpa only [hint, hfull] using hs

theorem integrable_pairSurfacePenalty_base (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (B : Set (Vector p)) :
    Integrable (fun r => pairSurfacePenalty a S s A σ r B) μ := by
  have hK : Integrable (fourFaceProjectionRadius (σ • A)) (standardGaussian p) := by
    have hi := (integrable_fourFaceProjectionRadius_moment hp (σ • A) 1).1.sub (integrable_const (1 : ℝ))
    convert hi using 1
    funext z
    simp
  have hi := integrable_base_gamma_kernel_integral μ s a (activeFaces S) (σ • A) _ hK B
  simpa only [pairSurfacePenalty, pairShellMoment, mul_assoc] using
    hi.const_mul ((((a : ℝ) + 2) * σ / s.bandwidth) *
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
      Real.sqrt (S.gram (A * A.transpose)).det)

theorem averaged_pairSurfacePenalty_hasSum_dyadicShell (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) :
    HasSum (fun n => ∫ r, pairSurfacePenalty a S s A σ r
      (dyadicShell (fourFaceProjectionRadius (σ • A)) n) ∂μ)
      (∫ r, pairSurfacePenalty a S s A σ r Set.univ ∂μ) := by
  have hK : Integrable (fourFaceProjectionRadius (σ • A)) (standardGaussian p) := by
    have hi := (integrable_fourFaceProjectionRadius_moment hp (σ • A) 1).1.sub (integrable_const (1 : ℝ))
    convert hi using 1
    funext z
    simp
  have hs := (averaged_gamma_kernel_hasSum_dyadicShell μ s a (activeFaces S) (σ • A) _ hK).mul_left
    ((((a : ℝ) + 2) * σ / s.bandwidth) *
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
      Real.sqrt (S.gram (A * A.transpose)).det)
  simpa only [pairSurfacePenalty, pairShellMoment, integral_const_mul, Measure.restrict_univ,
    mul_assoc] using hs


theorem integrable_facetSurfaceMoment_base (hp : 1 ≤ p) (a : ℕ) (f : Face p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (B : Set (Vector p)) :
    Integrable (fun r => facetSurfaceMoment a f s A σ r B) μ := by
  have hi := integrable_base_gamma_kernel_integral μ s a {f} (σ • A)
    (facetSurfacePenalty (σ • A)) (facetSurfacePenalty_integrable hp _) B
  convert hi using 1
  funext r
  apply integral_congr_ae
  exact ae_of_all _ fun z => by
    dsimp only
    rw [softFacePower_eq_Fpow_pi]
    simp only [gammaFaceKernel, Finset.prod_singleton]
    rfl

theorem averaged_facetSurfaceMoment_hasSum_dyadicShell (hp : 1 ≤ p) (a : ℕ)
    (f : Face p) (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) :
    HasSum (fun n => ∫ r, facetSurfaceMoment a f s A σ r
      (dyadicShell (fourFaceProjectionRadius (σ • A)) n) ∂μ)
      (∫ r, facetSurfaceMoment a f s A σ r Set.univ ∂μ) := by
  have hs := averaged_gamma_kernel_hasSum_dyadicShell μ s a {f} (σ • A)
    (facetSurfacePenalty (σ • A)) (facetSurfacePenalty_integrable hp _)
  simpa only [facetSurfaceMoment, softFacePower_eq_Fpow_pi, gammaFaceKernel,
    Finset.prod_singleton, FaceSmoother.F, FaceSmoother.pi, Measure.restrict_univ] using hs

/-- The actual positive full surface majorant at a fixed base point and
source subset. -/
def surfaceMomentOn (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p)) : ℝ :=
  (∑ f ∈ s.faces, facetSurfaceMoment a f s A σ r B) +
    ∑ T : NondegenerateFacePairs s.faces A, pairSurfacePenalty a T.tuple s A σ r B

def averagedSurfaceMomentOn (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (B : Set (Vector p)) : ℝ :=
  ∫ r, surfaceMomentOn s a A σ r B ∂μ

def averagedSurfaceShell (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (n : ℕ) : ℝ :=
  averagedSurfaceMomentOn μ s a A σ (dyadicShell (fourFaceProjectionRadius (σ • A)) n)

def averagedSurfaceMoment (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) : ℝ :=
  averagedSurfaceMomentOn μ s a A σ Set.univ

theorem integrable_surfaceMomentOn_base (hp : 1 ≤ p) (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (B : Set (Vector p)) :
    Integrable (fun r => surfaceMomentOn s a A σ r B) μ := by
  classical
  exact (integrable_finset_sum s.faces (fun f _ =>
    integrable_facetSurfaceMoment_base μ hp a f s A σ B)).add
      (integrable_finset_sum Finset.univ (fun T _ =>
        integrable_pairSurfacePenalty_base μ hp a T.tuple s A σ B))

theorem averagedSurfaceMomentOn_eq_sum_integrals (hp : 1 ≤ p) (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (B : Set (Vector p)) :
    averagedSurfaceMomentOn μ s a A σ B =
      (∑ f ∈ s.faces, ∫ r, facetSurfaceMoment a f s A σ r B ∂μ) +
        ∑ T : NondegenerateFacePairs s.faces A, ∫ r, pairSurfacePenalty a T.tuple s A σ r B ∂μ := by
  classical
  unfold averagedSurfaceMomentOn surfaceMomentOn
  rw [integral_add
    (integrable_finset_sum s.faces (fun f _ => integrable_facetSurfaceMoment_base μ hp a f s A σ B))
    (integrable_finset_sum Finset.univ (fun T _ => integrable_pairSurfacePenalty_base μ hp a T.tuple s A σ B)),
    integral_finset_sum _ (fun f _ => integrable_facetSurfaceMoment_base μ hp a f s A σ B),
    integral_finset_sum _ (fun T _ => integrable_pairSurfacePenalty_base μ hp a T.tuple s A σ B)]

theorem averagedSurfaceShell_hasSum (hp : 1 ≤ p) (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) :
    HasSum (averagedSurfaceShell μ s a A σ) (averagedSurfaceMoment μ s a A σ) := by
  classical
  have hf := hasSum_sum (s := s.faces) (fun f _ =>
    averaged_facetSurfaceMoment_hasSum_dyadicShell μ hp a f s A σ)
  have hpairs := hasSum_sum (s := (Finset.univ : Finset (NondegenerateFacePairs s.faces A)))
    (fun T _ => averaged_pairSurfacePenalty_hasSum_dyadicShell μ hp a T.tuple s A σ)
  convert hf.add hpairs using 1
  · funext n
    exact averagedSurfaceMomentOn_eq_sum_integrals μ hp s a A σ _
  · exact averagedSurfaceMomentOn_eq_sum_integrals μ hp s a A σ _

omit [IsProbabilityMeasure μ] in
theorem averagedSurfaceShell_nonneg (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : 0 ≤ σ) (n : ℕ) :
    0 ≤ averagedSurfaceShell μ s a A σ n := by
  apply integral_nonneg
  intro r
  apply add_nonneg
  · exact Finset.sum_nonneg (fun f _ => facetSurfaceMoment_nonneg a f s A σ r _)
  · exact Finset.sum_nonneg (fun T _ => pairSurfacePenalty_nonneg a T.tuple s A hσ r _)

/-- The signed power score is bounded by the genuine averaged positive
surface majorant. No moment or density assumption on the base is needed. -/
theorem abs_averagedGaussianPowerTrace_le_surfaceMoment (hp : 1 ≤ p)
    (s : FaceSmoother p) (a : ℕ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {σ : ℝ} (hσ : 0 < σ) :
    |averagedGaussianPowerTrace μ s (σ • A) a| ≤ averagedSurfaceMoment μ s a A σ := by
  rw [averagedGaussianPowerTrace_eq_integral]
  exact abs_integral_le_integral_abs.trans (integral_mono
    (integrable_gaussianPowerTrace_base μ s (σ • A) a).abs
    (integrable_surfaceMomentOn_base μ hp s a A σ Set.univ)
    (fun r => abs_gaussianPowerTrace_le_surface_penalties hp s a A hdiag hσ r))

end
end RectangleCLT.Companion.SignedSurface
