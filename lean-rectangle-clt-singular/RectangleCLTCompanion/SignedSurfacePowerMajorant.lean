import RectangleCLTCompanion.SignedSurfaceScoreExpansion
import RectangleCLTCompanion.SignedSurfaceIndexing
import RectangleCLTCompanion.SignedSurfaceFacetTube
import RectangleCLTCompanion.SignedSurfacePairBound
import RectangleCLTCompanion.SignedSurfaceShells

/-! An actual positive-kernel majorant for the signed Gaussian power score.
The proof retains the paired ridge cancellation and removes degenerate
pairs exactly, before using the common projection radius. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

variable {p : ℕ}

def singletonFaceTuple (f : Face p) : CompatibleFaceTuple p 1 where
  face := fun _ => f
  coordinate_injective := fun _ _ _ => Subsingleton.elim _ _

theorem softFacePower_eq_Fpow_pi (s : FaceSmoother p) (a : ℕ) (f : Face p) (x : Vector p) :
    softFacePower s a f x = s.F x ^ (a + 1) * s.pi x f := by
  simp only [softFacePower, FaceSmoother.softFaceWeight, Finset.prod_singleton, pow_succ]
  exact (mul_assoc _ _ _).symm

/-- The exact nonnegative facet kernel controlled by the one-face tube. -/
def facetSurfaceMoment (a : ℕ) (f : Face p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p)) : ℝ :=
  ∫ z in B, softFacePower s a f ((σ • A).mulVec z + r) *
    facetSurfacePenalty (σ • A) z ∂standardGaussian p

theorem facetSurfaceMoment_eq_Fpow_pi (a : ℕ) (f : Face p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p)) :
    facetSurfaceMoment a f s A σ r B =
      ∫ z in B, s.F ((σ • A).mulVec z + r) ^ (a + 1) *
        s.pi ((σ • A).mulVec z + r) f *
          (1 + fourFaceProjectionRadius (σ • A) z ^ 2) ∂standardGaussian p := by
  simp only [facetSurfaceMoment, softFacePower_eq_Fpow_pi, facetSurfacePenalty]

theorem facetSurfaceMoment_nonneg (a : ℕ) (f : Face p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p)) :
    0 ≤ facetSurfaceMoment a f s A σ r B := by
  apply integral_nonneg
  intro z
  exact mul_nonneg (softFacePower_nonneg _ _ _ _) (by dsimp [facetSurfacePenalty]; positivity)

theorem integrable_facetSurfaceMoment_kernel (hp : 1 ≤ p) (a : ℕ) (f : Face p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) :
    Integrable (fun z => softFacePower s a f ((σ • A).mulVec z + r) *
      facetSurfacePenalty (σ • A) z) (standardGaussian p) := by
  simpa only [mul_comm] using integrable_gaussian_softFacePower_mul s a f (σ • A) r
    (facetSurfacePenalty_integrable hp (σ • A))

theorem signedSurfaceRadius_integrable (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    Integrable (fourFaceProjectionRadius A) (standardGaussian p) := by
  have hi := (integrable_fourFaceProjectionRadius_moment hp A 1).1.sub
    (integrable_const (1 : ℝ))
  convert hi using 1
  funext z
  simp

/-- Every actual Gamma face kernel is bounded by one, so the required
radius-weighted Gaussian moment is integrable without a covariance gap. -/
theorem integrable_pairShellMoment_kernel (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) :
    Integrable (fun z => gammaFaceKernel a (s.weights ((σ • A).mulVec z + r)) (activeFaces S) *
      fourFaceProjectionRadius (σ • A) z) (standardGaussian p) := by
  have hw : Continuous (fun z => gammaFaceKernel a (s.weights ((σ • A).mulVec z + r))
      (activeFaces S)) := (continuous_gammaFaceKernel s a _).comp (by fun_prop)
  exact (signedSurfaceRadius_integrable hp (σ • A)).bdd_mul hw.aestronglyMeasurable
    ⟨1, fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (gammaFaceKernel_nonneg _ _ _)]
      exact gammaFaceKernel_le_one _ _ _⟩

theorem activeFaces_pair (S : CompatibleFaceTuple p 2) :
    activeFaces S = {S.face 0, S.face 1} := by
  classical
  ext f
  simp only [activeFaces, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem gammaFaceKernel_pair (a : ℕ) (S : CompatibleFaceTuple p 2)
    (s : FaceSmoother p) (x : Vector p) :
    gammaFaceKernel a (s.weights x) (activeFaces S) =
      softFacePower s a (S.face 0) x * (s.weights x).pi (S.face 1) := by
  classical
  have hne : S.face 0 ≠ S.face 1 := by
    intro hh
    exact (by decide : (0 : Fin 2) ≠ 1) (S.coordinate_injective (congrArg Prod.fst hh))
  rw [gammaFaceKernel, activeFaces_pair, Finset.prod_insert (by simpa using hne),
    Finset.prod_singleton, softFacePower_eq_Fpow_pi]
  exact (mul_assoc _ _ _).symm

theorem pairSurfacePenalty_nonneg (a : ℕ) (S : CompatibleFaceTuple p 2)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) {σ : ℝ} (hσ : 0 ≤ σ)
    (r : Vector p) (B : Set (Vector p)) : 0 ≤ pairSurfacePenalty a S s A σ r B := by
  unfold pairSurfacePenalty
  exact mul_nonneg (mul_nonneg (mul_nonneg (div_nonneg (mul_nonneg (by positivity) hσ)
    s.bandwidth_pos.le) (norm_nonneg _)) (Real.sqrt_nonneg _))
      (pairShellMoment_nonneg _ _ _ _ _ _ _)

theorem facetSurfaceMoment_eq_zero_of_missing (a : ℕ) (f : Face p) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p))
    (hf : f ∉ s.faces) : facetSurfaceMoment a f s A σ r B = 0 := by
  simp only [facetSurfaceMoment, softFacePower_eq_zero_of_missing s a f _ hf,
    zero_mul, integral_zero]

theorem sum_facetSurfaceMoment_eq_faces (a : ℕ) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) (B : Set (Vector p)) :
    (∑ f : Face p, facetSurfaceMoment a f s A σ r B) =
      ∑ f ∈ s.faces, facetSurfaceMoment a f s A σ r B := by
  classical
  apply Eq.symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro f _ hf
  exact facetSurfaceMoment_eq_zero_of_missing a f s A σ r B hf

/-- The signed power score is controlled by genuine positive facet and
nondegenerate paired-ridge kernels. All angular cancellation precedes the
absolute value, and no covariance eigenvalue lower bound is used. -/
theorem abs_gaussianPowerTrace_le_surface_penalties (hp : 1 ≤ p)
    (s : FaceSmoother p) (a : ℕ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) {σ : ℝ} (hσ : 0 < σ) (r : Vector p) :
    |gaussianPowerTrace s (σ • A) r a| ≤
      (∑ f ∈ s.faces, facetSurfaceMoment a f s A σ r Set.univ) +
        ∑ T : NondegenerateFacePairs s.faces A,
          pairSurfacePenalty a T.tuple s A σ r Set.univ := by
  classical
  let Y := fun z => (σ • A).mulVec z + r
  let Facet := fun z => ∑ f : Face p, (faceDot (signedRowNormal A f) z ^ 2 - 1) *
    softFacePower s a f (Y z)
  let Raw := fun z => ∑ f : Face p, ∑ k : Face p, pairedRidgeKernel s a A (Y z) z f k
  let Fpos := fun z => ∑ f : Face p,
    softFacePower s a f (Y z) * facetSurfacePenalty (σ • A) z
  let d := fun T : NondegenerateFacePairs s.faces A =>
    ‖euclideanNormal A (T.tuple.face 0) - euclideanNormal A (T.tuple.face 1)‖ *
      Real.sqrt (T.tuple.gram (A * A.transpose)).det
  let G := fun (T : NondegenerateFacePairs s.faces A) z =>
    gammaFaceKernel a (s.weights (Y z)) (activeFaces T.tuple) *
      fourFaceProjectionRadius (σ • A) z
  let Rpos := fun z => ∑ T : NondegenerateFacePairs s.faces A, d T * G T z
  let C := ((a : ℝ) + 2) * σ / s.bandwidth
  have hC : 0 ≤ C := div_nonneg (mul_nonneg (by positivity) hσ.le) s.bandwidth_pos.le
  have hfint : Integrable Fpos (standardGaussian p) :=
    integrable_finset_sum _ (fun f _ => integrable_facetSurfaceMoment_kernel hp a f s A σ r)
  have hrint : Integrable Rpos (standardGaussian p) :=
    integrable_finset_sum _ (fun T _ =>
      (integrable_pairShellMoment_kernel hp a T.tuple s A σ r).const_mul (d T))
  have hfacet (z : Vector p) : |Facet z| ≤ Fpos z := by
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro f _
    rw [abs_mul, abs_of_nonneg (softFacePower_nonneg _ _ _ _)]
    have hb := facetHermite_abs_le_penalty (singletonFaceTuple f) A hdiag hσ.ne' z
    exact (mul_le_mul_of_nonneg_right hb (softFacePower_nonneg _ _ _ _)).trans_eq
      (mul_comm _ _)
  have hraw (z : Vector p) : |Raw z| ≤ 2 * Rpos z := by
    calc
      _ ≤ ∑ f : Face p, ∑ k : Face p, |pairedRidgeKernel s a A (Y z) z f k| :=
        (Finset.abs_sum_le_sum_abs _ _).trans
          (Finset.sum_le_sum (fun _ _ => Finset.abs_sum_le_sum_abs _ _))
      _ = 2 * ∑ T : NondegenerateFacePairs s.faces A,
          softFacePower s a (T.tuple.face 0) (Y z) *
            (s.weights (Y z)).pi (T.tuple.face 1) * |pairRidgeNumerator T.tuple A z| :=
        sum_abs_pairedRidgeKernel_eq_two_nondegenerate s a A hdiag (Y z) z
      _ ≤ 2 * Rpos z := by
        apply mul_le_mul_of_nonneg_left _ (by norm_num)
        apply Finset.sum_le_sum
        intro T _
        have hb := pairRidgeNumerator_abs_le_radius T.tuple A hdiag T.tuple_det_pos hσ.ne' z
        have hw := mul_nonneg (softFacePower_nonneg s a (T.tuple.face 0) (Y z))
          ((s.weights (Y z)).pi_nonneg (T.tuple.face 1))
        calc
          _ ≤ (softFacePower s a (T.tuple.face 0) (Y z) *
              (s.weights (Y z)).pi (T.tuple.face 1)) *
              (d T * fourFaceProjectionRadius (σ • A) z) :=
            mul_le_mul_of_nonneg_left hb hw
          _ = d T * G T z := by
            dsimp only [G]
            rw [gammaFaceKernel_pair]
            ring
  have hP (f : Face p) : Continuous (fun z => softFacePower s a f ((σ • A).mulVec z + r)) :=
    (continuous_softFacePower s a f).comp (by fun_prop)
  have hdot (f : Face p) : Continuous (fun z => faceDot (signedRowNormal A f) z) :=
    continuous_finset_sum _ (fun j _ => continuous_const.mul (continuous_apply j))
  have hpi (f : Face p) : Continuous (fun z => (s.weights ((σ • A).mulVec z + r)).pi f) :=
    (s.continuous_pi f).comp (by fun_prop)
  have hfacetint : Integrable Facet (standardGaussian p) := by
    apply hfint.mono' _ (ae_of_all _ (fun z => ?_))
    · apply Continuous.aestronglyMeasurable
      exact continuous_finset_sum _ (fun f _ =>
        (((hdot f).pow 2).sub continuous_const).mul (hP f))
    · simpa only [Real.norm_eq_abs] using hfacet z
  have hrawint : Integrable Raw (standardGaussian p) := by
    apply (hrint.const_mul 2).mono' _ (ae_of_all _ (fun z => ?_))
    · apply Continuous.aestronglyMeasurable
      exact continuous_finset_sum _ (fun f _ => continuous_finset_sum _ (fun k _ =>
        ((hP f).mul (hpi k)).mul (continuous_const.mul ((hdot f).add (hdot k)))))
    · simpa only [Real.norm_eq_abs, Pi.smul_apply, smul_eq_mul] using hraw z
  have hIfacet : |∫ z, Facet z ∂standardGaussian p| ≤ ∫ z, Fpos z ∂standardGaussian p :=
    abs_integral_le_integral_abs.trans (integral_mono hfacetint.abs hfint hfacet)
  have hIraw : |∫ z, Raw z ∂standardGaussian p| ≤ 2 * ∫ z, Rpos z ∂standardGaussian p := by
    calc
      _ ≤ ∫ z, |Raw z| ∂standardGaussian p := abs_integral_le_integral_abs
      _ ≤ ∫ z, 2 * Rpos z ∂standardGaussian p := integral_mono hrawint.abs (hrint.const_mul 2) hraw
      _ = _ := integral_const_mul _ _
  have hFpos : (∫ z, Fpos z ∂standardGaussian p) =
      ∑ f : Face p, facetSurfaceMoment a f s A σ r Set.univ := by
    simp only [Fpos, facetSurfaceMoment, Measure.restrict_univ, Y]
    exact integral_finset_sum _ (fun f _ => integrable_facetSurfaceMoment_kernel hp a f s A σ r)
  have hRpos : C * (∫ z, Rpos z ∂standardGaussian p) =
      ∑ T : NondegenerateFacePairs s.faces A,
        pairSurfacePenalty a T.tuple s A σ r Set.univ := by
    rw [show (∫ z, Rpos z ∂standardGaussian p) =
        ∑ T : NondegenerateFacePairs s.faces A, d T * pairShellMoment a T.tuple s A σ r Set.univ by
      rw [show Rpos = fun z => ∑ T : NondegenerateFacePairs s.faces A, d T * G T z from rfl,
        integral_finset_sum _ (fun T _ =>
          (integrable_pairShellMoment_kernel hp a T.tuple s A σ r).const_mul (d T))]
      apply Finset.sum_congr rfl
      intro T _
      simp only [integral_const_mul, G, Y, pairShellMoment, Measure.restrict_univ]]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro T _
    dsimp [pairSurfacePenalty, C, d]
    ring
  have hid : gaussianPowerTrace s (σ • A) r a =
      (∫ z, Facet z ∂standardGaussian p) - (C / 2) * (∫ z, Raw z ∂standardGaussian p) := by
    simpa only [Facet, Raw, Y, C, pairedRidgeKernel, mul_assoc] using
      gaussianPowerTrace_eq_paired_facet_ridge s a A σ r hdiag
  rw [hid]
  calc
    _ ≤ |∫ z, Facet z ∂standardGaussian p| +
        |(C / 2) * (∫ z, Raw z ∂standardGaussian p)| := abs_sub _ _
    _ = |∫ z, Facet z ∂standardGaussian p| +
        (C / 2) * |∫ z, Raw z ∂standardGaussian p| := by
      rw [abs_mul, abs_of_nonneg (div_nonneg hC (by norm_num))]
    _ ≤ (∫ z, Fpos z ∂standardGaussian p) +
        (C / 2) * (2 * ∫ z, Rpos z ∂standardGaussian p) :=
      add_le_add hIfacet (mul_le_mul_of_nonneg_left hIraw (div_nonneg hC (by norm_num)))
    _ = (∫ z, Fpos z ∂standardGaussian p) + C * (∫ z, Rpos z ∂standardGaussian p) := by ring
    _ = _ := by rw [hFpos, hRpos, sum_facetSurfaceMoment_eq_faces]

/-- Genuine convergent dyadic decomposition of the actual facet moment. -/
theorem facetSurfaceMoment_hasSum_dyadicShell (hp : 1 ≤ p) (a : ℕ) (f : Face p)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) :
    HasSum (fun n => facetSurfaceMoment a f s A σ r
      (dyadicShell (fourFaceProjectionRadius (σ • A)) n))
        (facetSurfaceMoment a f s A σ r Set.univ) := by
  simpa only [facetSurfaceMoment, Measure.restrict_univ] using
    hasSum_integral_dyadicShell (standardGaussian p) (fourFaceProjectionRadius (σ • A))
      (measurable_fourFaceProjectionRadius _) _
        (integrable_facetSurfaceMoment_kernel hp a f s A σ r)

/-- Genuine convergent dyadic decomposition of the normalized paired
surface penalty, using the same Gaussian source partition as every facet. -/
theorem pairSurfacePenalty_hasSum_dyadicShell (hp : 1 ≤ p) (a : ℕ)
    (S : CompatibleFaceTuple p 2) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (r : Vector p) :
    HasSum (fun n => pairSurfacePenalty a S s A σ r
      (dyadicShell (fourFaceProjectionRadius (σ • A)) n))
        (pairSurfacePenalty a S s A σ r Set.univ) := by
  have hh := hasSum_integral_dyadicShell (standardGaussian p) (fourFaceProjectionRadius (σ • A))
    (measurable_fourFaceProjectionRadius _) _ (integrable_pairShellMoment_kernel hp a S s A σ r)
  simpa only [pairSurfacePenalty, pairShellMoment, Measure.restrict_univ] using
    hh.mul_left ((((a : ℝ) + 2) * σ / s.bandwidth) *
      ‖euclideanNormal A (S.face 0) - euclideanNormal A (S.face 1)‖ *
        Real.sqrt (S.gram (A * A.transpose)).det)

end
end RectangleCLT.Companion.SignedSurface
