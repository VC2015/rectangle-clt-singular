import RectangleCLTArxivV1.SupplementalHActualRidgeEstimates

/-! The actual native surface quantities vanish for an empty polyhedron
and for the empty facet presentation. No undefined-face convention is
used to discharge a nonzero integral. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

theorem hardGaussianWeightedFacetIntegral_zero_of_empty {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m)
    (hempty : gaussianFiniteThresholdEvent Finset.univ u b=∅) :
    hardGaussianWeightedFacetIntegral u b=0 := by
  simp only [hardGaussianWeightedFacetIntegral,hardGaussianFacetIntegral,hempty,Measure.restrict_empty,
    integral_zero_measure,mul_zero,Finset.sum_const_zero]

theorem hardGaussianSignedRidgeTerm_zero_of_empty {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hempty : gaussianFiniteThresholdEvent Finset.univ u b=∅) (j l : Fin m) :
    hardGaussianSignedRidgeTerm u b j l=0 := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u j l
  · have hnot (g : Vector r) : gaussianPairBase u b j l g∉
        gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l) u b := by
      intro hg
      have hfull : gaussianPairBase u b j l g∈gaussianFiniteThresholdEvent Finset.univ u b := by
        intro k _
        by_cases hkj : k=j
        · subst k
          exact (gaussianPairBase_left_level u b j l (hu j) (hu l) hp.1 hp.2 g).le
        · by_cases hkl : k=l
          · subst k
            exact (gaussianPairBase_right_level u b j l (hu j) (hu l) hp.1 hp.2 g).le
          · exact hg k (Finset.mem_erase.mpr ⟨hkl,Finset.mem_erase.mpr ⟨hkj,Finset.mem_univ _⟩⟩)
      simpa only [hempty,mem_empty_iff_false] using hfull
    unfold hardGaussianSignedRidgeTerm
    rw [if_pos hp]
    unfold hardGaussianPairSignedSection
    have he : (fun g => (gaussianFiniteThresholdEvent ((Finset.univ.erase j).erase l) u b).indicator
        (fun x => vectorNormSq x-(r:ℝ))
        (gaussianPairSectionPoint (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) g))=fun _ => (0:ℝ) := by
      funext g
      exact indicator_of_not_mem (hnot g) _
    rw [he,integral_zero,mul_zero]
  · simp only [hardGaussianSignedRidgeTerm,hp,if_false]

theorem hardGaussianWeightedRidgeIntegral_zero_of_empty {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hempty : gaussianFiniteThresholdEvent Finset.univ u b=∅) :
    hardGaussianWeightedRidgeIntegral u b=0 := by
  unfold hardGaussianWeightedRidgeIntegral
  simp only [hardGaussianSignedRidgeTerm_zero_of_empty u b hu hempty,Finset.sum_const_zero,mul_zero]

theorem gaussianFiniteThresholdEvent_affine_empty {m r : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (hempty : gaussianFiniteThresholdEvent Finset.univ u a=∅)
    (x : Vector r) {σ : ℝ} (hσ : 0<σ) :
    gaussianFiniteThresholdEvent Finset.univ u (fun k => (a k-faceDot (u k) x)/σ)=∅ := by
  apply eq_empty_iff_forall_not_mem.mpr
  intro g hg
  have hfull : x+σ • g∈gaussianFiniteThresholdEvent Finset.univ u a := by
    intro k _
    have hh := (le_div_iff₀ hσ).mp (hg k (Finset.mem_univ _))
    rw [threshold_faceDot_add_right,threshold_faceDot_smul_right]
    nlinarith
  simpa only [hempty,mem_empty_iff_false] using hfull

theorem hardGaussianSurfaceIntegrals_zero_empty_presentation {n : ℕ}
    (u : Fin 0 → Vector (n+1)) (b : Vector 0) :
    hardGaussianWeightedFacetIntegral u b=0 ∧ hardGaussianWeightedRidgeIntegral u b=0 := by
  simp [hardGaussianWeightedFacetIntegral,hardGaussianWeightedRidgeIntegral]

end
end RectangleCLTArxivV1
