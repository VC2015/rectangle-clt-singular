import RectangleCLTCompanion.SelectorEntropy

/-! The actual selector matrix reduction, with covariance contraction
discharged by the checked Prékopa theorem. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- No covariance-contraction or mass hypothesis is needed for the actual
selector. Coefficients are controlled by their quadratic forms. -/
theorem selectorWeight_trace_reduction {p k r : ℕ}
    (s : FaceSmoother p) (faces : Fin k → Face p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (B : Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hB : ∀ u, |matrixQuadratic B u| ≤ b * vectorNormSq u) :
    |Matrix.trace (B * weightedScore (standardGaussian r) id
      (fun g => selectorWeight s faces (A.mulVec g + v)))| ≤
      b * (2 * weightMass (standardGaussian r)
        (fun g => selectorWeight s faces (A.mulVec g + v)) *
          vectorNormSq (weightMean (standardGaussian r) id
            (fun g => selectorWeight s faces (A.mulVec g + v))) -
          Matrix.trace (weightedScore (standardGaussian r) id
            (fun g => selectorWeight s faces (A.mulVec g + v)))) := by
  classical
  by_cases hactive : ∀ i, faces i ∈ s.faces
  · apply standardGaussian_weightedScore_reduction
      (fun g => selectorWeight s faces (A.mulVec g + v))
      (continuous_selectorWeight_affine s faces A v).measurable
      (fun g => by
        rw [abs_of_nonneg (selectorWeight_nonneg s faces _)]
        exact selectorWeight_le_one s faces _) B
      (selectorWeight_affine_mass_pos s faces hactive A v) hB
      (selectorWeight_covariance_contraction s faces hactive A v)
  · push_neg at hactive
    obtain ⟨i, hi⟩ := hactive
    have hzero (g : Vector r) : selectorWeight s faces (A.mulVec g + v) = 0 := by
      unfold selectorWeight
      have hpi : s.pi (A.mulVec g + v) (faces i) = 0 := by
        simp only [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hi, ↓reduceIte,
          zero_div]
      rw [Finset.prod_eq_zero (Finset.mem_univ i) hpi, mul_zero]
    have hz : (fun g => selectorWeight s faces (A.mulVec g + v)) = (fun _ => (0 : ℝ)) :=
      funext hzero
    rw [hz]
    have hs : weightedScore (standardGaussian r) id (fun _ => (0 : ℝ)) = 0 := by
      ext j l
      simp [weightedScore]
    rw [hs]
    simp [weightMass]

/-- Sum absolute trace pairings first, while retaining the signed trace of
the summed selectors. This is the form needed by covariance restoration. -/
theorem sum_selectorWeight_trace_reduction {p k r : ℕ}
    (s : FaceSmoother p) (S : Finset (Fin k → Face p))
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (B : (Fin k → Face p) → Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hB : ∀ α ∈ S, ∀ u, |matrixQuadratic (B α) u| ≤ b * vectorNormSq u) :
    (∑ α ∈ S, |Matrix.trace (B α * weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g + v)))|) ≤
      b * (2 * (∑ α ∈ S, weightMass (standardGaussian r)
        (fun g => selectorWeight s α (A.mulVec g + v)) *
          vectorNormSq (weightMean (standardGaussian r) id
            (fun g => selectorWeight s α (A.mulVec g + v)))) -
          ∑ α ∈ S, Matrix.trace (weightedScore (standardGaussian r) id
            (fun g => selectorWeight s α (A.mulVec g + v)))) := by
  have hh := Finset.sum_le_sum (fun α hα =>
    selectorWeight_trace_reduction s α A v (B α) (hB α hα))
  simpa only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_assoc] using hh

end
end RectangleCLT.Companion
