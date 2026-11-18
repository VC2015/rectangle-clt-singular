import RectangleCLTArxivV1.SupplementalHSelectorTuples

/-! Actual selector matrices in the projected-reference reduction, with
all inactive faces and every additional factor retained. Quantitative
hard-facet/ridge localization is a separate analytic step. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHSelectorMass {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p) : ℝ :=
  weightMass (standardGaussian r) (fun g => selectorWeight s α (A.mulVec g+v))

def supplementalHSelectorProjection {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p)
    (P : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  ∫ g, selectorWeight s α (A.mulVec g+v)*vectorNormSq (P.mulVec g) ∂standardGaussian r

def supplementalHSelectorEntropy {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p)
    (P : Matrix (Fin r) (Fin r) ℝ) (β : Vector r → ℝ) : ℝ :=
  supplementalHSelectorMass s A v α*
    Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/supplementalHSelectorMass s A v α)

def supplementalHSelectorRadialTrace {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p) : ℝ :=
  ∫ g, (vectorNormSq g-(r:ℝ))*selectorWeight s α (A.mulVec g+v) ∂standardGaussian r

/-- H.2's genuine selector reduction, including tuples that contain an
inactive face (whose actual weight and matrix vanish). -/
theorem supplementalH_selector_projected_reduction {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (P : Matrix (Fin r) (Fin r) ℝ)
    (hPt : P.transpose=P) (hPP : P*P=P)
    (β : Vector r → ℝ) (hβ : Measurable β)
    (hβb : ∀ x, 0 ≤ β x ∧ β x ≤ 1)
    (hdom : ∀ g, selectorWeight s α (A.mulVec g+v) ≤ β (P.mulVec g)) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α (A.mulVec g+v))) ≤
      2*supplementalHSelectorProjection s A v α P+
        4*supplementalHSelectorEntropy s A v α P β-
        supplementalHSelectorRadialTrace s A v α := by
  classical
  by_cases ha : ∀ i, α i ∈ s.faces
  · simpa only [supplementalHSelectorProjection, supplementalHSelectorEntropy,
      supplementalHSelectorMass, supplementalHSelectorRadialTrace, mul_assoc] using
      gaussian_selector_projected_matrix_bound s α ha A v P hPt hPP β hβ hβb hdom
  · cases K with
    | zero => exact False.elim (ha (fun i => Fin.elim0 i))
    | succ K =>
      have hz (g : Vector r) : selectorWeight s α (A.mulVec g+v) = 0 :=
        selectorWeight_eq_zero_of_not_active s α ha _
      simp only [supplementalHSelectorProjection, supplementalHSelectorEntropy,
        supplementalHSelectorMass, supplementalHSelectorRadialTrace, weightedScore, weightMass, hz,
        zero_mul, mul_zero, integral_zero, Real.log_zero, add_zero, sub_zero,
        Matrix.of_apply, id_eq]
      have hzero : weightedScore (standardGaussian r) id (fun _ : Vector r => (0:ℝ)) = 0 := by
        ext j l
        simp [weightedScore]
      rw [hzero, symmetricNuclearNorm_zero]

/-- Nonnegative coefficients may include the exact first-pair angle.
The tuple length is completely unrestricted. -/
theorem supplementalH_sum_weighted_selector_reduction
    {p r K : ℕ} {ι : Type*} [Fintype ι]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : ι → Fin K → Face p) (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i)
    (P : ι → Matrix (Fin r) (Fin r) ℝ)
    (hPt : ∀ i, (P i).transpose=P i) (hPP : ∀ i, P i*P i=P i)
    (β : ι → Vector r → ℝ) (hβ : ∀ i, Measurable (β i))
    (hβb : ∀ i x, 0 ≤ β i x ∧ β i x ≤ 1)
    (hdom : ∀ i g, selectorWeight s (α i) (A.mulVec g+v) ≤ β i ((P i).mulVec g)) :
    (∑ i, c i*symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s (α i) (A.mulVec g+v)))) ≤
      2*(∑ i, c i*supplementalHSelectorProjection s A v (α i) (P i))+
      4*(∑ i, c i*supplementalHSelectorEntropy s A v (α i) (P i) (β i))-
        ∑ i, c i*supplementalHSelectorRadialTrace s A v (α i) := by
  classical
  calc
    _ ≤ ∑ i, c i*(2*supplementalHSelectorProjection s A v (α i) (P i)+
        4*supplementalHSelectorEntropy s A v (α i) (P i) (β i)-
        supplementalHSelectorRadialTrace s A v (α i)) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left
        (supplementalH_selector_projected_reduction s A v (α i) (P i)
          (hPt i) (hPP i) (β i) (hβ i) (hβb i) (hdom i)) (hc i))
    _ = _ := by
      simp only [mul_sub, mul_add, Finset.sum_sub_distrib, Finset.sum_add_distrib,
        ← Finset.mul_sum]
      ring_nf
      simp only [← Finset.sum_mul]
      ring

end
end RectangleCLTArxivV1
