import RectangleCLTCompanion.SplitV4.GenericC4SeededFourthIdentity

/-! Literal coordinate correspondence for the signed cubic tensor in
Appendix B.1. The finite index `Fin 3 → Fin p` lists all ordered triples;
the signed moments are summed before their contraction with D3. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem canonicalDiagonal_eq_coordinate_sum {p k : ℕ}
    (F : Vector p → ℝ) (x v : Vector p) :
    canonicalDiagonal F k x v =
      ∑ α : Fin k → Fin p, (∏ r, v (α r))*
        iteratedFDeriv ℝ k F x (fun r => C4Test.coordinateVector (α r)) := by
  classical
  let M := (iteratedFDeriv ℝ k F x).toMultilinearMap
  have hv : v = ∑ j : Fin p, v j • C4Test.coordinateVector j := by
    ext j
    simp [C4Test.coordinateVector, Finset.sum_apply, Pi.single_apply]
  change M (fun _ => v) = _
  conv_lhs => rw [hv]
  rw [M.map_sum (fun (_ : Fin k) (j : Fin p) => v j • C4Test.coordinateVector j)]
  simp only [M.map_smul_univ, smul_eq_mul]
  rfl

def signedCubicTensor {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (α : Fin 3 → Fin p) : ℝ :=
  ∑ i, ∫ ω, (∏ r : Fin 3, ξ i ω (α r)) ∂μ

def canonicalSignedCubicContraction {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p) (x : Vector p) : ℝ :=
  ∑ α : Fin 3 → Fin p, signedCubicTensor μ ξ α *
    iteratedFDeriv ℝ 3 F x (fun r => C4Test.coordinateVector (α r))

theorem signedCubicTensor_triple {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (j k l : Fin p) :
    signedCubicTensor μ ξ ![j,k,l] =
      ∑ i, ∫ ω, ξ i ω j*ξ i ω k*ξ i ω l ∂μ := by
  simp only [signedCubicTensor, Fin.prod_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Matrix.head_cons, Fin.prod_univ_zero, mul_one]
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  exact ae_of_all _ fun ω => (mul_assoc _ _ _).symm

theorem genericCubicContraction_eq_signedTensor
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (F : Vector p → ℝ) (x : Vector p) :
    genericCubicContraction μ F ξ x = canonicalSignedCubicContraction μ F ξ x := by
  have hi (i : Fin n) (α : Fin 3 → Fin p) : Integrable (fun ω => ∏ r, ξ i ω (α r)) μ :=
    integrable_bounded_coordinate_product μ (ξ i) (h.measurable i) (h.bounded i) α
  unfold genericCubicContraction canonicalSignedCubicContraction signedCubicTensor
  simp_rw [canonicalDiagonal_eq_coordinate_sum,
    integral_finset_sum _ (fun α _ => (hi _ α).mul_const _), integral_mul_const]
  rw [Finset.sum_comm]
  simp only [Finset.sum_mul]

theorem integrable_canonicalSignedCubicContraction_comp
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω] {p n : ℕ}
    (ρ : Measure B) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ C) (W : B → Vector p) (hW : Measurable W) :
    Integrable (fun z => canonicalSignedCubicContraction μ F ξ (W z)) ρ := by
  simpa only [genericCubicContraction_eq_signedTensor μ ξ h F] using
    integrable_genericCubicContraction_comp ρ μ ξ h hF hC hjet W hW

theorem integrable_canonicalSignedCubicContraction_seededLaw
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 3 F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ : ℝ → ℝ) (ε : ℝ) (x : Vector p) (t : ℝ)
    (hq : variableRetention γ t ∈ Set.Icc (0 : ℝ) 1) :
    Integrable (fun y => canonicalSignedCubicContraction μ F ξ (x+y))
      (variableSeededInterpolationLaw μ ξ A γ ε t) := by
  simpa only [genericCubicContraction_eq_signedTensor μ ξ h F] using
    integrable_genericCubicContraction_seededLaw μ ξ h hF hC hjet A γ ε x t hq

/-- Literal manuscript K3 formulation of the generic B.1 identity. The
tensor consists of actual signed third coordinate moments of the original
independent array; the displayed D3 contraction uses all ordered triples. -/
theorem hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (γ γ' : ℝ → ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hderiv : ∀ r ∈ Set.Ioo (0 : ℝ) 1, HasDerivAt γ (γ' r) r)
    (hpos : ∀ r ∈ Set.Ioo (0 : ℝ) 1, 0 < γ r)
    (hq : ∀ r ∈ Set.Ioo (0 : ℝ) 1, variableRetention γ r ∈ Set.Icc (0 : ℝ) 1)
    (x : Vector p) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (hcont : ContinuousAt γ' t) :
    HasDerivAt (fun r => ∫ y, F (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε r)
      (((-(γ t)+(1-t)*γ' t)/6)*
        (∫ y, canonicalSignedCubicContraction μ F ξ (x+y) ∂variableSeededInterpolationLaw μ ξ A γ ε t)+
       ∫ r in (0 : ℝ)..1, genericManuscriptFourthPathIntegrand μ (gaussianLaw A) F ξ x
         (variableRetention γ t) (γ t) (Real.sqrt (t+ε)) (variableEta γ γ' t) t r) t := by
  simpa only [genericCubicContraction_eq_signedTensor μ ξ h F] using
    hasDerivAt_integral_genericVariableSeededInterpolationLaw_manuscript μ ξ h hF hC hjet
      A hA γ γ' hε hderiv hpos hq x ht ht1 hcont

end
end RectangleCLT.Companion.SplitV4
