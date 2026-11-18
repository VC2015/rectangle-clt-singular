import RectangleCLTArxivV1.SupplementalGCopyModel

/-! Signed two-face projection of the actual independent array. These
constructors retain the original coordinate envelope under singular factors. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capSignedProjection {p : ℕ} (f g : Face p) (x : Vector p) : Vector 2 :=
  ![normalDot f x,normalDot g x]

theorem capSignedProjection_measurable {p : ℕ} (f g : Face p) :
    Measurable (capSignedProjection f g) := by
  apply measurable_pi_lambda
  intro j
  fin_cases j
  · change Measurable (fun x : Vector p => normalDot f x)
    unfold normalDot
    split <;> fun_prop
  · change Measurable (fun x : Vector p => normalDot g x)
    unfold normalDot
    split <;> fun_prop

theorem capSignedProjection_norm_le {p : ℕ} (f g : Face p) (x : Vector p) :
    ‖capSignedProjection f g x‖ ≤ ‖x‖ := by
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg x)).mpr
  intro j
  fin_cases j
  · simpa only [capSignedProjection,Matrix.cons_val_zero,Real.norm_eq_abs] using
      abs_normalDot_le_of_norm_le f (le_rfl : ‖x‖≤‖x‖)
  · simpa only [capSignedProjection,Matrix.cons_val_one,Real.norm_eq_abs] using
      abs_normalDot_le_of_norm_le g (le_rfl : ‖x‖≤‖x‖)

theorem capSignedProjection_sum {Ω : Type*} {p n : ℕ} (f g : Face p)
    (ξ : Fin n → Ω → Vector p) (ω : Ω) :
    sumVector (fun i ω => capSignedProjection f g (ξ i ω)) ω = capSignedProjection f g (sumVector ξ ω) := by
  ext j
  fin_cases j <;> unfold sumVector capSignedProjection normalDot
  all_goals split <;> simp [Finset.sum_apply,Finset.sum_neg_distrib]

theorem capSignedProjection_hypotheses
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (f g : Face p) :
    BoundedIndependentHypotheses μ (fun i ω => capSignedProjection f g (ξ i ω)) δ where
  measurable i := (capSignedProjection_measurable f g).comp (h.measurable i)
  independent := h.independent.comp (fun _ => capSignedProjection f g)
    (fun _ => capSignedProjection_measurable f g)
  centered i j := by
    fin_cases j
    · change (∫ ω, normalDot f (ξ i ω) ∂μ)=0
      unfold normalDot
      split <;> simp [integral_neg,h.centered]
    · change (∫ ω, normalDot g (ξ i ω) ∂μ)=0
      unfold normalDot
      split <;> simp [integral_neg,h.centered]
  bounded i := (h.bounded i).mono (fun ω hω => (capSignedProjection_norm_le f g (ξ i ω)).trans hω)
  delta_nonneg := h.delta_nonneg

theorem capSignedProjection_covariance_zero_zero
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p) (f g : Face p) :
    covariance μ (fun ω => capSignedProjection f g (W ω)) 0 0 = covariance μ W f.1 f.1 := by
  cases hf : f.2 <;> simp [covariance,capSignedProjection,normalDot,hf,integral_neg]

theorem capSignedProjection_covariance_one_one
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p) (f g : Face p) :
    covariance μ (fun ω => capSignedProjection f g (W ω)) 1 1 = covariance μ W g.1 g.1 := by
  cases hg : g.2 <;> simp [covariance,capSignedProjection,normalDot,hg,integral_neg]

/-- The projected off-diagonal covariance has exactly the signs of the
corresponding original faces. -/
theorem capSignedProjection_covariance_zero_one
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) (W : Ω → Vector p) (f g : Face p) :
    covariance μ (fun ω => capSignedProjection f g (W ω)) 0 1 =
      (if f.2 then (1 : ℝ) else -1)*(if g.2 then (1 : ℝ) else -1)*covariance μ W f.1 g.1 := by
  cases hf : f.2 <;> cases hg : g.2 <;>
    simp [covariance,capSignedProjection,normalDot,hf,hg,integral_neg,neg_mul,mul_neg]
  all_goals ring

/-- The factor-row angle is precisely the signed original covariance entry. -/
theorem capRectangularFactorNormal_gram {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (f g : Face p) :
    faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g) =
      (if f.2 then (1 : ℝ) else -1)*(if g.2 then (1 : ℝ) else -1)*(A*A.transpose) f.1 g.1 := by
  cases hf : f.2 <;> cases hg : g.2 <;>
    simp [capRectangularFactorNormal,hf,hg,faceDot,Matrix.mul_apply,Matrix.transpose_apply,
      Finset.sum_neg_distrib,neg_mul,mul_neg]

end
end RectangleCLTArxivV1
