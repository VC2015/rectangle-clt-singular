import RectangleCLTArxivV1.SupplementalHCubicFamilyMass

/-! The actual outer-averaged entropy for all cubic tuples. The common
factor C0*h*kappa is kept outside the logarithm. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalHCubicTupleMass_le_reference {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (U : Face p → Vector r) (α : Fin (K+1) → Face p) :
    supplementalHCubicTupleMoment s M (fun _ : Unit => v) U 0 α () ≤
      supplementalHCubicReferenceMass s M (fun _ : Unit => v) U α () := by
  let u := U (α 0)
  have hmi : Measurable (fun g : Vector r => oneFaceReference s (α 0) (v+M.mulVec g)) := by
    unfold oneFaceReference FaceSmoother.faceScore FaceSmoother.normalDot Matrix.mulVec dotProduct
    cases hf : (α 0).2 <;> simp [hf] <;> fun_prop
  have hpm : Measurable (supplementalHPositiveDirection u) := by
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hbi : Integrable (fun g => supplementalHPositiveDirection u g*
      oneFaceReference s (α 0) (v+M.mulVec g)) (standardGaussian r) := by
    apply (supplementalH_integrable_positiveDirection u).mono' (hpm.mul hmi).aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
        (supplementalHPositiveDirection_nonneg _ _) (oneFaceReference_bounds s (α 0) _).1)]
      exact mul_le_of_le_one_right (supplementalHPositiveDirection_nonneg _ _)
        (oneFaceReference_bounds s (α 0) _).2)
  simp only [supplementalHCubicTupleMoment,pow_zero,mul_one,supplementalHCubicReferenceMass]
  apply integral_mono_of_nonneg
    (ae_of_all _ (fun g => mul_nonneg (supplementalHPositiveDirection_nonneg _ _)
      (selectorWeight_nonneg s α _))) hbi
  exact ae_of_all _ (fun g => mul_le_mul_of_nonneg_left
    (selectorWeight_le_oneFaceReference s α _) (supplementalHPositiveDirection_nonneg _ _))

theorem supplementalH_log_face_card_le {p : ℕ} (hp : 1 ≤ p) :
    1 ≤ (Fintype.card (Face p):ℝ) ∧
      Real.log (Fintype.card (Face p):ℝ) ≤ dimensionLog p := by
  have hcard : (Fintype.card (Face p):ℝ)=2*(p:ℝ) := by simp [Face,Fintype.card_prod]; ring
  rw [hcard]
  have hp1 : 1 ≤ (p:ℝ) := by exact_mod_cast hp
  refine ⟨by linarith,?_⟩
  apply Real.log_le_log (by positivity)
  exact mul_le_mul_of_nonneg_right
    (show (2:ℝ) ≤ Real.exp 1 by linarith [Real.add_one_le_exp 1]) (Nat.cast_nonneg p)

/-- Actual finite-tuple entropy with the base average included, including
zero tuple masses. No log of h or kappa is introduced. -/
theorem intrinsicRectangleConcentration_cubicFamilyEntropy
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ] (V : Ω → Vector p) (hV : Measurable V)
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ)
    {C₀ δ κ : ℝ} (hC₀ : 0 ≤ C₀) (hκ : 0 ≤ κ) (hδh : δ ≤ s.bandwidth)
    (hc : IntrinsicRectangleConcentration (μ.map V) C₀ δ κ)
    (U : Face p → Vector r) (hU : ∀ f, vectorNormSq (U f)=1) :
    Integrable (fun ω => ∑ α : Fin (K+1) → Face p,
      supplementalHCubicTupleMoment s M V U 0 α ω*
        Real.log (supplementalHCubicReferenceMass s M V U α ω/
          supplementalHCubicTupleMoment s M V U 0 α ω)) μ ∧
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      supplementalHCubicTupleMoment s M V U 0 α ω*
        Real.log (supplementalHCubicReferenceMass s M V U α ω/
          supplementalHCubicTupleMoment s M V U 0 α ω) ∂μ) ≤
      (4*Real.exp 10*C₀*s.bandwidth*κ)*((K:ℝ)+2)*dimensionLog p*Real.sqrt (dimensionLog p) := by
  classical
  let P := supplementalHCubicTupleMoment (K := K) s M V U 0
  let B := supplementalHCubicReferenceMass (K := K) s M V U
  let A := 4*Real.exp 10*C₀*s.bandwidth*κ
  have hP := intrinsicRectangleConcentration_cubicTupleMoment (K := K) hp μ V hV s M
    hC₀ hκ hδh hc U hU 0
  have hB (α : Fin (K+1) → Face p) := supplementalHCubicReferenceMass_properties μ V hV s M U α
  have hP0 (α) (ω : Ω) : 0 ≤ P α ω := by
    apply integral_nonneg
    intro g
    exact mul_nonneg (mul_nonneg (supplementalHPositiveDirection_nonneg _ _)
      (pow_nonneg (abs_nonneg _) _)) (selectorWeight_nonneg s α _)
  have hPB (α) (ω : Ω) : P α ω ≤ B α ω :=
    supplementalHCubicTupleMass_le_reference s M (V ω) U α
  have hL := log_exp_mul_nat_ge_one hp
  have hR : 1 ≤ Real.sqrt (dimensionLog p) := Real.one_le_sqrt.mpr hL
  have hcoef : 0 ≤ 4*C₀*s.bandwidth*κ :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hC₀) s.bandwidth_pos.le) hκ
  have hh : 0 < s.bandwidth := s.bandwidth_pos
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hMass : (∫ ω, ∑ α : Fin (K+1) → Face p, P α ω ∂μ) ≤ A*Real.sqrt (dimensionLog p) := by
    have he : (8+((0+2:ℝ))^2/2)=10 := by norm_num
    have ht := hP.2
    simp only [Nat.zero_add,pow_one,he] at ht
    exact ht.trans_eq (by dsimp [A]; ring)
  have hReference : (∫ ω, ∑ α : Fin (K+1) → Face p, B α ω ∂μ) ≤
      A*(Fintype.card (Face p):ℝ)^(K+1) := by
    have ht := intrinsicRectangleConcentration_cubicReferenceFamily (K := K) μ V hV s M
      hC₀ hκ hδh hc U hU
    have hcA : 4*C₀*s.bandwidth*κ ≤ A := by
      have he : 1 ≤ Real.exp (10:ℝ) := Real.one_le_exp (by norm_num)
      convert le_mul_of_one_le_right hcoef he using 1
      dsimp [A]
      ring
    exact ht.trans (mul_le_mul_of_nonneg_right hcA (pow_nonneg (Nat.cast_nonneg _) _))
  refine ⟨integrable_finset_sum _ (fun α _ => integrable_entropy_term μ (P α) (B α)
    (hP.1 α).1 (hB α).1 (hP0 α) (hPB α) (hP.1 α).2 (hB α).2),?_⟩
  have ht := supplementalH_integral_entropy_cardinality_bound μ P B
    (fun α => (hP.1 α).1) (fun α => (hB α).1) hP0 hPB
    (fun α => (hP.1 α).2) (fun α => (hB α).2)
    hA hL hR (supplementalH_log_face_card_le hp).1 (supplementalH_log_face_card_le hp).2
    (K+1) hMass hReference
  simpa only [A,Nat.cast_add,Nat.cast_one,add_assoc,show (1:ℝ)+1=2 by norm_num,mul_assoc] using ht

end
end RectangleCLTArxivV1
