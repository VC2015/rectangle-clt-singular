import RectangleCLTArxivV1.HFourthFromSuppliers

/-! Literal tuple-length transport between the geometric `ell+2` and
restoration `2+ell` presentations, retaining both distinguished labels. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem hFourth_pair_nuclear_integral_add_comm
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (P : Face p → Face p → Prop) [DecidableRel P] (ℓ : ℕ) :
    (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ)=
      ∫ ω, ∑ γ : Fin (ℓ+2) → Face p,
        if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ := by
  let F := fun N : {N : ℕ // 2≤N} => ∫ ω, ∑ γ : Fin N.1 → Face p,
    if P (γ ⟨0,by omega⟩) (γ ⟨1,by omega⟩) then
      symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ
  have he := congrArg F (show (⟨2+ℓ,by omega⟩ : {N : ℕ // 2≤N})=⟨ℓ+2,by omega⟩ from
    Subtype.ext (Nat.add_comm 2 ℓ))
  have h0a : (⟨0,by omega⟩ : Fin (2+ℓ))=0 := by apply Fin.ext; simp
  have h1a : (⟨1,by omega⟩ : Fin (2+ℓ))=1 := by
    apply Fin.ext
    change (1:ℕ)=(1:ℕ)%(2+ℓ)
    rw [Nat.mod_eq_of_lt (by omega : (1:ℕ)<2+ℓ)]
  have h0b : (⟨0,by omega⟩ : Fin (ℓ+2))=0 := by apply Fin.ext; simp
  have h1b : (⟨1,by omega⟩ : Fin (ℓ+2))=1 := by
    apply Fin.ext
    change (1:ℕ)=(1:ℕ)%(ℓ+2)
    rw [Nat.mod_eq_of_lt (by omega : (1:ℕ)<ℓ+2)]
  simpa only [F,h0a,h1a,h0b,h1b] using he

theorem hFourth_pair_supplier_of_angle_weighted_front
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) {c C T : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+2) → Face p,
      correlationAngleWeight (faceDot (U (γ 0)) (U (γ 1)))*
        symmetricNuclearNorm (selectorGaussianScore s A V γ ω) ∂μ) ≤ C^(ℓ+3)*T) :
    ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if c ≤ 1-|faceDot (U (γ 0)) (U (γ 1))| then
        symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ) ≤
      C^(ℓ+3)*(T/exceptionalCutoffDet c) := by
  intro ℓ
  exact (hFourth_pair_nuclear_integral_add_comm μ s A V
    (fun f g => c ≤ 1-|faceDot (U f) (U g)|) ℓ).trans_le
      (hFourth_pair_supplier_of_angle_weighted μ s A U V hV hc hc1 hsupplier ℓ)

end
end RectangleCLTArxivV1
