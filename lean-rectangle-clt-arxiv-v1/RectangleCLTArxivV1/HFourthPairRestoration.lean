import RectangleCLTArxivV1.HFourthConditionalMatrix
import RectangleCLTCompanion.SplitV4.RestorationRelativeSeries
import RectangleCLTCompanion.RestorationScales

/-! Pair restoration keeps a restriction on the first two labels, with
every additional selector factor unchanged. The actual unweighted matrix
supplier on that restriction remains an explicit input. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1500000

def hFourthPairRestorationOrder {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (V : Ω → Vector p) (Z : Fin n → Ω → Vector r)
    (c : Fin n → (Fin 2 → Face p) → Ω → ℝ) (v : Fin n → Ω → Vector p) (ℓ : ℕ) : ℝ :=
  ∫ ω, ∑ α : Fin 2 → Face p, ∑ β : Fin ℓ → Face p,
    Matrix.trace (restorationRankOneSum Z
      (fun i z => c i α z*restorationTranslationCoefficient s α β (v i z)) ω*
        selectorGaussianScore s A V (Fin.append α β) ω) ∂μ

theorem hFourth_pair_restoration_order_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (c : Fin n → (Fin 2 → Face p) → Ω → ℝ)
    (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i α, AEStronglyMeasurable (m := mΩ) (c i α) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    (P : Face p → Face p → Prop) [DecidableRel P]
    (hzero : ∀ i α, ¬P (α 0) (α 1) → ∀ᵐ ω ∂μ, c i α ω=0)
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (ℓ : ℕ)
    (hsupplier : (∫ ω, ∑ γ : Fin (2+ℓ) → Face p,
      if P (γ 0) (γ 1) then symmetricNuclearNorm (selectorGaussianScore s A V γ ω) else 0 ∂μ) ≤ C^(ℓ+3)*T) :
    |hFourthPairRestorationOrder (mΩ := mΩ) s μ A V Z c v ℓ| ≤
      (b*Real.exp (2*R/s.bandwidth)*(Real.exp (R/s.bandwidth)-1)^ℓ)*C^(ℓ+3)*T := by
  classical
  letI : MeasurableSpace Ω := mΩ
  let E := Real.exp (2*R/s.bandwidth)*(Real.exp (R/s.bandwidth)-1)^ℓ
  have hE : 0 ≤ E := by simpa using restorationTranslationEnvelope_nonneg s hR 2 ℓ
  let a := fun (γ : Fin (2+ℓ) → Face p) (j : Fin 2) => γ (Fin.castAdd ℓ j)
  let β := fun (γ : Fin (2+ℓ) → Face p) (j : Fin ℓ) => γ (Fin.natAdd 2 j)
  let B := fun (γ : Fin (2+ℓ) → Face p) => restorationRankOneSum Z
    (fun i z => c i (a γ) z*restorationTranslationCoefficient s (a γ) (β γ) (v i z))
  let M := fun (γ : Fin (2+ℓ) → Face p) (ω : Ω) =>
    if P (γ 0) (γ 1) then selectorGaussianScore s A V γ ω else 0
  have hBi (γ : Fin (2+ℓ) → Face p) (j k : Fin r) : Integrable (fun ω => B γ ω j k) μ := by
    apply integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z _ hZ
    · intro i
      exact (hc i _).mul ((continuous_restorationTranslationCoefficient s _ _).comp_aestronglyMeasurable (hv i))
    · intro i
      filter_upwards [hcb i (a γ),hvb i] with ω hcω hvω
      rw [abs_mul]
      exact mul_le_mul hcω (abs_restorationTranslationCoefficient_le s (a γ) (β γ) hR hvω)
        (abs_nonneg _) hb
  have hCE (γ : Fin (2+ℓ) → Face p) : ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B γ) ω) u| ≤
        (b*E)*vectorNormSq u := by
    have hh := conditional_translated_restoration_coefficient_baseline (mΩ := mΩ) s μ H hH Z
      (fun i => c i (a γ)) v hZ (fun i => hc i _) hv hb hR
      (fun i => hcb i _) hvb hbudget (a γ) (β γ)
    simpa only [conditionalTranslatedRestorationCoefficient,conditionalRestorationCoefficient,B,E,
      Nat.cast_ofNat,mul_assoc] using hh
  have hMm (γ : Fin (2+ℓ) → Face p) (j k : Fin r) : StronglyMeasurable[H] (fun ω => M γ ω j k) := by
    by_cases hP : P (γ 0) (γ 1)
    · simpa only [M,if_pos hP] using stronglyMeasurable_selectorGaussianScore_entry (mΩ := H) s A V hV γ j k
    · simpa only [M,if_neg hP,Matrix.zero_apply] using (stronglyMeasurable_const : StronglyMeasurable[H] (fun _ : Ω => (0:ℝ)))
  have hMsym (γ : Fin (2+ℓ) → Face p) (ω : Ω) : (M γ ω).IsHermitian := by
    dsimp only [M]
    split_ifs
    · exact selectorGaussianScore_isHermitian s A V γ ω
    · exact Matrix.isHermitian_zero
  have hD (γ : Fin (2+ℓ) → Face p) (ω : Ω) (j k : Fin r) :
      |M γ ω j k| ≤ gaussianScoreEntryBudget r j k := by
    dsimp only [M]
    split_ifs
    · exact abs_selectorGaussianScore_entry_le s A V γ ω j k
    · simp only [Matrix.zero_apply,abs_zero]
      exact integral_nonneg (fun g => abs_nonneg _)
  have hsup : (∫ ω, ∑ γ : Fin (2+ℓ) → Face p, symmetricNuclearNorm (M γ ω) ∂μ) ≤ C^(ℓ+3)*T := by
    simpa only [M,apply_ite (symmetricNuclearNorm),symmetricNuclearNorm_zero] using hsupplier
  have hmain := hFourth_conditional_matrix_sum_bound (mΩ := mΩ) μ H hH M B hMm hMsym
    (fun _ j k => gaussianScoreEntryBudget r j k) hD hBi (mul_nonneg hb hE) hCE hsup
  have hBeq (γ : Fin (2+ℓ) → Face p) (hP : ¬P (γ 0) (γ 1)) :
      ∀ᵐ ω ∂μ, B γ ω=0 := by
    have h0 : Fin.castAdd ℓ (0 : Fin 2)=(0 : Fin (2+ℓ)) := by apply Fin.ext; simp
    have h1 : Fin.castAdd ℓ (1 : Fin 2)=(1 : Fin (2+ℓ)) := by
      apply Fin.ext
      change (1:ℕ)%2=(1:ℕ)%(2+ℓ)
      rw [Nat.mod_eq_of_lt (by omega : (1:ℕ)<2),Nat.mod_eq_of_lt (by omega : (1:ℕ)<2+ℓ)]
    have hP' : ¬P (a γ 0) (a γ 1) := by simpa only [a,h0,h1] using hP
    have hz (i : Fin n) : ∀ᵐ ω ∂μ, c i (a γ) ω=0 := hzero i (a γ) hP'
    filter_upwards [ae_all_iff.mpr hz] with ω hω
    ext j k
    simp [B,restorationRankOneSum,hω]
  have heq : (fun ω => ∑ γ : Fin (2+ℓ) → Face p,
      Matrix.trace (B γ ω*selectorGaussianScore s A V γ ω)) =ᵐ[μ]
      (fun ω => ∑ γ : Fin (2+ℓ) → Face p, Matrix.trace (B γ ω*M γ ω)) := by
    have hh (γ : Fin (2+ℓ) → Face p) : ∀ᵐ ω ∂μ,
        Matrix.trace (B γ ω*selectorGaussianScore s A V γ ω)=Matrix.trace (B γ ω*M γ ω) := by
      by_cases hP : P (γ 0) (γ 1)
      · exact ae_of_all _ (fun ω => by simp only [M,if_pos hP])
      · filter_upwards [hBeq γ hP] with ω hω
        simp [hω]
    filter_upwards [ae_all_iff.mpr hh] with ω hω
    exact Finset.sum_congr rfl (fun γ _ => hω γ)
  have hp (ω : Ω) : (∑ α : Fin 2 → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationRankOneSum Z
        (fun i z => c i α z*restorationTranslationCoefficient s α β (v i z)) ω*
          selectorGaussianScore s A V (Fin.append α β) ω))=
      ∑ γ : Fin (2+ℓ) → Face p, Matrix.trace (B γ ω*selectorGaussianScore s A V γ ω) := by
    rw [sum_faceTuples_append]
    exact Finset.sum_congr rfl (fun γ _ => by simp only [B,a,β,Fin.append_castAdd_natAdd])
  unfold hFourthPairRestorationOrder
  simp_rw [hp]
  rw [integral_congr_ae heq]
  exact hmain.2.trans_eq (by dsimp [E]; ring)

end
end RectangleCLTArxivV1
