import RectangleCLTArxivV1.HFourthConditionalMatrix
import RectangleCLTArxivV1.SupplementalHSelectorTuples
import RectangleCLTCompanion.SplitV4.RestorationRelativeSeries
import RectangleCLTCompanion.RestorationScales

/-! Signed common-base cubic restoration orders for Appendix H. The
arbitrary-length cubic nuclear supplier is explicit in every quantitative
statement. The coefficient matrix is the genuine conditional average. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def hFourthCubicRestorationOrder {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ)
    (U : Face p → Vector r) (V : Ω → Vector p) (Z : Fin n → Ω → Vector r)
    (c : Fin n → Face p → Ω → ℝ) (v : Fin n → Ω → Vector p) (ℓ : ℕ) : ℝ :=
  ∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
    Matrix.trace (restorationRankOneSum Z
      (fun i z => c i (γ 0) z*
        restorationTranslationCoefficient s ![γ 0] (Fin.tail γ) (v i z)) ω*
          hFourthCubicGaussianScore s A U V γ ω) ∂μ

/-- At every actual restoration order, the conditional covariance bound
is used before the unconditional signed cubic matrix supplier. -/
theorem hFourth_cubic_restoration_order_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Face p → Ω → ℝ)
    (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i f, AEStronglyMeasurable (m := mΩ) (c i f) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (ℓ : ℕ)
    (hsupplier : (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s A U V γ ω) ∂μ) ≤ C^(ℓ+2)*T) :
    |hFourthCubicRestorationOrder (mΩ := mΩ) s μ A U V Z c v ℓ| ≤
      (b*Real.exp (R/s.bandwidth)*(Real.exp (R/s.bandwidth)-1)^ℓ)*C^(ℓ+2)*T := by
  classical
  letI : MeasurableSpace Ω := mΩ
  let E := Real.exp (R/s.bandwidth)*(Real.exp (R/s.bandwidth)-1)^ℓ
  have hE : 0 ≤ E := by
    have he := restorationTranslationEnvelope_nonneg s hR 1 ℓ
    simpa using he
  let B := fun (γ : Fin (ℓ+1) → Face p) => restorationRankOneSum Z
    (fun i z => c i (γ 0) z*restorationTranslationCoefficient s ![γ 0] (Fin.tail γ) (v i z))
  have hBi (γ : Fin (ℓ+1) → Face p) (j k : Fin r) : Integrable (fun ω => B γ ω j k) μ := by
    apply integrable_restorationRankOneSum_entry (mΩ := mΩ) μ Z _ hZ
    · intro i
      exact (hc i _).mul ((continuous_restorationTranslationCoefficient s _ _).comp_aestronglyMeasurable (hv i))
    · intro i
      filter_upwards [hcb i (γ 0),hvb i] with ω hcω hvω
      rw [abs_mul]
      exact mul_le_mul hcω (abs_restorationTranslationCoefficient_le s ![γ 0] (Fin.tail γ) hR hvω)
        (abs_nonneg _) hb
  have hCE (γ : Fin (ℓ+1) → Face p) : ∀ᵐ ω ∂μ, ∀ u,
      |matrixQuadratic (conditionalMatrixAverage (mΩ := mΩ) μ H (B γ) ω) u| ≤
        (b*E)*vectorNormSq u := by
    have hh := conditional_translated_restoration_coefficient_baseline (mΩ := mΩ) s μ H hH Z
      (fun i => c i (γ 0)) v hZ (fun i => hc i _) hv hb hR
      (fun i => hcb i _) hvb hbudget ![γ 0] (Fin.tail γ)
    simpa only [conditionalTranslatedRestorationCoefficient,conditionalRestorationCoefficient,B,E,
      Nat.cast_one,one_mul,mul_assoc] using hh
  have hmain := hFourth_conditional_matrix_sum_bound (mΩ := mΩ) μ H hH
    (fun γ => hFourthCubicGaussianScore s A U V γ) B
    (fun γ j k => stronglyMeasurable_hFourthCubicGaussianScore_entry (mΩ := H) s A U V hV γ j k)
    (fun γ ω => hFourthCubicGaussianScore_isHermitian s A U V γ ω)
    (fun γ j k => ∫ g, |capThirdHermiteMatrix (U (γ 0)) g j k| ∂standardGaussian r)
    (fun γ ω j k => abs_hFourthCubicGaussianScore_entry_le s A U V γ ω j k)
    hBi (mul_nonneg hb hE) hCE hsupplier
  exact hmain.2.trans_eq (by dsimp [E]; ring)

/-- Absolute summability and the exact geometric-series cap, with the
arbitrary restoration-length supplier still visible. -/
theorem hFourth_cubic_restoration_series_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Face p → Ω → ℝ)
    (v : Fin n → Ω → Vector p)
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i f, AEStronglyMeasurable (m := mΩ) (c i f) μ)
    (hv : ∀ i, AEStronglyMeasurable (m := mΩ) (v i) μ)
    {b R C T : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b)
    (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T)
    (hsmall : C*(Real.exp (R/s.bandwidth)-1) < 1)
    (hsupplier : ∀ ℓ : ℕ, (∫ ω, ∑ γ : Fin (ℓ+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s A U V γ ω) ∂μ) ≤ C^(ℓ+2)*T) :
    Summable (fun ℓ => (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)*
      hFourthCubicRestorationOrder (mΩ := mΩ) s μ A U V Z c v ℓ) ∧
    |∑' ℓ, (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)*hFourthCubicRestorationOrder (mΩ := mΩ) s μ A U V Z c v ℓ| ≤
      (b*Real.exp (R/s.bandwidth)*C^2*T)/(1-C*(Real.exp (R/s.bandwidth)-1))^2 := by
  have hord (ℓ : ℕ) := hFourth_cubic_restoration_order_bound (mΩ := mΩ) s μ H hH A U V hV
    Z c v hZ hc hv hb hR hcb hvb hbudget ℓ (hsupplier ℓ)
  have hh := restoration_scalar_series_bound (k := 1)
    (hFourthCubicRestorationOrder (mΩ := mΩ) s μ A U V Z c v) hb hR s.bandwidth_pos hC hT hsmall
    (fun ℓ => by simpa only [Nat.cast_one,one_mul,show 1+ℓ+1=ℓ+2 by omega] using hord ℓ)
  simpa only [Nat.cast_one,one_mul] using hh

end
end RectangleCLTArxivV1
