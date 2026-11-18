import RectangleCLTArxivV1.HFourthConditionalMatrix
import RectangleCLTArxivV1.SupplementalHCubicMatrix

/-! Exact bridges between the geometric H matrix suppliers on a physical
Gaussian-support base law and the native seeded face-coordinate matrices. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hFourthCubicGaussianScore_eq_selectorScore {Ω : Type*} {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (α : Fin (K+1) → Face p) (ω : Ω) :
    hFourthCubicGaussianScore s M U V α ω=
      supplementalHCubicSelectorScore s M (V ω) α (U (α 0)) := rfl

theorem measurable_hFourthCubicGaussianScore_nuclear
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (s : FaceSmoother p) (M : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (α : Fin (K+1) → Face p) :
    Measurable (fun ω => symmetricNuclearNorm (hFourthCubicGaussianScore s M U V α ω)) := by
  have hc : Continuous (fun N : Fin r → Fin r → ℝ => symmetricNuclearNorm N) := continuous_symmetricNuclearNorm
  have hm : Measurable (fun ω => fun j k => hFourthCubicGaussianScore s M U V α ω j k) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun k =>
      (stronglyMeasurable_hFourthCubicGaussianScore_entry s M U V hV α j k).measurable))
  exact hc.measurable.comp hm

theorem hFourth_cubic_matrix_sum_physical_transport
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) (s : FaceSmoother p)
    (A M : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r) (x : Vector p)
    (B : Ω → Vector r) (hB : Measurable B) (V : Ω → Vector p)
    (hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω)) :
    (∫ ω, ∑ α : Fin (K+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s M U V α ω) ∂μ)=
      ∫ b, ∑ α : Fin (K+1) → Face p,
        symmetricNuclearNorm (hFourthCubicGaussianScore s M U (fun b => x+A.mulVec b) α b) ∂μ.map B := by
  have hV : Measurable (fun b => x+A.mulVec b) :=
    measurable_const.add (continuous_const.matrix_mulVec continuous_id).measurable
  have hF : Measurable (fun b : Vector r => ∑ α : Fin (K+1) → Face p,
      symmetricNuclearNorm (hFourthCubicGaussianScore s M U (fun b => x+A.mulVec b) α b)) :=
    Finset.measurable_sum Finset.univ (fun α _ =>
      measurable_hFourthCubicGaussianScore_nuclear s M U _ hV α)
  rw [integral_map hB.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hrec] with ω hω
  apply Finset.sum_congr rfl
  intro α _
  apply congrArg symmetricNuclearNorm
  ext j k
  simp only [hFourthCubicGaussianScore,hω]

/-- Arbitrary fixed tuple coefficients include the angle weight and the
first-pair cutoff. The original smoother and every extra factor survive. -/
theorem hFourth_pair_matrix_sum_physical_transport
    {Ω : Type*} [MeasurableSpace Ω] {p r K : ℕ}
    (μ : Measure Ω) (s : FaceSmoother p)
    (A M : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (B : Ω → Vector r) (hB : Measurable B) (V : Ω → Vector p)
    (hrec : V =ᵐ[μ] fun ω => x+A.mulVec (B ω))
    (w : (Fin K → Face p) → ℝ) :
    (∫ ω, ∑ α : Fin K → Face p,
      w α*symmetricNuclearNorm (selectorGaussianScore s M V α ω) ∂μ)=
      ∫ b, ∑ α : Fin K → Face p,
        w α*symmetricNuclearNorm (selectorGaussianScore s M (fun b => x+A.mulVec b) α b) ∂μ.map B := by
  have hV : Measurable (fun b => x+A.mulVec b) :=
    measurable_const.add (continuous_const.matrix_mulVec continuous_id).measurable
  have hF := Finset.measurable_sum Finset.univ (fun α _ =>
    (measurable_selectorGaussianScore_nuclear s M _ hV α).const_mul (w α))
  rw [integral_map hB.aemeasurable hF.aestronglyMeasurable]
  apply integral_congr_ae
  filter_upwards [hrec] with ω hω
  apply Finset.sum_congr rfl
  intro α _
  simp only [selectorGaussianScore,hω]

end
end RectangleCLTArxivV1
