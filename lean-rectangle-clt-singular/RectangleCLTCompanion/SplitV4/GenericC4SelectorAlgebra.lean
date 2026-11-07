import RectangleCLTCompanion.SplitV4.GenericC4RowIntegrability
import RectangleCLTCompanion.SplitV4.GenericC4Heat

/-! Finite-selector algebra for actual general C4 tests. The forced-row
identities use proved independence and genuine linear-growth integrability. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

namespace C4Test
variable {p : ℕ} (f : C4Test p)

theorem integrable_value_sum_prod
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω]
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsFiniteMeasure μ]
    (B : Β → Vector p) (T : Ω → Vector p) (hB : Measurable B) (hT : Measurable T)
    (hiB : Integrable (fun β => ‖B β‖) ρ) (hiT : Integrable (fun ω => ‖T ω‖) μ) (a : ℝ) :
    Integrable (fun z : Β × Ω => f.value (B z.1+a • T z.2)) (ρ.prod μ) := by
  have hiBprod : Integrable (fun z : Β × Ω => ‖B z.1‖) (ρ.prod μ) := by
    simpa only [mul_one] using hiB.mul_prod (integrable_const (1 : ℝ))
  have hiTprod : Integrable (fun z : Β × Ω => ‖T z.2‖) (ρ.prod μ) := by
    simpa only [one_mul] using
      (integrable_const (1 : ℝ) : Integrable (fun _ : Β => (1 : ℝ)) ρ).mul_prod hiT
  have hm : Measurable (fun z : Β × Ω => B z.1+a • T z.2) :=
    (hB.comp measurable_fst).add (measurable_const.smul (hT.comp measurable_snd))
  apply f.integrable_value_of_norm _ _ hm
  apply (hiBprod.add (hiTprod.const_mul |a|)).mono' hm.norm.aestronglyMeasurable
  apply ae_of_all
  intro z
  rw [norm_norm]
  calc
    _ ≤ ‖B z.1‖+‖a • T z.2‖ := norm_add_le _ _
    _ = _ := by simp only [norm_smul, Real.norm_eq_abs, Pi.add_apply]

end C4Test

def genericFixedValue {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (x : Vector p) (a : ℝ) (mask : Kane.Cube n) : ℝ :=
  ∫ ω, F (x+a • maskObservationSum ξ mask ω) ∂μ

def genericFixedGradient {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (x : Vector p) (a : ℝ) (i : Fin n) (mask : Kane.Cube n) : ℝ :=
  ∫ ω, canonicalDiagonal F 1 (x+a • maskObservationSum ξ mask ω) (ξ i ω) ∂μ

def canonicalHessianCoordinate {p : ℕ} (F : Vector p → ℝ) (x : Vector p) (j k : Fin p) : ℝ :=
  iteratedFDeriv ℝ 2 F x ![C4Test.coordinateVector k,C4Test.coordinateVector j]

def genericFixedHeat {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (S : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (a : ℝ) (mask : Kane.Cube n) : ℝ :=
  (1/2 : ℝ)*∑ j, ∑ k, S j k*(∫ ω, canonicalHessianCoordinate F (x+a • maskObservationSum ξ mask ω) j k ∂μ)

theorem ofContDiff_gradient_eq_canonicalDiagonal {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C) (x v : Vector p) :
    (C4Test.ofContDiff F hF C hC hjet).gradient x v = canonicalDiagonal F 1 x v := by
  simp only [C4Test.ofContDiff, canonicalDiagonal, iteratedFDeriv_one_apply]

theorem ofContDiff_hessianCoordinate_eq_canonicalHessianCoordinate {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C) (x : Vector p) (j k : Fin p) :
    (C4Test.ofContDiff F hF C hC hjet).hessianCoordinate x j k = canonicalHessianCoordinate F x j k := by
  unfold C4Test.ofContDiff C4Test.hessianCoordinate canonicalHessianCoordinate
  congr 1
  funext i
  fin_cases i <;> simp

theorem generic_forced_increment_eq_rowOperator
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (mask : Kane.Cube n) (i : Fin n) (x : Vector p) (a c b : ℝ) :
    c*(genericFixedValue μ F ξ x a (Function.update mask i true)-
      genericFixedValue μ F ξ x a (Function.update mask i false))+
      b*genericFixedGradient μ F ξ x a i (Function.update mask i true) =
      ∫ ω, genericRowOperator μ F (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ := by
  let V := maskObservationSum ξ (Function.update mask i false)
  let B := fun ω => x+a • V ω
  let f := C4Test.ofContDiff F hF C hC hjet
  have hV : Measurable V := measurable_maskObservationSum ξ h.measurable _
  have hB : Measurable B := measurable_const.add (measurable_const.smul hV)
  have hiV : Integrable V μ := (integrable_const ((n : ℝ)*δ)).mono' hV.aestronglyMeasurable
    (maskObservationSum_bounded μ ξ h.delta_nonneg h.bounded _)
  have hiB : Integrable B μ := (integrable_const x).add (hiV.smul a)
  have hiT : Integrable (ξ i) μ := (integrable_const δ).mono' (h.measurable i).aestronglyMeasurable (h.bounded i)
  have hind : IndepFun B (ξ i) μ := by
    exact (indepFun_maskObservationSum_leaveOne μ ξ h.measurable h.independent mask i).symm.comp
      (measurable_const.add (measurable_const.smul measurable_id)) measurable_id
  have hvalue := f.integral_value_independent_copy μ B (ξ i) hB (h.measurable i) hind hiB.norm hiT.norm a
  have hgrad := integral_canonical_independent_copy μ hF (by decide) hC h.delta_nonneg
    (hjet 1 (by decide) (by decide)) B (ξ i) hB (h.measurable i) hind (h.bounded i) a
  have hpoint (ω : Ω) : x+a • maskObservationSum ξ (Function.update mask i true) ω = B ω+a • ξ i ω := by
    rw [maskObservationSum_update_add ξ mask i true ω]
    simp only [Bool.true_eq, ↓reduceIte, smul_add]
    dsimp [B, V]
    abel
  have ht : genericFixedValue μ F ξ x a (Function.update mask i true) =
      ∫ ω, (∫ u, F (B ω+a • ξ i u) ∂μ) ∂μ := by
    unfold genericFixedValue
    simp_rw [hpoint]
    exact hvalue.2
  have hg : genericFixedGradient μ F ξ x a i (Function.update mask i true) =
      ∫ ω, (∫ u, canonicalDiagonal F 1 (B ω+a • ξ i u) (ξ i u) ∂μ) ∂μ := by
    unfold genericFixedGradient
    simp_rw [hpoint]
    exact hgrad.2
  have htr := (f.integrable_value_sum_prod μ μ B (ξ i) hB (h.measurable i) hiB.norm hiT.norm a).integral_prod_left
  have hbase := f.integrable_value_of_norm μ B hB hiB.norm
  have hbcopy : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖ξ i z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae (h.bounded i)
  have hgjoint := integrable_canonicalDiagonal_bounded (μ.prod μ) hF (by decide)
    (fun z => B z.1+a • ξ i z.2) (fun z => ξ i z.2)
    ((hB.comp measurable_fst).add (measurable_const.smul ((h.measurable i).comp measurable_snd)))
    ((h.measurable i).comp measurable_snd) hC h.delta_nonneg (hjet 1 (by decide) (by decide)) hbcopy
  rw [ht, hg]
  unfold genericRowOperator
  rw [integral_add
    (f := fun ω => c*((∫ u, F (B ω+a • ξ i u) ∂μ)-F (B ω)))
    (g := fun ω => b*(∫ u, canonicalDiagonal F 1 (B ω+a • ξ i u) (ξ i u) ∂μ))
    ((htr.sub hbase).const_mul c) (hgjoint.integral_prod_left.const_mul b),
    integral_const_mul, integral_const_mul,
    integral_sub (f := fun ω => ∫ u, F (B ω+a • ξ i u) ∂μ) (g := fun ω => F (B ω)) htr hbase]
  rfl

def genericSelectorOperator {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (S : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (q a c b : ℝ) : ℝ :=
  c*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    (genericFixedValue μ F ξ x a (Function.update mask i true)-
      genericFixedValue μ F ξ x a (Function.update mask i false))) +
  b*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    genericFixedGradient μ F ξ x a i (Function.update mask i true)) +
  ∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ S x a mask

end
end RectangleCLT.Companion.SplitV4
