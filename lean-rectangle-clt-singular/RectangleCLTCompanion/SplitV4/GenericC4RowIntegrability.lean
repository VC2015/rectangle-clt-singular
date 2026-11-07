import RectangleCLTCompanion.SplitV4.GenericC4FourthRows

/-! Genuine base-variable integrability for the generic fourth-order
identity. Arbitrarily large measurable deleted bases are allowed because
the derivatives are globally bounded and the copy directions are bounded. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem canonicalFourthTensor_diagonal {p : ℕ} (F : Vector p → ℝ) (x v : Vector p) :
    canonicalFourthTensor F x v v v v = canonicalDiagonal F 4 x v := by
  unfold canonicalFourthTensor canonicalDiagonal
  congr 1
  funext i
  fin_cases i <;> rfl

theorem integrable_genericFourthRows_base
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p : ℕ}
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W : Β → Vector p) (hW : Measurable W) (T : Ω → Vector p) (hT : Measurable T)
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (q a c b d : ℝ) :
    Integrable (fun β => genericRowFourthRemainder μ F T (W β) a c b) ρ ∧
      Integrable (fun β => genericFourthRowB μ F T (W β) q a) ρ ∧
      Integrable (fun β => genericFourthRowC μ F T (W β) q a d) ρ := by
  have hbA : ∀ᵐ z : Β × Ω ∂ρ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hA := canonicalFourthTensor_interval_fubini_data (ρ.prod μ) hF hC hδ hjet
    (fun z => W z.1) (fun z => T z.2) (fun z => T z.2) (fun z => T z.2)
    (fun z => T z.2) (fun z => T z.2) (hW.comp measurable_fst) (hT.comp measurable_snd)
    (hT.comp measurable_snd) (hT.comp measurable_snd) (hT.comp measurable_snd) (hT.comp measurable_snd)
    hbA hbA hbA hbA a (fun r => c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2) (by fun_prop)
  have hb1 : ∀ᵐ z : Β × (Ω × Ω) ∂ρ.prod (μ.prod μ), ‖T z.2.1‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hbound)
  have hb2 : ∀ᵐ z : Β × (Ω × Ω) ∂ρ.prod (μ.prod μ), ‖T z.2.2‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae hbound)
  have hB := canonicalFourthTensor_interval_fubini_data (ρ.prod (μ.prod μ)) hF hC hδ hjet
    (fun z => W z.1) (fun z => T z.2.2) (fun z => T z.2.1) (fun z => T z.2.1)
    (fun z => T z.2.2) (fun z => T z.2.2) (hW.comp measurable_fst)
    (hT.comp (measurable_snd.comp measurable_snd))
    (hT.comp (measurable_fst.comp measurable_snd)) (hT.comp (measurable_fst.comp measurable_snd))
    (hT.comp (measurable_snd.comp measurable_snd)) (hT.comp (measurable_snd.comp measurable_snd))
    hb1 hb1 hb2 hb2 a (fun r => 1-r) (by fun_prop)
  have hCdata := canonicalFourthTensor_interval_fubini_data (ρ.prod (μ.prod μ)) hF hC hδ hjet
    (fun z => W z.1) (fun z => T z.2.2) (fun z => T z.2.1) (fun z => T z.2.1)
    (fun z => T z.2.1) (fun z => T z.2.2) (hW.comp measurable_fst)
    (hT.comp (measurable_snd.comp measurable_snd))
    (hT.comp (measurable_fst.comp measurable_snd)) (hT.comp (measurable_fst.comp measurable_snd))
    (hT.comp (measurable_fst.comp measurable_snd)) (hT.comp (measurable_snd.comp measurable_snd))
    hb1 hb1 hb1 hb2 a (fun _ => 1) continuous_const
  refine ⟨?_, ?_, ?_⟩
  · simpa only [genericRowFourthRemainder, canonicalFourthTensor_diagonal] using hA.1.integral_prod_left
  · exact hB.1.integral_prod_left.const_mul (q*a^2/2)
  · simpa only [genericFourthRowC, one_mul] using hCdata.1.integral_prod_left.const_mul (-d*q*a)

theorem integrable_genericBernoulliMoment_base
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p k : ℕ}
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) (hk : k ≤ 4) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (W : Β → Vector p) (hW : Measurable W) (T : Ω → Vector p) (hT : Measurable T)
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (q a : ℝ) :
    Integrable (fun β => genericBernoulliMoment μ F k T (W β) q a) ρ := by
  have hb0 : ∀ᵐ z : Β × Ω ∂ρ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hbase := integrable_canonicalDiagonal_bounded (ρ.prod μ) hF hk (fun z => W z.1) (fun z => T z.2)
    (hW.comp measurable_fst) (hT.comp measurable_snd) hC hδ hjet hb0
  have hb1 : ∀ᵐ z : Β × (Ω × Ω) ∂ρ.prod (μ.prod μ), ‖T z.2.1‖ ≤ δ :=
    Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae hbound)
  have hshift := integrable_canonicalDiagonal_bounded (ρ.prod (μ.prod μ)) hF hk
    (fun z => W z.1+a • T z.2.2) (fun z => T z.2.1)
    ((hW.comp measurable_fst).add (measurable_const.smul (hT.comp (measurable_snd.comp measurable_snd))))
    (hT.comp (measurable_fst.comp measurable_snd)) hC hδ hjet hb1
  have hnest : Integrable (fun β => ∫ u, (∫ v, canonicalDiagonal F k (W β+a • T v) (T u) ∂μ) ∂μ) ρ := by
    apply hshift.integral_prod_left.congr
    filter_upwards [hshift.prod_right_ae] with β hβ
    exact integral_prod _ hβ
  exact (hbase.integral_prod_left.const_mul (1-q)).add (hnest.const_mul q)

def genericRowOperator {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (T : Ω → Vector p) (x : Vector p) (a c b : ℝ) : ℝ :=
  c*((∫ ω, F (x+a • T ω) ∂μ)-F x)+b*(∫ ω, canonicalDiagonal F 1 (x+a • T ω) (T ω) ∂μ)

def genericRowFourthTotal {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (T : Ω → Vector p) (x : Vector p) (q a c b d : ℝ) : ℝ :=
  genericRowFourthRemainder μ F T x a c b+genericFourthRowB μ F T x q a+genericFourthRowC μ F T x q a d

theorem integral_genericRow_commonPoint_identity
    {Β Ω : Type*} [MeasurableSpace Β] [MeasurableSpace Ω] {p : ℕ}
    (ρ : Measure Β) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (W : Β → Vector p) (hW : Measurable W) (T : Ω → Vector p) (hT : Measurable T)
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0)
    (q a c b d : ℝ) (ha : a ≠ 0)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    Integrable (fun β => genericRowOperator μ F T (W β) a c b) ρ ∧
    (∫ β, genericRowOperator μ F T (W β) a c b ∂ρ) =
      -(1/2 : ℝ)*(∫ β, genericBernoulliMoment μ F 2 T (W β) q a ∂ρ)+
      d*(∫ β, genericBernoulliMoment μ F 3 T (W β) q a ∂ρ)+
      (∫ β, genericRowFourthTotal μ F T (W β) q a c b d ∂ρ) := by
  have hi2 := integrable_genericBernoulliMoment_base ρ μ hF (by decide) hC hδ
    (hjet 2 (by decide) (by decide)) W hW T hT hbound q a
  have hi3 := integrable_genericBernoulliMoment_base ρ μ hF (by decide) hC hδ
    (hjet 3 (by decide) (by decide)) W hW T hT hbound q a
  have hiR := integrable_genericFourthRows_base ρ μ hF hC hδ (hjet 4 (by decide) (by decide))
    W hW T hT hbound q a c b d
  have hiTotal : Integrable (fun β => genericRowFourthTotal μ F T (W β) q a c b d) ρ :=
    (hiR.1.add hiR.2.1).add hiR.2.2
  have he (β : Β) : genericRowOperator μ F T (W β) a c b =
      -(1/2 : ℝ)*genericBernoulliMoment μ F 2 T (W β) q a+
      d*genericBernoulliMoment μ F 3 T (W β) q a+genericRowFourthTotal μ F T (W β) q a c b d :=
    genericRow_commonPoint_identity μ hF hC hδ hjet T hT hbound hc (W β) q a c b d ha h2 h3
  refine ⟨?_, ?_⟩
  · exact (((hi2.const_mul (-(1/2 : ℝ))).add (hi3.const_mul d)).add hiTotal).congr
      (ae_of_all _ fun β => (he β).symm)
  · rw [integral_congr_ae (ae_of_all _ he),
      integral_add (f := fun β => -(1/2 : ℝ)*genericBernoulliMoment μ F 2 T (W β) q a+
        d*genericBernoulliMoment μ F 3 T (W β) q a)
        (g := fun β => genericRowFourthTotal μ F T (W β) q a c b d)
        ((hi2.const_mul (-(1/2 : ℝ))).add (hi3.const_mul d)) hiTotal,
      integral_add (f := fun β => -(1/2 : ℝ)*genericBernoulliMoment μ F 2 T (W β) q a)
        (g := fun β => d*genericBernoulliMoment μ F 3 T (W β) q a)
        (hi2.const_mul (-(1/2 : ℝ))) (hi3.const_mul d), integral_const_mul, integral_const_mul]

end
end RectangleCLT.Companion.SplitV4
