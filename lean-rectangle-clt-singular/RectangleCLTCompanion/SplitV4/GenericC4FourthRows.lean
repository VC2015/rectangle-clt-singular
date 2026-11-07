import RectangleCLTCompanion.SplitV4.GenericC4Copies
import RectangleCLTCompanion.SplitV4.GenericC4Symmetry

/-! Actual fourth-order independent-copy terms and Fubini for arbitrary
C4 tests. The fourth tensor uses the ordinary manuscript slot order. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def canonicalFourthTensor {p : ℕ} (F : Vector p → ℝ) (x u v w z : Vector p) : ℝ :=
  iteratedFDeriv ℝ 4 F x ![u,v,w,z]

theorem norm_canonicalFourthTensor_le {p : ℕ} (F : Vector p → ℝ)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (x u v w z : Vector p) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ) (hw : ‖w‖ ≤ δ) (hz : ‖z‖ ≤ δ) :
    ‖canonicalFourthTensor F x u v w z‖ ≤ C*δ^4 := by
  have htuple (i : Fin 4) : ‖(![u,v,w,z] : Fin 4 → Vector p) i‖ ≤ δ := by
    fin_cases i <;> first | exact hu | exact hv | exact hw | exact hz
  calc
    _ ≤ ‖iteratedFDeriv ℝ 4 F x‖*∏ i, ‖(![u,v,w,z] : Fin 4 → Vector p) i‖ :=
      (iteratedFDeriv ℝ 4 F x).le_opNorm _
    _ ≤ C*∏ _i : Fin 4, δ := mul_le_mul (hjet x)
      (Finset.prod_le_prod (fun i _ => norm_nonneg _) (fun i _ => htuple i))
      (Finset.prod_nonneg (fun i _ => norm_nonneg _)) hC
    _ = _ := by simp

set_option maxHeartbeats 1000000 in
theorem integrable_canonicalFourthTensor_interval_prod
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W V U1 U2 U3 U4 : Ω → Vector p)
    (hW : Measurable W) (hV : Measurable V) (hU1 : Measurable U1) (hU2 : Measurable U2)
    (hU3 : Measurable U3) (hU4 : Measurable U4)
    (hb1 : ∀ᵐ ω ∂μ, ‖U1 ω‖ ≤ δ) (hb2 : ∀ᵐ ω ∂μ, ‖U2 ω‖ ≤ δ)
    (hb3 : ∀ᵐ ω ∂μ, ‖U3 ω‖ ≤ δ) (hb4 : ∀ᵐ ω ∂μ, ‖U4 ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    Integrable (fun y : Ω × ℝ => K y.2 * canonicalFourthTensor F (W y.1+(a*y.2) • V y.1)
      (U1 y.1) (U2 y.1) (U3 y.1) (U4 y.1))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image hK.norm.continuousOn
  let M := max 0 M0
  have hM : 0 ≤ M := le_max_left _ _
  have hKb (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1) : ‖K r‖ ≤ M :=
    (hM0 (Set.mem_image_of_mem _ ⟨hr.1.le,hr.2⟩)).trans (le_max_right _ _)
  have hEval : Continuous (fun z : Vector p × (Fin 4 → Vector p) => iteratedFDeriv ℝ 4 F z.1 z.2) :=
    ((hF.continuous_iteratedFDeriv (m := 4) (by norm_num)).comp continuous_fst).eval continuous_snd
  have hpoint : Measurable (fun y : Ω × ℝ => W y.1+(a*y.2) • V y.1) :=
    (hW.comp measurable_fst).add ((measurable_const.mul measurable_snd).smul (hV.comp measurable_fst))
  have htuple : Measurable (fun y : Ω × ℝ => (![U1 y.1,U2 y.1,U3 y.1,U4 y.1] : Fin 4 → Vector p)) := by
    apply measurable_pi_lambda
    intro i
    fin_cases i <;> first | exact hU1.comp measurable_fst | exact hU2.comp measurable_fst |
      exact hU3.comp measurable_fst | exact hU4.comp measurable_fst
  have hm : Measurable (fun y : Ω × ℝ => K y.2 * canonicalFourthTensor F (W y.1+(a*y.2) • V y.1)
      (U1 y.1) (U2 y.1) (U3 y.1) (U4 y.1)) :=
    (hK.measurable.comp measurable_snd).mul (hEval.measurable.comp (hpoint.prodMk htuple))
  apply (integrable_const (M*(C*δ^4))).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hb1, Measure.quasiMeasurePreserving_fst.ae hb2,
    Measure.quasiMeasurePreserving_fst.ae hb3, Measure.quasiMeasurePreserving_fst.ae hb4,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with y hy1 hy2 hy3 hy4 hyr
  rw [norm_mul]
  exact mul_le_mul (hKb y.2 hyr)
    (norm_canonicalFourthTensor_le F hC hδ hjet _ _ _ _ _ hy1 hy2 hy3 hy4) (norm_nonneg _) hM

theorem canonicalFourthTensor_interval_fubini_data
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W V U1 U2 U3 U4 : Ω → Vector p)
    (hW : Measurable W) (hV : Measurable V) (hU1 : Measurable U1) (hU2 : Measurable U2)
    (hU3 : Measurable U3) (hU4 : Measurable U4)
    (hb1 : ∀ᵐ ω ∂μ, ‖U1 ω‖ ≤ δ) (hb2 : ∀ᵐ ω ∂μ, ‖U2 ω‖ ≤ δ)
    (hb3 : ∀ᵐ ω ∂μ, ‖U3 ω‖ ≤ δ) (hb4 : ∀ᵐ ω ∂μ, ‖U4 ω‖ ≤ δ)
    (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..1, K r * canonicalFourthTensor F (W ω+(a*r) • V ω)
      (U1 ω) (U2 ω) (U3 ω) (U4 ω)) μ ∧
    IntervalIntegrable (fun r => K r*(∫ ω, canonicalFourthTensor F (W ω+(a*r) • V ω)
      (U1 ω) (U2 ω) (U3 ω) (U4 ω) ∂μ)) volume 0 1 ∧
    (∫ ω, (∫ r in (0 : ℝ)..1, K r * canonicalFourthTensor F (W ω+(a*r) • V ω)
      (U1 ω) (U2 ω) (U3 ω) (U4 ω)) ∂μ) =
      ∫ r in (0 : ℝ)..1, K r*(∫ ω, canonicalFourthTensor F (W ω+(a*r) • V ω)
        (U1 ω) (U2 ω) (U3 ω) (U4 ω) ∂μ) := by
  have hi := integrable_canonicalFourthTensor_interval_prod μ hF hC hδ hjet W V U1 U2 U3 U4
    hW hV hU1 hU2 hU3 hU4 hb1 hb2 hb3 hb4 a K hK
  refine ⟨?_, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_of_le zero_le_one] using hi.integral_prod_left
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    simpa only [integral_const_mul] using hi.integral_prod_right
  · have hs := integral_integral_swap (μ := μ) (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun ω r => K r*canonicalFourthTensor F (W ω+(a*r) • V ω) (U1 ω) (U2 ω) (U3 ω) (U4 ω)) hi
    simpa only [intervalIntegral.integral_of_le zero_le_one, integral_const_mul] using hs

theorem canonicalFourthTensor_pair_slot_equivalence {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x u v : Vector p) :
    iteratedFDeriv ℝ 4 F x (Fin.cons v (Fin.cons v (fun _ : Fin 2 => u))) =
      canonicalFourthTensor F x u u v v := by
  have he : Fin.cons v (Fin.cons v (fun _ : Fin 2 => u)) = (![v,v,u,u] : Fin 4 → Vector p) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact canonical_fourth_reverse hF x v v u u

theorem canonicalFourthTensor_triple_slot_equivalence {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x u v : Vector p) :
    iteratedFDeriv ℝ 4 F x (Fin.cons v (fun _ : Fin 3 => u)) =
      canonicalFourthTensor F x u u u v := by
  have he : Fin.cons v (fun _ : Fin 3 => u) = (![v,u,u,u] : Fin 4 → Vector p) := by
    funext i
    fin_cases i <;> rfl
  rw [he]
  exact canonical_fourth_reverse hF x v u u u

def genericFourthRowB {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  q*a^2/2 * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, (1-r)*
    canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.2) (T z.2)) ∂μ.prod μ

def genericFourthRowC {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (T : Ω → Vector p) (x : Vector p) (q a d : ℝ) : ℝ :=
  -d*q*a * ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1,
    canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.1) (T z.2)) ∂μ.prod μ

theorem genericFourthRowB_eq_correction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (q : ℝ) {a : ℝ} (ha : a ≠ 0) :
    genericFourthRowB μ F T x q a = q/2 *
      ((∫ u, (∫ v, canonicalDiagonal F 2 (x+a • T v) (T u) ∂μ) ∂μ)-
        (∫ u, canonicalDiagonal F 2 x (T u) ∂μ)) := by
  have hb1 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.1‖ ≤ δ := Measure.quasiMeasurePreserving_fst.ae hbound
  have hb2 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hd := canonicalFourthTensor_interval_fubini_data (μ.prod μ) hF hC hδ
    (hjet 4 (by decide) (by decide)) (fun _ => x) (fun z => T z.2)
    (fun z => T z.1) (fun z => T z.1) (fun z => T z.2) (fun z => T z.2)
    measurable_const (hT.comp measurable_snd) (hT.comp measurable_fst) (hT.comp measurable_fst)
    (hT.comp measurable_snd) (hT.comp measurable_snd) hb1 hb1 hb2 hb2 a (fun r => 1-r) (by fun_prop)
  have hshiftPair : Integrable (fun z : Ω × Ω => canonicalDiagonal F 2 (x+a • T z.2) (T z.1)) (μ.prod μ) :=
    integrable_canonicalDiagonal_bounded (μ.prod μ) hF (by decide) _ _
      (measurable_const.add (measurable_const.smul (hT.comp measurable_snd)))
      (hT.comp measurable_fst) hC hδ (hjet 2 (by decide) (by decide)) hb1
  have hbase : Integrable (fun u => canonicalDiagonal F 2 x (T u)) μ :=
    integrable_canonicalDiagonal_bounded μ hF (by decide) _ _ measurable_const hT
      hC hδ (hjet 2 (by decide) (by decide)) hbound
  have he (u : Ω) : (∫ v, canonicalDiagonal F 2 (x+a • T v) (T u) ∂μ)-
      canonicalDiagonal F 2 x (T u) =
      a^2*(∫ v, (∫ r in (0 : ℝ)..1, (1-r)*
        canonicalFourthTensor F (x+(a*r) • T v) (T u) (T u) (T v) (T v)) ∂μ) := by
    have hh := integral_canonical_hessian_shift_sub μ hF hC hδ hjet T hT hbound hc x (T u) ha
    simpa only [canonicalDiagonal, canonicalFourthTensor_pair_slot_equivalence hF] using hh
  have hh := integral_congr_ae (ae_of_all μ he)
  rw [integral_sub (f := fun u => ∫ v, canonicalDiagonal F 2 (x+a • T v) (T u) ∂μ)
    (g := fun u => canonicalDiagonal F 2 x (T u)) hshiftPair.integral_prod_left hbase,
    integral_const_mul] at hh
  unfold genericFourthRowB
  rw [integral_prod _ hd.1]
  rw [hh]
  ring

theorem genericFourthRowC_eq_correction
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (q d : ℝ) {a : ℝ} (ha : a ≠ 0) :
    genericFourthRowC μ F T x q a d = -d*q *
      ((∫ u, (∫ v, canonicalDiagonal F 3 (x+a • T v) (T u) ∂μ) ∂μ)-
        (∫ u, canonicalDiagonal F 3 x (T u) ∂μ)) := by
  have hb1 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.1‖ ≤ δ := Measure.quasiMeasurePreserving_fst.ae hbound
  have hb2 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hd := canonicalFourthTensor_interval_fubini_data (μ.prod μ) hF hC hδ
    (hjet 4 (by decide) (by decide)) (fun _ => x) (fun z => T z.2)
    (fun z => T z.1) (fun z => T z.1) (fun z => T z.1) (fun z => T z.2)
    measurable_const (hT.comp measurable_snd) (hT.comp measurable_fst) (hT.comp measurable_fst)
    (hT.comp measurable_fst) (hT.comp measurable_snd) hb1 hb1 hb1 hb2 a (fun _ => 1) continuous_const
  have hR : Integrable (fun z : Ω × Ω => ∫ r in (0 : ℝ)..1,
      canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.1) (T z.2)) (μ.prod μ) := by
    simpa only [one_mul] using hd.1
  have hshiftPair : Integrable (fun z : Ω × Ω => canonicalDiagonal F 3 (x+a • T z.2) (T z.1)) (μ.prod μ) :=
    integrable_canonicalDiagonal_bounded (μ.prod μ) hF (by decide) _ _
      (measurable_const.add (measurable_const.smul (hT.comp measurable_snd)))
      (hT.comp measurable_fst) hC hδ (hjet 3 (by decide) (by decide)) hb1
  have hbase : Integrable (fun u => canonicalDiagonal F 3 x (T u)) μ :=
    integrable_canonicalDiagonal_bounded μ hF (by decide) _ _ measurable_const hT
      hC hδ (hjet 3 (by decide) (by decide)) hbound
  have he (u : Ω) : (∫ v, canonicalDiagonal F 3 (x+a • T v) (T u) ∂μ)-
      canonicalDiagonal F 3 x (T u) =
      a*(∫ v, (∫ r in (0 : ℝ)..1,
        canonicalFourthTensor F (x+(a*r) • T v) (T u) (T u) (T u) (T v)) ∂μ) := by
    have hh := integral_canonical_third_shift_sub μ hF hC
      (hjet 3 (by decide) (by decide)) T hT x (T u) ha
    simpa only [canonicalDiagonal, canonicalFourthTensor_triple_slot_equivalence hF] using hh
  have hh := integral_congr_ae (ae_of_all μ he)
  rw [integral_sub (f := fun u => ∫ v, canonicalDiagonal F 3 (x+a • T v) (T u) ∂μ)
    (g := fun u => canonicalDiagonal F 3 x (T u)) hshiftPair.integral_prod_left hbase,
    integral_const_mul] at hh
  unfold genericFourthRowC
  rw [integral_prod _ hR, hh]
  ring

def genericBernoulliMoment {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (k : ℕ) (T : Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  (1-q)*(∫ u, canonicalDiagonal F k x (T u) ∂μ)+
    q*(∫ u, (∫ v, canonicalDiagonal F k (x+a • T v) (T u) ∂μ) ∂μ)

/-- General smooth-test common-point restoration, with the ordinary
fourth derivative in the manuscript's exact independent-copy slot order. -/
theorem genericRow_commonPoint_identity
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (q a c b d : ℝ) (ha : a ≠ 0)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    c*((∫ ω, F (x+a • T ω) ∂μ)-F x)+
      b*(∫ ω, canonicalDiagonal F 1 (x+a • T ω) (T ω) ∂μ) =
      -(1/2 : ℝ)*genericBernoulliMoment μ F 2 T x q a+
      d*genericBernoulliMoment μ F 3 T x q a+
      (genericRowFourthRemainder μ F T x a c b+genericFourthRowB μ F T x q a+
        genericFourthRowC μ F T x q a d) := by
  rw [genericRowTranslation_identity μ hF hC hδ hjet T hT hbound hc x a c b d h2 h3,
    genericFourthRowB_eq_correction μ hF hC hδ hjet T hT hbound hc x q ha,
    genericFourthRowC_eq_correction μ hF hC hδ hjet T hT hbound x q d ha]
  unfold genericBernoulliMoment
  ring

end
end RectangleCLT.Companion.SplitV4
