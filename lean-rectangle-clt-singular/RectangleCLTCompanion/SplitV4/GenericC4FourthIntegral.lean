import RectangleCLTCompanion.SplitV4.GenericC4FourthIdentity

/-! Outer-interval representation of the actual generic fourth-order
remainder, on one common product space carrying the two independent copies.
All three tensors use the ordinary iterated Fréchet derivative slot order. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def genericFourthCombination {p : ℕ} (F : Vector p → ℝ) (x u v : Vector p)
    (q a c b d r : ℝ) : ℝ :=
  (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*canonicalFourthTensor F (x+(a*r) • v) v v v v+
    (q*a^2/2*(1-r))*canonicalFourthTensor F (x+(a*r) • v) u u v v+
    (-d*q*a)*canonicalFourthTensor F (x+(a*r) • v) u u u v

theorem integrable_genericFourthCombination_interval_prod
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W U V : Ω → Vector p) (hW : Measurable W) (hU : Measurable U) (hV : Measurable V)
    (hbU : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ δ) (hbV : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ) (q a c b d : ℝ) :
    Integrable (fun y : Ω × ℝ => genericFourthCombination F (W y.1) (U y.1) (V y.1) q a c b d y.2)
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  have hA := integrable_canonicalFourthTensor_interval_prod μ hF hC hδ hjet W V V V V V
    hW hV hV hV hV hV hbV hbV hbV hbV a
    (fun r => c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2) (by fun_prop)
  have hB := integrable_canonicalFourthTensor_interval_prod μ hF hC hδ hjet W V U U V V
    hW hV hU hU hV hV hbU hbU hbV hbV a (fun r => q*a^2/2*(1-r)) (by fun_prop)
  have hCdata := integrable_canonicalFourthTensor_interval_prod μ hF hC hδ hjet W V U U U V
    hW hV hU hU hU hV hbU hbU hbU hbV a (fun _ => -d*q*a) continuous_const
  exact (hA.add hB).add hCdata

theorem genericFourthCombination_interval_data
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsFiniteMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W U V : Ω → Vector p) (hW : Measurable W) (hU : Measurable U) (hV : Measurable V)
    (hbU : ∀ᵐ ω ∂μ, ‖U ω‖ ≤ δ) (hbV : ∀ᵐ ω ∂μ, ‖V ω‖ ≤ δ) (q a c b d : ℝ) :
    Integrable (fun ω => ∫ r in (0 : ℝ)..1, genericFourthCombination F (W ω) (U ω) (V ω) q a c b d r) μ ∧
    IntervalIntegrable (fun r => ∫ ω, genericFourthCombination F (W ω) (U ω) (V ω) q a c b d r ∂μ) volume 0 1 ∧
    (∫ ω, (∫ r in (0 : ℝ)..1, genericFourthCombination F (W ω) (U ω) (V ω) q a c b d r) ∂μ) =
      ∫ r in (0 : ℝ)..1, (∫ ω, genericFourthCombination F (W ω) (U ω) (V ω) q a c b d r ∂μ) := by
  have hi := integrable_genericFourthCombination_interval_prod μ hF hC hδ hjet W U V hW hU hV hbU hbV q a c b d
  refine ⟨?_, ?_, ?_⟩
  · simpa only [intervalIntegral.integral_of_le zero_le_one] using hi.integral_prod_left
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one]
    exact hi.integral_prod_right
  · simpa only [intervalIntegral.integral_of_le zero_le_one] using integral_integral_swap hi

set_option maxHeartbeats 200000 in
theorem genericRowFourthTotal_eq_pair_interval
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (q a c b d : ℝ) :
    genericRowFourthTotal μ F T x q a c b d =
      ∫ z : Ω × Ω, (∫ r in (0 : ℝ)..1, genericFourthCombination F x (T z.1) (T z.2) q a c b d r) ∂μ.prod μ := by
  let IA := fun z : Ω × Ω => ∫ r in (0 : ℝ)..1,
    (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*canonicalFourthTensor F (x+(a*r) • T z.2) (T z.2) (T z.2) (T z.2) (T z.2)
  let IB := fun z : Ω × Ω => ∫ r in (0 : ℝ)..1,
    (q*a^2/2*(1-r))*canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.2) (T z.2)
  let IC := fun z : Ω × Ω => ∫ r in (0 : ℝ)..1,
    (-d*q*a)*canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.1) (T z.2)
  have hb1 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.1‖ ≤ δ := Measure.quasiMeasurePreserving_fst.ae hbound
  have hb2 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hA := integrable_canonicalFourthTensor_interval_prod (μ.prod μ) hF hC hδ hjet
    (fun _ => x) (fun z => T z.2) (fun z => T z.2) (fun z => T z.2) (fun z => T z.2) (fun z => T z.2)
    measurable_const (hT.comp measurable_snd) (hT.comp measurable_snd) (hT.comp measurable_snd)
    (hT.comp measurable_snd) (hT.comp measurable_snd) hb2 hb2 hb2 hb2 a
    (fun r => c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2) (by fun_prop)
  have hB := integrable_canonicalFourthTensor_interval_prod (μ.prod μ) hF hC hδ hjet
    (fun _ => x) (fun z => T z.2) (fun z => T z.1) (fun z => T z.1) (fun z => T z.2) (fun z => T z.2)
    measurable_const (hT.comp measurable_snd) (hT.comp measurable_fst) (hT.comp measurable_fst)
    (hT.comp measurable_snd) (hT.comp measurable_snd) hb1 hb1 hb2 hb2 a (fun r => q*a^2/2*(1-r)) (by fun_prop)
  have hCdata := integrable_canonicalFourthTensor_interval_prod (μ.prod μ) hF hC hδ hjet
    (fun _ => x) (fun z => T z.2) (fun z => T z.1) (fun z => T z.1) (fun z => T z.1) (fun z => T z.2)
    measurable_const (hT.comp measurable_snd) (hT.comp measurable_fst) (hT.comp measurable_fst)
    (hT.comp measurable_fst) (hT.comp measurable_snd) hb1 hb1 hb1 hb2 a (fun _ => -d*q*a) continuous_const
  have hiA : Integrable IA (μ.prod μ) := by simpa only [IA, intervalIntegral.integral_of_le zero_le_one] using hA.integral_prod_left
  have hiB : Integrable IB (μ.prod μ) := by simpa only [IB, intervalIntegral.integral_of_le zero_le_one] using hB.integral_prod_left
  have hiC : Integrable IC (μ.prod μ) := by simpa only [IC, intervalIntegral.integral_of_le zero_le_one] using hCdata.integral_prod_left
  have eA : genericRowFourthRemainder μ F T x a c b = ∫ z, IA z ∂μ.prod μ := by
    simp only [IA, canonicalFourthTensor_diagonal]
    simpa only [measureReal_univ_eq_one, one_smul, genericRowFourthRemainder] using
      (integral_fun_snd (μ := μ) (ν := μ) (fun ω => ∫ r in (0 : ℝ)..1,
        (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*canonicalDiagonal F 4 (x+(a*r) • T ω) (T ω))).symm
  have eB : genericFourthRowB μ F T x q a = ∫ z, IB z ∂μ.prod μ := by
    unfold genericFourthRowB IB
    rw [← integral_const_mul]
    apply integral_congr_ae
    apply ae_of_all
    intro z
    change q*a^2/2*(∫ r in (0 : ℝ)..1, (1-r)*canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.2) (T z.2)) = _
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro r _
    exact (mul_assoc _ _ _).symm
  have eC : genericFourthRowC μ F T x q a d = ∫ z, IC z ∂μ.prod μ := by
    unfold genericFourthRowC IC
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ fun z => (intervalIntegral.integral_const_mul _ _).symm
  unfold genericRowFourthTotal
  rw [eA,eB,eC, ← integral_add (f := IA) (g := IB) hiA hiB,
    ← integral_add (f := fun z => IA z+IB z) (g := IC) (hiA.add hiB) hiC]
  apply integral_congr_ae
  filter_upwards [hA.prod_right_ae,hB.prod_right_ae,hCdata.prod_right_ae] with z hzA hzB hzC
  change IA z+IB z+IC z = _
  let fA := fun r : ℝ => (c*a^4/6*(1-r)^3+b*a^3/2*(1-r)^2)*
    canonicalFourthTensor F (x+(a*r) • T z.2) (T z.2) (T z.2) (T z.2) (T z.2)
  let fB := fun r : ℝ => q*a^2/2*(1-r)*
    canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.2) (T z.2)
  let fC := fun r : ℝ => -d*q*a*
    canonicalFourthTensor F (x+(a*r) • T z.2) (T z.1) (T z.1) (T z.1) (T z.2)
  have eAB := integral_add (f := fA) (g := fB) hzA hzB
  have eABC := integral_add (f := fun r => fA r+fB r) (g := fC) (hzA.add hzB) hzC
  simp only [IA,IB,IC,intervalIntegral.integral_of_le zero_le_one]
  exact (eABC.trans (congrArg (fun y : ℝ => y+∫ r in Set.Ioc (0 : ℝ) 1, fC r) eAB)).symm

theorem integral_genericRowFourthTotal_eq_interval
    {B Ω : Type*} [MeasurableSpace B] [MeasurableSpace Ω] {p : ℕ}
    (ρ : Measure B) [IsFiniteMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ 4 F x‖ ≤ C)
    (W : B → Vector p) (hW : Measurable W) (T : Ω → Vector p) (hT : Measurable T)
    (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (q a c b d : ℝ) :
    Integrable (fun z => genericRowFourthTotal μ F T (W z) q a c b d) ρ ∧
    IntervalIntegrable (fun r => ∫ z : B × (Ω × Ω),
      genericFourthCombination F (W z.1) (T z.2.1) (T z.2.2) q a c b d r ∂ρ.prod (μ.prod μ)) volume 0 1 ∧
    (∫ z, genericRowFourthTotal μ F T (W z) q a c b d ∂ρ) =
      ∫ r in (0 : ℝ)..1, (∫ z : B × (Ω × Ω),
        genericFourthCombination F (W z.1) (T z.2.1) (T z.2.2) q a c b d r ∂ρ.prod (μ.prod μ)) := by
  have hb1 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.1‖ ≤ δ := Measure.quasiMeasurePreserving_fst.ae hbound
  have hb2 : ∀ᵐ z : Ω × Ω ∂μ.prod μ, ‖T z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae hbound
  have hd := genericFourthCombination_interval_data (ρ.prod (μ.prod μ)) hF hC hδ hjet
    (W ∘ Prod.fst) (fun z => T z.2.1) (fun z => T z.2.2) (hW.comp measurable_fst)
    (hT.comp (measurable_fst.comp measurable_snd)) (hT.comp (measurable_snd.comp measurable_snd))
    (Measure.quasiMeasurePreserving_snd.ae hb1) (Measure.quasiMeasurePreserving_snd.ae hb2) q a c b d
  have he (z : B) := genericRowFourthTotal_eq_pair_interval μ hF hC hδ hjet T hT hbound (W z) q a c b d
  refine ⟨?_, hd.2.1, ?_⟩
  · exact hd.1.integral_prod_left.congr (ae_of_all _ fun z => (he z).symm)
  · calc
      _ = ∫ z : B, (∫ v : Ω × Ω, (∫ r in (0 : ℝ)..1,
          genericFourthCombination F (W z) (T v.1) (T v.2) q a c b d r) ∂μ.prod μ) ∂ρ :=
        integral_congr_ae (ae_of_all _ he)
      _ = ∫ z : B × (Ω × Ω), (∫ r in (0 : ℝ)..1,
          genericFourthCombination F (W z.1) (T z.2.1) (T z.2.2) q a c b d r) ∂ρ.prod (μ.prod μ) :=
        (integral_prod _ hd.1).symm
      _ = _ := hd.2.2

end
end RectangleCLT.Companion.SplitV4
