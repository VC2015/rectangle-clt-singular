import RectangleCLTCompanion.SplitV4.GenericC4RowTaylor

/-! The two second-order identities used before the signed-Hessian formula
in the printed B.1 proof (frozen manuscript, lines 2067--2075).  The test
has its actual Fréchet derivatives; all expectations below are genuine
integrals.  These are intermediate identities, not comparison premises. -/

open MeasureTheory
open scoped BigOperators Interval

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem canonical_value_taylor_two {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x v : Vector p) (a : ℝ) :
    F (x+a • v)-(F x+a*canonicalDiagonal F 1 x v) =
      ∫ r in (0 : ℝ)..1, a^2*(1-r)*canonicalDiagonal F 2 (x+(a*r) • v) v := by
  have hc : Continuous (fun r => canonicalDiagonal F 2 (x+r • v) v) :=
    ((hF.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast (by decide : (2 : ℕ) ≤ 4))).comp
      (show Continuous (fun r : ℝ => x+r • v) by fun_prop)).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_two
    (fun r => canonicalDiagonal F 0 (x+r • v) v)
    (fun r => canonicalDiagonal F 1 (x+r • v) v)
    (fun r => canonicalDiagonal F 2 (x+r • v) v)
    (fun r => by simpa only [one_mul] using
      hasDerivAt_canonicalDiagonal_segment hF (k := 0) (by decide) x v 1 r)
    (fun r => by simpa only [one_mul] using
      hasDerivAt_canonicalDiagonal_segment hF (k := 1) (by decide) x v 1 r) hc a
  simpa only [canonicalDiagonal, iteratedFDeriv_zero_apply, zero_smul, add_zero] using hh

theorem canonical_gradient_taylor_one {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (x v : Vector p) (a : ℝ) :
    canonicalDiagonal F 1 (x+a • v) v-canonicalDiagonal F 1 x v =
      ∫ r in (0 : ℝ)..1, a*canonicalDiagonal F 2 (x+(a*r) • v) v := by
  have hc : Continuous (fun r => canonicalDiagonal F 2 (x+r • v) v) :=
    ((hF.continuous_iteratedFDeriv (m := 2) (by exact_mod_cast (by decide : (2 : ℕ) ≤ 4))).comp
      (show Continuous (fun r : ℝ => x+r • v) by fun_prop)).eval continuous_const
  have hh := RectangleCLT.Companion.integral_taylor_one
    (fun r => canonicalDiagonal F 1 (x+r • v) v)
    (fun r => canonicalDiagonal F 2 (x+r • v) v)
    (fun r => by simpa only [one_mul] using
      hasDerivAt_canonicalDiagonal_segment hF (k := 1) (by decide) x v 1 r) hc a
  simpa only [zero_smul, add_zero] using hh

theorem integrable_canonicalDiagonal_interval_prod
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (hk : k ≤ 4) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    Integrable (fun y : Ω × ℝ => K y.2*canonicalDiagonal F k (x+(a*y.2) • T y.1) (T y.1))
      (μ.prod (volume.restrict (Set.Ioc (0 : ℝ) 1))) := by
  obtain ⟨M0,hM0⟩ := (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1)).bddAbove_image hK.norm.continuousOn
  let M := max 0 M0
  have hM : 0 ≤ M := le_max_left _ _
  have hKb (r : ℝ) (hr : r ∈ Set.Ioc (0 : ℝ) 1) : ‖K r‖ ≤ M :=
    (hM0 (Set.mem_image_of_mem _ ⟨hr.1.le,hr.2⟩)).trans (le_max_right _ _)
  have hpoint : Measurable (fun y : Ω × ℝ => x+(a*y.2) • T y.1) :=
    measurable_const.add ((measurable_const.mul measurable_snd).smul (hT.comp measurable_fst))
  have hEval : Continuous (fun z : Vector p × Vector p => canonicalDiagonal F k z.1 z.2) :=
    ((hF.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)).comp continuous_fst).eval
      (continuous_pi (fun _ => continuous_snd))
  have hm : Measurable (fun y : Ω × ℝ => K y.2*canonicalDiagonal F k (x+(a*y.2) • T y.1) (T y.1)) :=
    (hK.measurable.comp measurable_snd).mul
      (hEval.measurable.comp (hpoint.prodMk (hT.comp measurable_fst)))
  apply (integrable_const (M*(C*δ^k))).mono' hm.aestronglyMeasurable
  filter_upwards [Measure.quasiMeasurePreserving_fst.ae hbound,
    Measure.quasiMeasurePreserving_snd.ae (ae_restrict_mem measurableSet_Ioc)] with y hy hyr
  rw [norm_mul]
  apply mul_le_mul (hKb y.2 hyr) _ (norm_nonneg _) hM
  calc
    _ ≤ ‖iteratedFDeriv ℝ k F (x+(a*y.2) • T y.1)‖*∏ _i : Fin k, ‖T y.1‖ :=
      (iteratedFDeriv ℝ k F _).le_opNorm _
    _ ≤ C*∏ _i : Fin k, δ := mul_le_mul (hjet _)
      (Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun _ _ => hy))
      (Finset.prod_nonneg (fun _ _ => norm_nonneg _)) hC
    _ = _ := by simp

theorem canonicalDiagonal_interval_fubini
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (hk : k ≤ 4) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (a : ℝ) (K : ℝ → ℝ) (hK : Continuous K) :
    (∫ ω, (∫ r in (0 : ℝ)..1, K r*canonicalDiagonal F k (x+(a*r) • T ω) (T ω)) ∂μ) =
      ∫ r in (0 : ℝ)..1, K r*(∫ ω, canonicalDiagonal F k (x+(a*r) • T ω) (T ω) ∂μ) := by
  have hi := integrable_canonicalDiagonal_interval_prod μ hF hk hC hδ hjet T hT hbound x a K hK
  simpa only [intervalIntegral.integral_of_le zero_le_one, integral_const_mul] using
    integral_integral_swap (μ := μ) (ν := volume.restrict (Set.Ioc (0 : ℝ) 1))
      (f := fun ω r => K r*canonicalDiagonal F k (x+(a*r) • T ω) (T ω)) hi

theorem centered_value_hessian_identity
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (a : ℝ) :
    (∫ ω, F (x+a • T ω) ∂μ)-F x =
      a^2*∫ r in (0 : ℝ)..1, (1-r)*(∫ ω, canonicalDiagonal F 2 (x+(a*r) • T ω) (T ω) ∂μ) := by
  have hv := integrable_canonicalValue_shifted_bounded μ hF hC hδ hjet T hT hbound x a
  have h1 := integrable_canonicalDiagonal_bounded μ hF (by decide) (fun _ => x) T
    measurable_const hT hC hδ (hjet 1 (by decide) (by decide)) hbound
  have hz := integral_canonicalLinear_zero μ F T hT hbound hc x
  have he := integral_congr_ae (μ := μ) (ae_of_all _ fun ω => canonical_value_taylor_two hF x (T ω) a)
  rw [integral_sub (f := fun ω => F (x+a • T ω))
    (g := fun ω => F x+a*canonicalDiagonal F 1 x (T ω)) hv
      ((integrable_const (F x)).add (h1.const_mul a)),
    integral_add (f := fun _ : Ω => F x) (g := fun ω => a*canonicalDiagonal F 1 x (T ω))
      (integrable_const _) (h1.const_mul a), integral_const_mul] at he
  simp only [integral_const, measureReal_univ_eq_one, one_smul, hz, mul_zero, add_zero] at he
  rw [canonicalDiagonal_interval_fubini μ hF (by decide) hC hδ (hjet 2 (by decide) (by decide))
    T hT hbound x a (fun r => a^2*(1-r)) (by fun_prop)] at he
  rw [← intervalIntegral.integral_const_mul]
  convert he using 1 <;> congr 1 <;> funext r <;> ring

theorem centered_gradient_hessian_identity
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (hc : ∀ j, (∫ ω, T ω j ∂μ) = 0) (x : Vector p) (a : ℝ) :
    (∫ ω, canonicalDiagonal F 1 (x+a • T ω) (T ω) ∂μ) =
      a*∫ r in (0 : ℝ)..1, (∫ ω, canonicalDiagonal F 2 (x+(a*r) • T ω) (T ω) ∂μ) := by
  have hpoint : Measurable (fun ω => x+a • T ω) := measurable_const.add (measurable_const.smul hT)
  have h0 := integrable_canonicalDiagonal_bounded μ hF (by decide) (fun _ => x) T
    measurable_const hT hC hδ (hjet 1 (by decide) (by decide)) hbound
  have h1 := integrable_canonicalDiagonal_bounded μ hF (by decide) (fun ω => x+a • T ω) T
    hpoint hT hC hδ (hjet 1 (by decide) (by decide)) hbound
  have hz := integral_canonicalLinear_zero μ F T hT hbound hc x
  have he := integral_congr_ae (μ := μ) (ae_of_all _ fun ω => canonical_gradient_taylor_one hF x (T ω) a)
  rw [integral_sub h1 h0, hz, sub_zero] at he
  rw [canonicalDiagonal_interval_fubini μ hF (by decide) hC hδ (hjet 2 (by decide) (by decide))
    T hT hbound x a (fun _ => a) continuous_const] at he
  simpa only [intervalIntegral.integral_const_mul] using he

end
end RectangleCLT.Companion.SplitV4.Printed
