import RectangleCLTCompanion.SplitV4.GenericC4RowIntegrability
import RectangleCLT.BernoulliCommonPoint

/-! Genuine independent-copy and selector averaging for an arbitrary C4
function. The actual second and third derivative moments are restored at
the common full Bernoulli point, using finite-product Fubini and independence.
The argument works for each derivative order at most four. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem continuous_canonicalDiagonal_base {p k : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (hk : k ≤ 4) (v : Vector p) :
    Continuous (fun x => canonicalDiagonal F k x v) :=
  (hF.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)).eval continuous_const

theorem norm_canonicalDiagonal_le {p k : ℕ} (F : Vector p → ℝ) (x v : Vector p)
    {C : ℝ} (hjet : ‖iteratedFDeriv ℝ k F x‖ ≤ C) :
    ‖canonicalDiagonal F k x v‖ ≤ C * ‖v‖ ^ k := by
  calc
    _ ≤ ‖iteratedFDeriv ℝ k F x‖ * ∏ _i : Fin k, ‖v‖ :=
      (iteratedFDeriv ℝ k F x).le_opNorm _
    _ ≤ C * ∏ _i : Fin k, ‖v‖ := mul_le_mul_of_nonneg_right hjet (Finset.prod_nonneg (fun _ _ => norm_nonneg _))
    _ = _ := by simp

theorem genericBernoulliMoment_eq_integral_retained
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) (hk : k ≤ 4) {C δ : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ)
    (x : Vector p) (q a : ℝ) :
    genericBernoulliMoment μ F k T x q a =
      ∫ u, ((1-q)*canonicalDiagonal F k x (T u)+
        q*(∫ v, canonicalDiagonal F k (x+a • T v) (T u) ∂μ)) ∂μ := by
  have h0 := integrable_canonicalDiagonal_bounded μ hF hk (fun _ => x) T
    measurable_const hT hC hδ hjet hbound
  have h1 := integrable_canonicalDiagonal_bounded (μ.prod μ) hF hk
    (fun z => x+a • T z.2) (fun z => T z.1)
    (measurable_const.add (measurable_const.smul (hT.comp measurable_snd)))
    (hT.comp measurable_fst) hC hδ hjet (Measure.quasiMeasurePreserving_fst.ae hbound)
  rw [integral_add (h0.const_mul (1-q)) (h1.integral_prod_left.const_mul q),
    integral_const_mul, integral_const_mul]
  rfl

/-- Actual retained-copy averaging at a common full point, for every
order `k≤4`. The only independence assumption concerns the original rows;
the fresh directions are integrated under the genuine product law. -/
theorem sum_mask_genericBernoulliMoment_commonPoint
    {Ω : Type*} [MeasurableSpace Ω] {p n k : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) (hk : k ≤ 4)
    {C : ℝ} (hC : 0 ≤ C) (hjet : ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (i : Fin n) (x : Vector p) (q a : ℝ) :
    (∑ mask : Kane.Cube n, Kane.maskWeight q mask *
      ∫ ω, genericBernoulliMoment μ F k (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a ∂μ) =
    ∑ mask : Kane.Cube n, Kane.maskWeight q mask *
      ∫ ω, ∫ u, canonicalDiagonal F k (x+a • maskObservationSum ξ mask ω) (ξ i u) ∂μ ∂μ := by
  let W : Kane.Cube n → Ω → Vector p := fun mask ω =>
    x+a • maskObservationSum ξ (Function.update mask i false) ω
  let D : Kane.Cube n → Ω → Ω → ℝ := fun mask ω u =>
    (1-q)*canonicalDiagonal F k (W mask ω) (ξ i u)+
      q*(∫ v, canonicalDiagonal F k (W mask ω+a • ξ i v) (ξ i u) ∂μ)
  let H : Kane.Cube n → Ω → Ω → ℝ := fun mask ω u =>
    canonicalDiagonal F k (x+a • maskObservationSum ξ mask ω) (ξ i u)
  have hW (mask : Kane.Cube n) : Measurable (W mask) :=
    measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ h.measurable _))
  have hD (mask : Kane.Cube n) : Integrable (fun z : Ω × Ω => D mask z.1 z.2) (μ.prod μ) := by
    have h0 := integrable_canonicalDiagonal_bounded (μ.prod μ) hF hk
      (fun z => W mask z.1) (fun z => ξ i z.2)
      ((hW mask).comp measurable_fst) ((h.measurable i).comp measurable_snd)
      hC h.delta_nonneg hjet (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
    have h1 := integrable_canonicalDiagonal_bounded ((μ.prod μ).prod μ) hF hk
      (fun z => W mask z.1.1+a • ξ i z.2) (fun z => ξ i z.1.2)
      (((hW mask).comp (measurable_fst.comp measurable_fst)).add
        (measurable_const.smul ((h.measurable i).comp measurable_snd)))
      ((h.measurable i).comp (measurable_snd.comp measurable_fst)) hC h.delta_nonneg hjet
      (Measure.quasiMeasurePreserving_fst.ae (Measure.quasiMeasurePreserving_snd.ae (h.bounded i)))
    exact (h0.const_mul (1-q)).add (h1.integral_prod_left.const_mul q)
  have hH (mask : Kane.Cube n) : Integrable (fun z : Ω × Ω => H mask z.1 z.2) (μ.prod μ) :=
    integrable_canonicalDiagonal_bounded (μ.prod μ) hF hk _ _
      (measurable_const.add (measurable_const.smul
        ((measurable_maskObservationSum ξ h.measurable mask).comp measurable_fst)))
      ((h.measurable i).comp measurable_snd) hC h.delta_nonneg hjet
      (Measure.quasiMeasurePreserving_snd.ae (h.bounded i))
  have he (mask : Kane.Cube n) (ω : Ω) :
      genericBernoulliMoment μ F k (ξ i) (W mask ω) q a = ∫ u, D mask ω u ∂μ :=
    genericBernoulliMoment_eq_integral_retained μ hF hk hC h.delta_nonneg hjet
      (ξ i) (h.measurable i) (h.bounded i) (W mask ω) q a
  have hfresh (u : Ω) :
      (∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ ω, D mask ω u ∂μ) =
        ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ ω, H mask ω u ∂μ :=
    sum_mask_freshCopy_average μ ξ h.measurable h.independent h.bounded i q a x
      (fun y => canonicalDiagonal F k y (ξ i u)) (continuous_canonicalDiagonal_base hF hk _)
      (C*‖ξ i u‖^k) (fun y => norm_canonicalDiagonal_le F y _ (hjet y))
  change (∑ mask : Kane.Cube n, Kane.maskWeight q mask *
    ∫ ω, genericBernoulliMoment μ F k (ξ i) (W mask ω) q a ∂μ) = _
  simp_rw [he]
  calc
    _ = ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ u, ∫ ω, D mask ω u ∂μ ∂μ := by
      apply Finset.sum_congr rfl
      intro mask _
      congr 1
      exact integral_integral_swap (hD mask)
    _ = ∫ u, ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ ω, D mask ω u ∂μ ∂μ := by
      rw [integral_finset_sum Finset.univ (fun mask _ => (hD mask).integral_prod_right.const_mul _)]
      simp only [integral_const_mul]
    _ = ∫ u, ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ ω, H mask ω u ∂μ ∂μ := by
      exact integral_congr_ae (ae_of_all _ hfresh)
    _ = ∑ mask : Kane.Cube n, Kane.maskWeight q mask * ∫ u, ∫ ω, H mask ω u ∂μ ∂μ := by
      rw [integral_finset_sum Finset.univ (fun mask _ => (hH mask).integral_prod_right.const_mul _)]
      simp only [integral_const_mul]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro mask _
      congr 1
      exact (integral_integral_swap (hH mask)).symm

end
end RectangleCLT.Companion.SplitV4
