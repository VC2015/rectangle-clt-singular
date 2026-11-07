import RectangleCLTCompanion.SplitV4.SlepianDerivative
import RectangleCLTCompanion.SplitV4.PairedCoefficients
import RectangleCLTCompanion.SplitV4.MomentIntegrability
import RectangleCLTCompanion.SplitV4.CopyProjection
import RectangleCLT.BoundedCurvature
import Mathlib.Probability.Independence.Basic

/-! Finite independent-array assembly of the paired Slepian identity.
Each summand is paired with a copy of its own law; no identical-distribution
or symmetry assumption is imposed. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

private theorem independent_pair_copy_map
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X B : Ω → Vector p) (hX : Measurable X) (hB : Measurable B)
    (hind : IndepFun B X μ) :
    (μ.prod μ).map (fun z => (B z.1, (X z.1, X z.2))) =
      (μ.map B).prod ((μ.map X).prod (μ.map X)) := by
  have hpair := (indepFun_iff_map_prod_eq_prod_map_map hB.aemeasurable hX.aemeasurable).mp hind
  have hp := Measure.map_prod_map μ μ (hB.prodMk hX) hX
  calc
    _ = Measure.map MeasurableEquiv.prodAssoc
        ((μ.prod μ).map (Prod.map (fun ω => (B ω, X ω)) X)) := by
      rw [Measure.map_map MeasurableEquiv.prodAssoc.measurable ((hB.prodMk hX).prodMap hX)]
      rfl
    _ = Measure.map MeasurableEquiv.prodAssoc ((μ.map (fun ω => (B ω, X ω))).prod (μ.map X)) :=
      congrArg (Measure.map MeasurableEquiv.prodAssoc) hp.symm
    _ = _ := by rw [hpair, Measure.prodAssoc_prod]

private theorem independent_base_copy_map
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X B : Ω → Vector p) (hX : Measurable X) :
    ((μ.map B).prod (μ.prod μ)).map (fun z => (z.1, (X z.2.1, X z.2.2))) =
      (μ.map B).prod ((μ.map X).prod (μ.map X)) := by
  have hm := Measure.map_prod_map (μ.map B) (μ.prod μ) measurable_id (hX.prodMap hX)
  simpa only [Measure.map_id, ← Measure.map_prod_map μ μ hX hX] using hm.symm

/-- Exact transport of a genuine independent pair and an independent copy
to the product model used by the single-summand Taylor identity. -/
private theorem integral_independent_pair_copy
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X B : Ω → Vector p) (hX : Measurable X) (hB : Measurable B)
    (hind : IndepFun B X μ)
    (K : Vector p × (Vector p × Vector p) → ℝ) (hK : Measurable K) :
    (∫ z : Ω × Ω, K (B z.1, (X z.1, X z.2)) ∂μ.prod μ) =
      ∫ z : Vector p × (Ω × Ω), K (z.1, (X z.2.1, X z.2.2))
        ∂(μ.map B).prod (μ.prod μ) := by
  have hL : Measurable (fun z : Ω × Ω => (B z.1, (X z.1, X z.2))) :=
    (hB.comp measurable_fst).prodMk ((hX.comp measurable_fst).prodMk (hX.comp measurable_snd))
  have hR : Measurable (fun z : Vector p × (Ω × Ω) => (z.1, (X z.2.1, X z.2.2))) :=
    measurable_fst.prodMk ((hX.comp (measurable_fst.comp measurable_snd)).prodMk
      (hX.comp (measurable_snd.comp measurable_snd)))
  calc
    _ = ∫ z, K z ∂(μ.prod μ).map (fun z => (B z.1, (X z.1, X z.2))) :=
      (integral_map hL.aemeasurable hK.aestronglyMeasurable).symm
    _ = ∫ z, K z ∂(μ.map B).prod ((μ.map X).prod (μ.map X)) := by
      rw [independent_pair_copy_map μ X B hX hB hind]
    _ = _ := by
      rw [← independent_base_copy_map μ X B hX]
      exact integral_map hR.aemeasurable hK.aestronglyMeasurable

namespace C4Test
variable {p : ℕ} (f : C4Test p)

/-- The paired summand identity on the original joint probability space,
after proving the independent-base transport. The deleted base may have an
arbitrary law. -/
theorem integral_paired_stein_of_independent_base
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (X B : Ω → Vector p) (hX : Measurable X) (hB : Measurable B)
    (hind : IndepFun B X μ) (hXint : Integrable X μ) (hmean : ∫ ω, X ω ∂μ = 0)
    (a b h : ℝ) (hh : 0 ≤ h) (g : Vector p) :
    let U := fun z : Ω × Ω => a • B z.1 + b • g + a • X z.1
    let Y := fun z : Ω × Ω => pairedTruncatedIncrement (X z.1) (X z.2) h
    (∫ z, f.gradient (U z) (X z.1) ∂μ.prod μ) =
      a / 2 * (∫ z, f.secondDiagonal (U z) (Y z) ∂μ.prod μ) -
        a ^ 3 / 4 * (∫ z, f.trapezoidalRemainder (U z) (Y z) a ∂μ.prod μ) -
        ∫ z, f.gradient (U z) (X z.2 - X z.1 - Y z) ∂μ.prod μ := by
  let V : Vector p → Vector p := fun y => a • y + b • g
  have hV : Measurable V := by fun_prop
  letI : IsProbabilityMeasure (μ.map B) := isProbabilityMeasure_map hB.aemeasurable
  let U : Vector p × (Vector p × Vector p) → Vector p := fun z => V z.1 + a • z.2.1
  let Y : Vector p × (Vector p × Vector p) → Vector p := fun z =>
    pairedTruncatedIncrement z.2.1 z.2.2 h
  have hU : Measurable U := (hV.comp measurable_fst).add
    (measurable_const.smul (measurable_fst.comp measurable_snd))
  have hY : Measurable Y :=
    (measurable_pairedTruncatedIncrement id measurable_id h).comp measurable_snd
  have hG : Measurable (fun z : Vector p × (Vector p × Vector p) => f.gradient (U z) z.2.1) :=
    f.continuous_gradient_eval.measurable.comp (hU.prodMk (measurable_fst.comp measurable_snd))
  have hH : Measurable (fun z => f.secondDiagonal (U z) (Y z)) :=
    f.continuous_secondDiagonal.measurable.comp (hU.prodMk hY)
  have hR : Measurable (fun z => f.trapezoidalRemainder (U z) (Y z) a) :=
    (f.measurable_trapezoidalRemainder a).comp (hU.prodMk hY)
  have hT : Measurable (fun z : Vector p × (Vector p × Vector p) =>
      f.gradient (U z) (z.2.2 - z.2.1 - Y z)) :=
    f.continuous_gradient_eval.measurable.comp (hU.prodMk
      (((measurable_snd.comp measurable_snd).sub (measurable_fst.comp measurable_snd)).sub hY))
  have ht := f.integral_paired_stein_with_independent_base μ (μ.map B) X hX hXint hmean V hV a h hh
  have htG := integral_independent_pair_copy μ X B hX hB hind _ hG
  have htH := integral_independent_pair_copy μ X B hX hB hind _ hH
  have htR := integral_independent_pair_copy μ X B hX hB hind _ hR
  have htT := integral_independent_pair_copy μ X B hX hB hind _ hT
  change (∫ z : Ω × Ω, f.gradient (U (B z.1, (X z.1, X z.2))) (X z.1) ∂μ.prod μ) = _
  rw [htG, htH, htR, htT]
  exact ht

def arrayCopyPoint {Ω : Type*} {n : ℕ} (ξ : Fin n → Ω → Vector p)
    (a b : ℝ) (z : Vector p × (Ω × Ω)) : Vector p :=
  a • sumVector ξ z.2.1 + b • z.1

def arrayCopyIncrement {Ω : Type*} {n : ℕ} (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (h : ℝ) (z : Vector p × (Ω × Ω)) : Vector p :=
  pairedTruncatedIncrement (ξ i z.2.1) (ξ i z.2.2) h

private theorem measurable_arrayCopyPoint {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (a b : ℝ) :
    Measurable (arrayCopyPoint ξ a b) := by
  have hs : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  exact (measurable_const.smul (hs.comp (measurable_fst.comp measurable_snd))).add
    (measurable_const.smul measurable_fst)

private theorem measurable_arrayCopyIncrement {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (i : Fin n) (h : ℝ) :
    Measurable (arrayCopyIncrement ξ i h) :=
  (measurable_pairedTruncatedIncrement (ξ i) (hξ i) h).comp measurable_snd

/-- The actual paired identity for one summand of a finite independent
array, integrated over the other summands and an independent random shift. -/
theorem integral_array_summand_paired
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hInt : ∀ i, Integrable (ξ i) μ)
    (hMean : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (γ : Measure (Vector p)) [IsProbabilityMeasure γ]
    (a b h : ℝ) (hh : 0 ≤ h) (i : Fin n) :
    (∫ z, f.gradient (arrayCopyPoint ξ a b z) (ξ i z.2.1) ∂γ.prod (μ.prod μ)) =
      a / 2 * (∫ z, f.secondDiagonal (arrayCopyPoint ξ a b z)
        (arrayCopyIncrement ξ i h z) ∂γ.prod (μ.prod μ)) -
      a ^ 3 / 4 * (∫ z, f.trapezoidalRemainder (arrayCopyPoint ξ a b z)
        (arrayCopyIncrement ξ i h z) a ∂γ.prod (μ.prod μ)) -
      ∫ z, f.gradient (arrayCopyPoint ξ a b z)
        (ξ i z.2.2 - ξ i z.2.1 - arrayCopyIncrement ξ i h z) ∂γ.prod (μ.prod μ) := by
  let U := arrayCopyPoint ξ a b
  let Y := arrayCopyIncrement ξ i h
  have hU : Measurable U := measurable_arrayCopyPoint ξ hξ a b
  have hY : Measurable Y := measurable_arrayCopyIncrement ξ hξ i h
  have hbound : ∀ z, ‖Y z‖ ≤ h := fun z =>
    norm_pairedTruncatedIncrement_le _ _ hh
  have hN₀ : Integrable (fun z : Ω × Ω => ‖ξ i z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using (hInt i).norm.mul_prod (integrable_const (1 : ℝ))
  have hN₁ : Integrable (fun z : Ω × Ω => ‖ξ i z.2‖) (μ.prod μ) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod (hInt i).norm
  have hM₀ : Integrable (fun z : Vector p × (Ω × Ω) => ‖ξ i z.2.1‖) (γ.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hN₀
  have hM₁ : Integrable (fun z : Vector p × (Ω × Ω) => ‖ξ i z.2.2‖) (γ.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hN₁
  let G := fun z : Vector p × (Ω × Ω) => f.gradient (U z) (ξ i z.2.1)
  let H := fun z : Vector p × (Ω × Ω) => f.secondDiagonal (U z) (Y z)
  let R := fun z : Vector p × (Ω × Ω) => f.trapezoidalRemainder (U z) (Y z) a
  let T := fun z : Vector p × (Ω × Ω) => f.gradient (U z) (ξ i z.2.2 - ξ i z.2.1 - Y z)
  have hG : Integrable G (γ.prod (μ.prod μ)) :=
    f.integrable_gradient_direction_of_norm _ U _ hU
      ((hξ i).comp (measurable_fst.comp measurable_snd)) hM₀
  have hG' : Integrable (fun z : Vector p × (Ω × Ω) => f.gradient (U z) (ξ i z.2.2))
      (γ.prod (μ.prod μ)) := f.integrable_gradient_direction_of_norm _ U _ hU
        ((hξ i).comp (measurable_snd.comp measurable_snd)) hM₁
  have hGY := f.integrable_gradient_eval (γ.prod (μ.prod μ)) U Y hU hY h hbound
  have hH : Integrable H (γ.prod (μ.prod μ)) := f.integrable_secondDiagonal _ U Y hU hY h hbound
  have hR : Integrable R (γ.prod (μ.prod μ)) := f.integrable_trapezoidalRemainder _ U Y hU hY h hbound a
  have hT : Integrable T (γ.prod (μ.prod μ)) := by
    simpa only [T, G, map_sub] using (hG'.sub hG).sub hGY
  have hB : Measurable (leaveOneOut ξ i) := Finset.measurable_sum _ (fun k _ => hξ k)
  have hi : IndepFun (leaveOneOut ξ i) (ξ i) μ := by
    convert hind.indepFun_finset_sum_of_not_mem hξ (Finset.not_mem_erase i Finset.univ) using 1
    funext ω
    simp only [leaveOneOut, Finset.sum_apply]
  have hpoint (g : Vector p) :
      (∫ z, G (g, z) ∂μ.prod μ) =
        a / 2 * (∫ z, H (g, z) ∂μ.prod μ) -
          a ^ 3 / 4 * (∫ z, R (g, z) ∂μ.prod μ) -
          ∫ z, T (g, z) ∂μ.prod μ := by
    have ht := f.integral_paired_stein_of_independent_base μ (ξ i) (leaveOneOut ξ i)
      (hξ i) hB hi (hInt i) (hMean i) a b h hh g
    have heq (ω : Ω) : a • leaveOneOut ξ i ω + b • g + a • ξ i ω =
        a • sumVector ξ ω + b • g := by
      rw [sumVector_eq_leaveOneOut_add ξ i ω, smul_add]
      abel
    dsimp only at ht
    simp_rw [heq] at ht
    exact ht
  have hiA : Integrable (fun g => a / 2 * (∫ z, H (g, z) ∂μ.prod μ) -
      a ^ 3 / 4 * (∫ z, R (g, z) ∂μ.prod μ)) γ :=
    (hH.integral_prod_left.const_mul _).sub (hR.integral_prod_left.const_mul _)
  change (∫ z, G z ∂γ.prod (μ.prod μ)) = _
  calc
    _ = ∫ g, ∫ z, G (g, z) ∂μ.prod μ ∂γ := integral_prod _ hG
    _ = ∫ g, a / 2 * (∫ z, H (g, z) ∂μ.prod μ) -
        a ^ 3 / 4 * (∫ z, R (g, z) ∂μ.prod μ) -
        (∫ z, T (g, z) ∂μ.prod μ) ∂γ := integral_congr_ae (ae_of_all _ hpoint)
    _ = _ := by
      rw [integral_sub hiA hT.integral_prod_left,
        integral_sub (hH.integral_prod_left.const_mul _) (hR.integral_prod_left.const_mul _),
        integral_const_mul, integral_const_mul, ← integral_prod _ hH,
        ← integral_prod _ hR, ← integral_prod _ hT]

private theorem integrable_array_gradient_summand
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hInt : ∀ i, Integrable (ξ i) μ)
    (γ : Measure (Vector p)) [IsProbabilityMeasure γ] (a b : ℝ) (i : Fin n) :
    Integrable (fun z => f.gradient (arrayCopyPoint ξ a b z) (ξ i z.2.1))
      (γ.prod (μ.prod μ)) := by
  have hN : Integrable (fun z : Ω × Ω => ‖ξ i z.1‖) (μ.prod μ) := by
    simpa only [mul_one] using (hInt i).norm.mul_prod (integrable_const (1 : ℝ))
  have hM : Integrable (fun z : Vector p × (Ω × Ω) => ‖ξ i z.2.1‖) (γ.prod (μ.prod μ)) := by
    simpa only [one_mul] using (integrable_const (1 : ℝ)).mul_prod hN
  exact f.integrable_gradient_direction_of_norm _ (arrayCopyPoint ξ a b) _
    (measurable_arrayCopyPoint ξ hξ a b) ((hξ i).comp (measurable_fst.comp measurable_snd)) hM

theorem integral_array_paired_sum
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hInt : ∀ i, Integrable (ξ i) μ)
    (hMean : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (γ : Measure (Vector p)) [IsProbabilityMeasure γ]
    (a b h : ℝ) (hh : 0 ≤ h) :
    (∫ z, f.gradient (arrayCopyPoint ξ a b z) (sumVector ξ z.2.1) ∂γ.prod (μ.prod μ)) =
      a / 2 * (∑ i, ∫ z, f.secondDiagonal (arrayCopyPoint ξ a b z)
        (arrayCopyIncrement ξ i h z) ∂γ.prod (μ.prod μ)) -
      a ^ 3 / 4 * (∑ i, ∫ z, f.trapezoidalRemainder (arrayCopyPoint ξ a b z)
        (arrayCopyIncrement ξ i h z) a ∂γ.prod (μ.prod μ)) -
      ∑ i, ∫ z, f.gradient (arrayCopyPoint ξ a b z)
        (ξ i z.2.2 - ξ i z.2.1 - arrayCopyIncrement ξ i h z) ∂γ.prod (μ.prod μ) := by
  have heq (z : Vector p × (Ω × Ω)) :
      f.gradient (arrayCopyPoint ξ a b z) (sumVector ξ z.2.1) =
        ∑ i, f.gradient (arrayCopyPoint ξ a b z) (ξ i z.2.1) := by
    simp only [sumVector, map_sum]
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ
    (fun i _ => f.integrable_array_gradient_summand μ ξ hξ hInt γ a b i)]
  simp_rw [f.integral_array_summand_paired μ ξ hξ hind hInt hMean γ a b h hh]
  simp only [Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- The complete paired Slepian derivative before rewriting its copy
averages as conditional coefficients. It includes every summand, the actual
independent Gaussian, the conditional large-increment contribution, and the
signed `-t/8` fourth-order remainder. -/
theorem hasDerivAt_arraySlepian_paired
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hInt : ∀ i, Integrable (ξ i) μ)
    (hMean : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 ≤ h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      ((1 / 4 : ℝ) * (∑ i, ∫ z, f.secondDiagonal
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ)) -
        (1 / 2 : ℝ) * (∫ z, f.hessianTrace (A * A.transpose)
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
            ∂(gaussianLaw A).prod (μ.prod μ)) -
        t / 8 * (∑ i, ∫ z, f.trapezoidalRemainder
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ)) -
        (1 / (2 * Real.sqrt t)) * (∑ i, ∫ z, f.gradient
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (ξ i z.2.2 - ξ i z.2.1 - arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ))) t := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  have hWi : Integrable (sumVector ξ) μ := integrable_finset_sum _ (fun i _ => hInt i)
  have hd := f.hasDerivAt_slepianExpectation μ (sumVector ξ) hW hWi.norm A ht ht1
  have hG : Measurable (fun z : Ω × Vector p =>
      f.gradient (slepianPoint (sumVector ξ) t z) (sumVector ξ z.1)) :=
    f.continuous_gradient_eval.measurable.comp
      ((measurable_slepianPoint _ hW t).prodMk (hW.comp measurable_fst))
  have hH : Measurable (fun z : Ω × Vector p =>
      f.hessianTrace (A * A.transpose) (slepianPoint (sumVector ξ) t z)) := by
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul ((f.continuous_hessianCoordinate j k).measurable.comp
      (measurable_slepianPoint _ hW t))
  have hGtransport := integral_copyGaussianProjection (gaussianLaw A) μ _ hG.aestronglyMeasurable
  have hHtransport := integral_copyGaussianProjection (gaussianLaw A) μ _ hH.aestronglyMeasurable
  change (∫ z, f.gradient (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
      (sumVector ξ z.2.1) ∂(gaussianLaw A).prod (μ.prod μ)) = _ at hGtransport
  change (∫ z, f.hessianTrace (A * A.transpose)
      (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
        ∂(gaussianLaw A).prod (μ.prod μ)) = _ at hHtransport
  rw [← hGtransport, ← hHtransport,
    f.integral_array_paired_sum μ ξ hξ hind hInt hMean (gaussianLaw A)
      (Real.sqrt t) (Real.sqrt (1 - t)) h hh] at hd
  have ha : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr ht)
  have hc₂ : (1 / (2 * Real.sqrt t)) * (Real.sqrt t / 2) = (1 / 4 : ℝ) := by
    field_simp [ha]
    ring
  have hc₄ : (1 / (2 * Real.sqrt t)) * ((Real.sqrt t) ^ 3 / 4) = t / 8 := by
    rw [pow_succ, Real.sq_sqrt ht.le]
    field_simp [ha]
    ring
  convert hd using 1
  symm
  calc
    _ = ((1 / (2 * Real.sqrt t)) * (Real.sqrt t / 2)) *
        (∑ i, ∫ z, f.secondDiagonal (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ)) -
      ((1 / (2 * Real.sqrt t)) * ((Real.sqrt t) ^ 3 / 4)) *
        (∑ i, ∫ z, f.trapezoidalRemainder (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ)) -
      (1 / (2 * Real.sqrt t)) * (∑ i, ∫ z, f.gradient
        (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
        (ξ i z.2.2 - ξ i z.2.1 - arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ)) -
      (1 / 2 : ℝ) * (∫ z, f.hessianTrace (A * A.transpose)
        (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          ∂(gaussianLaw A).prod (μ.prod μ)) := by ring
    _ = _ := by rw [hc₂, hc₄]; ring

/-- Full Lemma G.3 in terms of the actual copy-conditional matrix and
large-increment mean. ProductConditional identifies these explicit copy
integrals with conditional expectations, including the whole-array
sigma-field in the canonical independent-array realization. The remainder
is the actual fourth-derivative segment integral and has coefficient
`-t/8`. No zero-skewness, symmetry, rank, or identical-law premise is used. -/
theorem hasDerivAt_arraySlepian
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ) (hInt : ∀ i, Integrable (ξ i) μ)
    (hMean : ∀ i, ∫ ω, ξ i ω ∂μ = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 ≤ h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      ((1 / 2 : ℝ) * (∫ z : Ω × Vector p, f.hessianTrace
          (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
          (slepianPoint (sumVector ξ) t z) ∂μ.prod (gaussianLaw A)) -
        (1 / (2 * Real.sqrt t)) * (∫ z : Ω × Vector p,
          f.gradient (slepianPoint (sumVector ξ) t z) (copyArrayLargeMean μ ξ z.1 h)
            ∂μ.prod (gaussianLaw A)) -
        t / 8 * (∑ i, ∫ z, f.trapezoidalRemainder
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ))) t := by
  have hW : Measurable (sumVector ξ) := Finset.measurable_sum _ (fun i _ => hξ i)
  let S := slepianPoint (sumVector ξ) t
  have hS : Measurable S := measurable_slepianPoint _ hW t
  have hd := f.hasDerivAt_arraySlepian_paired μ ξ hξ hind hInt hMean A h hh ht ht1
  have hT := f.shifted_hessianTrace_copyArrayTruncatedCovariance μ (gaussianLaw A) ξ S hξ hS hh
  have hb := f.shifted_gradient_copyArrayLargeMean μ (gaussianLaw A) ξ S hξ hInt hS hh
  change (∫ z, f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h) (S z)
      ∂μ.prod (gaussianLaw A)) = (1 / 2 : ℝ) * ∑ i, ∫ z,
        f.secondDiagonal (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ) at hT
  change (∫ z, f.gradient (S z) (copyArrayLargeMean μ ξ z.1 h) ∂μ.prod (gaussianLaw A)) =
      ∑ i, ∫ z, f.gradient (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
        (ξ i z.2.2 - ξ i z.2.1 - arrayCopyIncrement ξ i h z)
          ∂(gaussianLaw A).prod (μ.prod μ) at hb
  have hiT := f.integrable_shifted_hessianTrace_copyArrayTruncatedCovariance
    μ (gaussianLaw A) ξ S hξ hS hh
  have hiCov := f.integrable_hessianTrace (μ.prod (gaussianLaw A)) S hS (A * A.transpose)
  have hmCov : Measurable (fun z : Ω × Vector p => f.hessianTrace (A * A.transpose) (S z)) := by
    apply Finset.measurable_sum
    intro j _
    apply Finset.measurable_sum
    intro k _
    exact measurable_const.mul ((f.continuous_hessianCoordinate j k).measurable.comp hS)
  have hCov := integral_copyGaussianProjection (gaussianLaw A) μ _ hmCov.aestronglyMeasurable
  change (∫ z, f.hessianTrace (A * A.transpose)
      (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
        ∂(gaussianLaw A).prod (μ.prod μ)) =
      ∫ z, f.hessianTrace (A * A.transpose) (S z) ∂μ.prod (gaussianLaw A) at hCov
  have hFluct : (∫ z, f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
      (S z) ∂μ.prod (gaussianLaw A)) =
      (1 / 2 : ℝ) * (∑ i, ∫ z, f.secondDiagonal
        (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
        (arrayCopyIncrement ξ i h z) ∂(gaussianLaw A).prod (μ.prod μ)) -
      (∫ z, f.hessianTrace (A * A.transpose)
        (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          ∂(gaussianLaw A).prod (μ.prod μ)) := by
    simp_rw [f.hessianTrace_sub]
    rw [integral_sub (f := fun z => f.hessianTrace (copyArrayTruncatedCovariance μ ξ z.1 h) (S z))
      (g := fun z => f.hessianTrace (A * A.transpose) (S z)) hiT hiCov, hT, ← hCov]
  convert hd using 1
  rw [hFluct, hb]
  ring

/-- The manuscript's ordinary coordinate-fourth-moment and coordinate-
centering hypotheses discharge all genuine first-moment and vector-mean
requirements of the full paired Slepian identity. -/
theorem hasDerivAt_arraySlepian_of_coordinate_fourths
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hfourth : ∀ i j, Integrable (fun ω => ξ i ω j ^ 4) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (A : Matrix (Fin p) (Fin p) ℝ) (h : ℝ) (hh : 0 ≤ h)
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    HasDerivAt (f.slepianExpectation μ (sumVector ξ) A)
      ((1 / 2 : ℝ) * (∫ z : Ω × Vector p, f.hessianTrace
          (copyArrayTruncatedCovariance μ ξ z.1 h - A * A.transpose)
          (slepianPoint (sumVector ξ) t z) ∂μ.prod (gaussianLaw A)) -
        (1 / (2 * Real.sqrt t)) * (∫ z : Ω × Vector p,
          f.gradient (slepianPoint (sumVector ξ) t z) (copyArrayLargeMean μ ξ z.1 h)
            ∂μ.prod (gaussianLaw A)) -
        t / 8 * (∑ i, ∫ z, f.trapezoidalRemainder
          (arrayCopyPoint ξ (Real.sqrt t) (Real.sqrt (1 - t)) z)
          (arrayCopyIncrement ξ i h z) (Real.sqrt t) ∂(gaussianLaw A).prod (μ.prod μ))) t := by
  have hInt (i : Fin n) : Integrable (ξ i) μ :=
    integrable_vector_of_coordinate_fourth_moments μ (ξ i) (hξ i) (hfourth i)
  have hMean (i : Fin n) : (∫ ω, ξ i ω ∂μ) = 0 :=
    integral_vector_eq_zero_of_coordinate_centered μ (ξ i) (hInt i) (hcenter i)
  exact f.hasDerivAt_arraySlepian μ ξ hξ hind hInt hMean A h hh ht ht1

end C4Test
end
end RectangleCLT.Companion.SplitV4
