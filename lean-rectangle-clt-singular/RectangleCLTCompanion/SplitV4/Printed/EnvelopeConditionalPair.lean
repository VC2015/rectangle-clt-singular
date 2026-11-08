import RectangleCLTCompanion.SplitV4.RestorationConditionalBudgets
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-! Literal conditional Cauchy--Schwarz displayed before B.1/B.2,
appx-an:pair-contraction (frozen lines 1941--1959). Integrability of the
actual squared projections is retained. A countable dense set gives a
single exceptional null set for the conditional quadratic inequality. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem sq_le_mul_of_nonnegative_quadratic {A B C : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hquad : ∀ t : ℝ, 0 ≤ A*t^2-2*B*t+C) : B^2 ≤ A*C := by
  by_cases ha : A = 0
  · by_cases hb : B = 0
    · simp [ha, hb]
    · have hp : 0 < B := lt_of_le_of_ne hB (Ne.symm hb)
      have hh := hquad ((C+1)/(2*B))
      have he : A*((C+1)/(2*B))^2-2*B*((C+1)/(2*B))+C = -1 := by
        rw [ha]
        field_simp
        <;> ring
      rw [he] at hh
      linarith
  · have hp : 0 < A := lt_of_le_of_ne hA (Ne.symm ha)
    have hh := mul_nonneg hA (hquad (B/A))
    have he : A*(A*(B/A)^2-2*B*(B/A)+C) = A*C-B^2 := by
      field_simp
      <;> ring
    rw [he] at hh
    linarith

theorem conditional_finite_cauchy_schwarz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (X Y : Fin n → Ω → ℝ) (hX : ∀ i, @Measurable Ω ℝ mΩ _ (X i))
    (hY : ∀ i, @Measurable Ω ℝ mΩ _ (Y i))
    (hX2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (hY2 : ∀ i, Integrable (fun ω => (Y i ω)^2) μ) :
    ∀ᵐ ω ∂μ,
      (μ[(fun z => ∑ i, |X i z*Y i z|)|H]) ω ≤
        Real.sqrt ((μ[(fun z => ∑ i, (X i z)^2)|H]) ω*
          (μ[(fun z => ∑ i, (Y i z)^2)|H]) ω) := by
  letI : MeasurableSpace Ω := mΩ
  let P : Ω → ℝ := fun z => ∑ i, (X i z)^2
  let Q : Ω → ℝ := fun z => ∑ i, |X i z*Y i z|
  let R : Ω → ℝ := fun z => ∑ i, (Y i z)^2
  have hP : Integrable P μ := integrable_finset_sum _ (fun i _ => hX2 i)
  have hR : Integrable R μ := integrable_finset_sum _ (fun i _ => hY2 i)
  have hprod (i : Fin n) : Integrable (fun z => |X i z*Y i z|) μ := by
    apply (((hX2 i).add (hY2 i)).div_const 2).mono'
      (((hX i).mul (hY i)).abs.aestronglyMeasurable)
    apply ae_of_all
    intro z
    simp only [Real.norm_eq_abs, abs_abs, Pi.add_apply]
    rw [abs_mul]
    nlinarith [sq_nonneg (|X i z|-|Y i z|), sq_abs (X i z), sq_abs (Y i z)]
  have hQ : Integrable Q μ := integrable_finset_sum _ (fun i _ => hprod i)
  have hnonneg (t : ℝ) : ∀ᵐ ω ∂μ,
      0 ≤ t^2*(μ[P|H]) ω-2*t*(μ[Q|H]) ω+(μ[R|H]) ω := by
    let S : Ω → ℝ := fun z => t^2*P z-2*t*Q z+R z
    have hS : Integrable S μ := ((hP.const_mul _).sub (hQ.const_mul _)).add hR
    have hspos : ∀ z, 0 ≤ S z := by
      intro z
      have he : S z = ∑ i, (t*|X i z|-|Y i z|)^2 := by
        dsimp only [S,P,Q,R]
        simp only [Finset.mul_sum, ← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro i _
        rw [abs_mul]
        nlinarith [sq_abs (X i z), sq_abs (Y i z)]
      rw [he]
      exact Finset.sum_nonneg (fun _ _ => sq_nonneg _)
    have hc := condExp_nonneg (m := H) (μ := μ) (ae_of_all _ hspos)
    have hcomb := condExp_real_linear_combination (mΩ := mΩ) μ H
      (![t^2,-2*t,1] : Fin 3 → ℝ) (![P,Q,R] : Fin 3 → Ω → ℝ) (by
        intro i
        fin_cases i <;> first | exact hP | exact hQ | exact hR)
    have he : (fun z => ∑ j : Fin 3, (![t^2,-2*t,1] : Fin 3 → ℝ) j*
        (![P,Q,R] : Fin 3 → Ω → ℝ) j z) = S := by
      funext z
      simp [Fin.sum_univ_succ, S]
      <;> ring
    rw [he] at hcomb
    filter_upwards [hc,hcomb] with ω hω heq
    rw [heq] at hω
    simp [Fin.sum_univ_succ] at hω
    convert hω using 1 <;> ring
  have hq : ∀ q : ℚ, ∀ᵐ ω ∂μ,
      0 ≤ (q : ℝ)^2*(μ[P|H]) ω-2*(q : ℝ)*(μ[Q|H]) ω+(μ[R|H]) ω := fun q => hnonneg q
  have hPpos := condExp_nonneg (m := H) (μ := μ)
    (ae_of_all _ (show ∀ z, 0 ≤ P z from fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hQpos := condExp_nonneg (m := H) (μ := μ)
    (ae_of_all _ (show ∀ z, 0 ≤ Q z from fun z => Finset.sum_nonneg (fun _ _ => abs_nonneg _)))
  have hRpos := condExp_nonneg (m := H) (μ := μ)
    (ae_of_all _ (show ∀ z, 0 ≤ R z from fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  filter_upwards [ae_all_iff.mpr hq,hPpos,hQpos,hRpos] with ω hω hp hq0 hr
  simp only [Pi.zero_apply] at hp hq0 hr
  have hcont : Continuous (fun t : ℝ => t^2*(μ[P|H]) ω-2*t*(μ[Q|H]) ω+(μ[R|H]) ω) := by fun_prop
  have hc := isClosed_le (show Continuous (fun _ : ℝ => (0 : ℝ)) from continuous_const) hcont
  have hrange : Set.range ((↑) : ℚ → ℝ) ⊆
      {t : ℝ | 0 ≤ t^2*(μ[P|H]) ω-2*t*(μ[Q|H]) ω+(μ[R|H]) ω} := by
    rintro _ ⟨q,rfl⟩
    exact hω q
  have hall : ∀ t : ℝ, 0 ≤ t^2*(μ[P|H]) ω-2*t*(μ[Q|H]) ω+(μ[R|H]) ω :=
    fun t => hc.closure_subset_iff.mpr hrange (Rat.denseRange_cast t)
  have hsq := sq_le_mul_of_nonnegative_quadratic hp hq0 hr (fun t => by
    convert hall t using 1 <;> ring)
  have hsqrt := Real.sq_sqrt (mul_nonneg hp hr)
  have hsqrtpos := Real.sqrt_nonneg ((μ[P|H]) ω*(μ[R|H]) ω)
  change (μ[Q|H]) ω ≤ Real.sqrt ((μ[P|H]) ω*(μ[R|H]) ω)
  nlinarith

theorem conditional_finite_pair_contraction
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (X Y : Fin n → Ω → ℝ) (hX : ∀ i, @Measurable Ω ℝ mΩ _ (X i))
    (hY : ∀ i, @Measurable Ω ℝ mΩ _ (Y i))
    (hX2 : ∀ i, Integrable (fun ω => (X i ω)^2) μ)
    (hY2 : ∀ i, Integrable (fun ω => (Y i ω)^2) μ)
    (hbX : ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, (X i z)^2)|H]) ω ≤ 1)
    (hbY : ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, (Y i z)^2)|H]) ω ≤ 1) :
    ∀ᵐ ω ∂μ, (μ[(fun z => ∑ i, |X i z*Y i z|)|H]) ω ≤ 1 := by
  letI : MeasurableSpace Ω := mΩ
  have hc := conditional_finite_cauchy_schwarz (mΩ := mΩ) μ H hH X Y hX hY hX2 hY2
  have hp := condExp_nonneg (m := H) (μ := μ)
    (ae_of_all _ (show ∀ z, 0 ≤ ∑ i, (X i z)^2 from fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  have hr := condExp_nonneg (m := H) (μ := μ)
    (ae_of_all _ (show ∀ z, 0 ≤ ∑ i, (Y i z)^2 from fun z => Finset.sum_nonneg (fun _ _ => sq_nonneg _)))
  filter_upwards [hc,hbX,hbY,hp,hr] with ω hω hx hy hx0 hy0
  refine hω.trans ?_
  apply (Real.sqrt_le_one).mpr
  nlinarith [mul_le_mul hx hy hy0 (by norm_num : (0 : ℝ) ≤ 1)]

end
end RectangleCLT.Companion.SplitV4.Printed
