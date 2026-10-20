import RectangleCLTCompanion.RestorationSeries
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! Domination and integration of the actual common-base selector series.
The dominating function is explicit; integrability is never inferred from a
bound on a potentially undefined Bochner integral. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

theorem abs_restorationSeriesTerm_le {k : ℕ} (α : Fin k → Face p)
    (x : Vector p) {v : Vector p} {R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (ℓ : ℕ) :
    |restorationSeriesTerm s α x v ℓ| ≤
      selectorTupleWeight s α x * Real.exp ((k : ℝ) * R / s.bandwidth) *
        (((k + ℓ).choose ℓ : ℝ) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) := by
  have hsum : (∑ i, FaceSmoother.normalDot (α i) v) ≤ (k : ℝ) * R := by
    calc
      _ ≤ ∑ _i : Fin k, R := Finset.sum_le_sum (fun i _ =>
        (le_abs_self _).trans (FaceSmoother.abs_normalDot_le_of_norm_le (α i) hv))
      _ = _ := by simp
  have he := Real.exp_le_exp.mpr
    (div_le_div_of_nonneg_right hsum s.bandwidth_pos.le)
  have hz := pow_le_pow_left₀ (abs_nonneg (translationZ s x v))
    (abs_translationZ_le s x hR hv) ℓ
  have hW := selectorTupleWeight_nonneg s α x
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  rw [restorationSeriesTerm_eq, abs_mul,
    abs_of_nonneg (mul_nonneg hW (Real.exp_pos _).le)]
  have habs : |(-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * translationZ s x v ^ ℓ| =
      ((k + ℓ).choose ℓ : ℝ) * |translationZ s x v| ^ ℓ := by
    simp [abs_mul, abs_pow]
  rw [habs]
  exact mul_le_mul (mul_le_mul_of_nonneg_left he hW)
    (mul_le_mul_of_nonneg_left hz (Nat.cast_nonneg _)) (by positivity) (by positivity)

/-- All ordered face indices are summed before the domination estimate;
there is no factor counting faces. -/
theorem abs_sum_mul_restorationSeriesTerm_le {k : ℕ}
    (c : (Fin k → Face p) → ℝ) (x : Vector p) {v : Vector p} {R D : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hD : 0 ≤ D)
    (hc : ∀ α, |c α| ≤ D) (ℓ : ℕ) :
    |∑ α : Fin k → Face p, c α * restorationSeriesTerm s α x v ℓ| ≤
      (((k + ℓ).choose ℓ : ℝ) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ) *
        (Real.exp ((k : ℝ) * R / s.bandwidth) * D) := by
  let E := Real.exp ((k : ℝ) * R / s.bandwidth)
  let a := ((k + ℓ).choose ℓ : ℝ) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have ha : 0 ≤ a := mul_nonneg (Nat.cast_nonneg _) (pow_nonneg hη _)
  calc
    _ ≤ ∑ α, |c α| * |restorationSeriesTerm s α x v ℓ| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun α => c α * restorationSeriesTerm s α x v ℓ) Finset.univ
    _ ≤ ∑ α, D * (selectorTupleWeight s α x * E * a) := by
      apply Finset.sum_le_sum
      intro α _
      exact mul_le_mul (hc α) (abs_restorationSeriesTerm_le s α x hR hv ℓ)
        (abs_nonneg _) hD
    _ = (a * (E * D)) * (∑ α, selectorTupleWeight s α x) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro α _
      ring
    _ ≤ (a * (E * D)) * 1 := mul_le_mul_of_nonneg_left
      (sum_selectorTupleWeight_le_one s k x) (by positivity)
    _ = _ := mul_one _

section Measurability

variable {X : Type*} [MeasurableSpace X]

theorem measurable_selectorTupleWeight_comp {k : ℕ} (α : Fin k → Face p)
    (U : X → Vector p) (hU : Measurable U) :
    Measurable (fun a => selectorTupleWeight s α (U a)) := by
  unfold selectorTupleWeight
  exact ((s.continuous_F.measurable.comp hU).mul
    (Finset.measurable_prod _ (fun i _ => (s.continuous_pi (α i)).measurable.comp hU)))

theorem measurable_translationZ_comp (U V : X → Vector p)
    (hU : Measurable U) (hV : Measurable V) :
    Measurable (fun a => translationZ s (U a) (V a)) := by
  unfold translationZ translationIncrement
  exact Finset.measurable_sum _ (fun f _ =>
    ((s.continuous_pi f).measurable.comp hU).mul
      (((((FaceSmoother.continuous_normalDot f).measurable.comp hV).div_const _).exp).sub_const 1))

theorem measurable_restorationSeriesTerm_comp {k : ℕ} (α : Fin k → Face p)
    (U V : X → Vector p) (hU : Measurable U) (hV : Measurable V) (ℓ : ℕ) :
    Measurable (fun a => restorationSeriesTerm s α (U a) (V a) ℓ) := by
  simp_rw [restorationSeriesTerm_eq]
  apply Measurable.mul
  · exact (measurable_selectorTupleWeight_comp s α U hU).mul
      (((Finset.measurable_sum _ (fun i _ =>
        (FaceSmoother.continuous_normalDot (α i)).measurable.comp hV)).div_const _).exp)
  · exact measurable_const.mul ((measurable_translationZ_comp s U V hU hV).pow_const _)

end Measurability

/-- Dominated convergence for the actual translated selector product and
the full finite ordered face sum.  `D` can be the absolute Gaussian score
times a bound on the remaining directions. -/
theorem hasSum_integral_restorationSeries
    {X : Type*} [MeasurableSpace X] (ρ : Measure X) {k : ℕ}
    (c : (Fin k → Face p) → X → ℝ) (U V : X → Vector p) (D : X → ℝ)
    (hc : ∀ α, Measurable (c α)) (hU : Measurable U) (hV : Measurable V)
    (hDi : Integrable D ρ) (hD : ∀ a, 0 ≤ D a)
    (hcb : ∀ α a, |c α a| ≤ D a) {R : ℝ}
    (hR : 0 ≤ R) (hv : ∀ a, ‖V a‖ ≤ R) (hsmall : R / s.bandwidth < Real.log 2) :
    HasSum (fun ℓ : ℕ => ∫ a, ∑ α : Fin k → Face p,
      c α a * restorationSeriesTerm s α (U a) (V a) ℓ ∂ρ)
      (∫ a, ∑ α : Fin k → Face p,
        c α a * selectorTupleWeight s α (U a + V a) ∂ρ) := by
  let η := Real.exp (R / s.bandwidth) - 1
  let E := Real.exp ((k : ℝ) * R / s.bandwidth)
  have hη : 0 ≤ η :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη1 : η < 1 := by
    have hh := Real.exp_lt_exp.mpr hsmall
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hh
    dsimp only [η]
    linarith
  have hs := hasSum_restoration_matrix_majorant k (C := 1) (η := η)
    (by norm_num) hη (by simpa using hη1)
  simp only [one_mul] at hs
  apply hasSum_integral_of_dominated_convergence
    (fun ℓ a => (((k + ℓ).choose ℓ : ℝ) * η ^ ℓ) * (E * D a))
  · intro ℓ
    exact (Finset.measurable_sum _ (fun α _ => (hc α).mul
      (measurable_restorationSeriesTerm_comp s α U V hU hV ℓ))).aestronglyMeasurable
  · intro ℓ
    exact Filter.Eventually.of_forall (fun a =>
      abs_sum_mul_restorationSeriesTerm_le s (fun α => c α a) (U a)
        hR (hv a) (hD a) (fun α => hcb α a) ℓ)
  · exact Filter.Eventually.of_forall (fun a => hs.summable.mul_right (E * D a))
  · have heq (a : X) : (∑' ℓ : ℕ,
        (((k + ℓ).choose ℓ : ℝ) * η ^ ℓ) * (E * D a)) =
        (1 / (1 - η) ^ (k + 1)) * (E * D a) :=
      (hs.mul_right (E * D a)).tsum_eq
    simp_rw [heq]
    exact (hDi.const_mul E).const_mul _
  · exact Filter.Eventually.of_forall (fun a =>
      hasSum_sum (fun α _ => (hasSum_restorationSeriesTerm s α (U a)
        hR (hv a) hsmall).mul_left (c α a)))

end
end RectangleCLT.Companion
