import RectangleCLTCompanion.TranslatedWeights
import RectangleCLTCompanion.RestorationCoefficients

/-! The actual translated-selector series used to put all fresh-array terms
over one common base.  Both its finite face expansion and its convergence
are exact, including repeated or omitted face indices. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p : ℕ} (s : FaceSmoother p)

/-- The actual null selector times an ordered product of face selectors. -/
def selectorTupleWeight {k : ℕ} (α : Fin k → Face p) (x : Vector p) : ℝ :=
  s.F x * ∏ i, s.pi x (α i)

theorem selectorTupleWeight_nonneg {k : ℕ} (α : Fin k → Face p) (x : Vector p) :
    0 ≤ selectorTupleWeight s α x := by
  unfold selectorTupleWeight
  exact mul_nonneg (s.F_pos x).le
    (Finset.prod_nonneg (fun i _ => (s.weights x).pi_nonneg (α i)))

theorem sum_prod_pi_le_one (k : ℕ) (x : Vector p) :
    (∑ α : Fin k → Face p, ∏ i, s.pi x (α i)) ≤ 1 := by
  rw [← Fintype.sum_pow]
  have hsum0 : 0 ≤ ∑ f, s.pi x f :=
    Finset.sum_nonneg (fun f _ => (s.weights x).pi_nonneg f)
  have hsum1 : (∑ f, s.pi x f) ≤ 1 := by
    have hn := (s.weights x).normalization
    have hF := (s.weights x).F_pos
    change (s.weights x).F + (∑ f, s.pi x f) = 1 at hn
    linarith
  exact pow_le_one₀ hsum0 hsum1

theorem sum_selectorTupleWeight_le_one (k : ℕ) (x : Vector p) :
    (∑ α : Fin k → Face p, selectorTupleWeight s α x) ≤ 1 := by
  unfold selectorTupleWeight
  rw [← Finset.mul_sum]
  calc
    _ ≤ s.F x * 1 := mul_le_mul_of_nonneg_left (sum_prod_pi_le_one s k x) (s.F_pos x).le
    _ ≤ 1 := by simpa only [mul_one] using s.F_le_one x

theorem selectorTupleWeight_le_one {k : ℕ} (α : Fin k → Face p) (x : Vector p) :
    selectorTupleWeight s α x ≤ 1 := by
  exact (Finset.single_le_sum (fun β _ => selectorTupleWeight_nonneg s β x)
    (Finset.mem_univ α)).trans (sum_selectorTupleWeight_le_one s k x)

theorem translationZ_eq_sum_univ (x v : Vector p) :
    translationZ s x v = ∑ f, s.pi x f * translationIncrement s f v := by
  classical
  unfold translationZ
  apply Finset.sum_subset (Finset.subset_univ _)
  intro f _ hf
  simp only [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hf, if_false,
    zero_div, zero_mul]

/-- Exact finite expansion of a power of the common denominator increment. -/
theorem translationZ_pow_eq_sum_tuples (x v : Vector p) (ℓ : ℕ) :
    translationZ s x v ^ ℓ =
      ∑ β : Fin ℓ → Face p, ∏ i,
        (s.pi x (β i) * translationIncrement s (β i) v) := by
  rw [translationZ_eq_sum_univ]
  exact Fintype.sum_pow _ _

/-- The multiplier in a term of the translated finite face expansion. -/
def restorationTranslationCoefficient {k ℓ : ℕ}
    (α : Fin k → Face p) (β : Fin ℓ → Face p) (v : Vector p) : ℝ :=
  Real.exp ((∑ i, FaceSmoother.normalDot (α i) v) / s.bandwidth) *
    ∏ i, translationIncrement s (β i) v

theorem abs_restorationTranslationCoefficient_le {k ℓ : ℕ}
    (α : Fin k → Face p) (β : Fin ℓ → Face p) {v : Vector p} {R : ℝ}
    (_hR : 0 ≤ R) (hv : ‖v‖ ≤ R) :
    |restorationTranslationCoefficient s α β v| ≤
      Real.exp ((k : ℝ) * R / s.bandwidth) *
        (Real.exp (R / s.bandwidth) - 1) ^ ℓ := by
  have he : (∑ i, FaceSmoother.normalDot (α i) v) ≤ (k : ℝ) * R := by
    calc
      _ ≤ ∑ _i : Fin k, R := Finset.sum_le_sum (fun i _ =>
        (le_abs_self _).trans (FaceSmoother.abs_normalDot_le_of_norm_le (α i) hv))
      _ = _ := by simp
  have hp : |∏ i, translationIncrement s (β i) v| ≤
      (Real.exp (R / s.bandwidth) - 1) ^ ℓ := by
    rw [Finset.abs_prod]
    calc
      _ ≤ ∏ _i : Fin ℓ, (Real.exp (R / s.bandwidth) - 1) :=
        Finset.prod_le_prod (fun _ _ => abs_nonneg _)
          (fun i _ => abs_translationIncrement_le s hv (β i))
      _ = _ := by simp
  unfold restorationTranslationCoefficient
  rw [abs_mul, abs_of_pos (Real.exp_pos _)]
  exact mul_le_mul
    (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right he s.bandwidth_pos.le))
    hp (abs_nonneg _) (Real.exp_pos _).le

/-- The order-`ℓ` term, entirely in actual selectors at the common point. -/
def restorationSeriesTerm {k : ℕ} (α : Fin k → Face p)
    (x v : Vector p) (ℓ : ℕ) : ℝ :=
  (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
    ∑ β : Fin ℓ → Face p,
      (selectorTupleWeight s α x * ∏ i, s.pi x (β i)) *
        restorationTranslationCoefficient s α β v

theorem restorationSeriesTerm_eq {k : ℕ} (α : Fin k → Face p)
    (x v : Vector p) (ℓ : ℕ) :
    restorationSeriesTerm s α x v ℓ =
      (selectorTupleWeight s α x *
        Real.exp ((∑ i, FaceSmoother.normalDot (α i) v) / s.bandwidth)) *
      ((-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) * translationZ s x v ^ ℓ) := by
  rw [restorationSeriesTerm, translationZ_pow_eq_sum_tuples]
  unfold restorationTranslationCoefficient
  simp only [Finset.prod_mul_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro β _
  ring

/-- The actual translated selector product is the sum of its common-base
face expansion.  Smallness is an explicit condition on the actual shift. -/
theorem hasSum_restorationSeriesTerm {k : ℕ} (α : Fin k → Face p)
    (x : Vector p) {v : Vector p} {R : ℝ}
    (hR : 0 ≤ R) (hv : ‖v‖ ≤ R) (hsmall : R / s.bandwidth < Real.log 2) :
    HasSum (restorationSeriesTerm s α x v) (selectorTupleWeight s α (x + v)) := by
  have hs := (hasSum_translationZ_binomial s k x hR hv hsmall).mul_left
    (selectorTupleWeight s α x *
      Real.exp ((∑ i, FaceSmoother.normalDot (α i) v) / s.bandwidth))
  have he := F_mul_prod_pi_translation s α x v
  change selectorTupleWeight s α (x + v) =
    (selectorTupleWeight s α x *
      Real.exp ((∑ i, FaceSmoother.normalDot (α i) v) / s.bandwidth)) /
        (1 + translationZ s x v) ^ (k + 1) at he
  rw [he]
  convert hs using 1
  · funext ℓ
    exact restorationSeriesTerm_eq s α x v ℓ
  · ring

/-- The geometric/binomial majorant used after the actual averaged matrix
estimate.  Its constant is finite as soon as `C * η < 1`. -/
theorem hasSum_restoration_matrix_majorant (k : ℕ) {C η : ℝ}
    (hC : 0 ≤ C) (hη : 0 ≤ η) (hsmall : C * η < 1) :
    HasSum (fun ℓ : ℕ => ((k + ℓ).choose ℓ : ℝ) * (C * η) ^ ℓ)
      (1 / (1 - C * η) ^ (k + 1)) := by
  have hs := hasSum_choose_mul_geometric_of_norm_lt_one k
    (r := C * η) (by rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hC hη)]; exact hsmall)
  convert hs using 1
  funext ℓ
  rw [Nat.add_comm k ℓ, Nat.choose_symm_add]

end
end RectangleCLT.Companion
