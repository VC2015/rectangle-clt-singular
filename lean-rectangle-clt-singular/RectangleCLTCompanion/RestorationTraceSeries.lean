import RectangleCLTCompanion.RestorationIntegration
import RectangleCLTCompanion.RestorationMatrixBound

/-! Exact coefficient extraction for the actual fresh-array/Gaussian
experiment.  This is the common-base trace series, pointwise in the external
base randomness.  In particular no conditional concentration is used. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r n k : ℕ} {Ξ : Type*} [MeasurableSpace Ξ]

private theorem measurable_affine (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) :
    Measurable (fun g => A.mulVec g + x) := by
  have hm : Measurable (fun g : Vector r => A.mulVec g) := by
    apply measurable_pi_lambda
    intro l
    change Measurable (fun g : Vector r => ∑ j, A l j * g j)
    exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))
  exact hm.add measurable_const

theorem measurable_restorationTranslationCoefficient_comp (s : FaceSmoother p)
    {X : Type*} [MeasurableSpace X] {ℓ : ℕ}
    (α : Fin k → Face p) (β : Fin ℓ → Face p)
    (v : X → Vector p) (hv : Measurable v) :
    Measurable (fun a => restorationTranslationCoefficient s α β (v a)) := by
  unfold restorationTranslationCoefficient translationIncrement
  exact (((Finset.measurable_sum _ (fun j _ =>
      (FaceSmoother.continuous_normalDot (α j)).measurable.comp hv)).div_const _).exp).mul
    (Finset.measurable_prod _ (fun j _ =>
      (((FaceSmoother.continuous_normalDot (β j)).measurable.comp hv).div_const _).exp.sub_const 1))

theorem measurable_repeatedDirectionScore_product
    (Z : Ξ → Vector r) (hZ : Measurable Z) :
    Measurable (fun ag : Ξ × Vector r => repeatedDirectionScore ag.2 (Z ag.1)) := by
  unfold repeatedDirectionScore faceDot vectorNormSq
  exact ((Finset.measurable_sum _ (fun j _ =>
    ((measurable_pi_apply j).comp (hZ.comp measurable_fst)).mul
      ((measurable_pi_apply j).comp measurable_snd))).pow_const 2).sub
    (Finset.measurable_sum _ (fun j _ =>
      ((measurable_pi_apply j).comp (hZ.comp measurable_fst)).pow_const 2))

def fixedRestorationTraceOrder (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (c : Fin n → (Fin k → Face p) → Ξ → ℝ)
    (v : Fin n → Ξ → Vector p) (ℓ : ℕ) : ℝ :=
  (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
    ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      Matrix.trace (restorationCoefficient μ Z
        (fun i a => c i α a * restorationTranslationCoefficient s α β (v i a)) *
          weightedScore (standardGaussian r) id
            (fun g => selectorTupleWeight s (Fin.append α β) (A.mulVec g + x)))

def fixedRestorationTranslatedExpectation (s : FaceSmoother p) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (c : Fin n → (Fin k → Face p) → Ξ → ℝ)
    (v : Fin n → Ξ → Vector p) : ℝ :=
  ∑ i, ∫ ag : Ξ × Vector r, ∑ α : Fin k → Face p,
    (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
      selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1)
        ∂μ.prod (standardGaussian r)

private theorem sum_three_rotate {ι κ τ : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    (f : ι → κ → τ → ℝ) :
    (∑ i, ∑ a, ∑ b, f i a b) = ∑ a, ∑ b, ∑ i, f i a b := by
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_comm

/-- At each order, finite face sums and actual integrals give exactly the
summed coefficient trace.  Bounded multipliers may depend on every fresh
direction, and are not assumed independent of the repeated pair. -/
theorem fixedRestorationTraceOrder_eq_integral
    (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (c : Fin n → (Fin k → Face p) → Ξ → ℝ)
    (v : Fin n → Ξ → Vector p) {b R : ℝ}
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    (hc : ∀ i α, Measurable (c i α)) (hv : ∀ i, Measurable (v i))
    (hb : ∀ i α a, |c i α a| ≤ b) (hb0 : 0 ≤ b)
    (hR : 0 ≤ R) (hvb : ∀ i a, ‖v i a‖ ≤ R) (ℓ : ℕ) :
    fixedRestorationTraceOrder s μ A x Z c v ℓ =
      ∑ i, ∫ ag : Ξ × Vector r, ∑ α : Fin k → Face p,
        (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          restorationSeriesTerm s α (A.mulVec ag.2 + x) (v i ag.1) ℓ
            ∂μ.prod (standardGaussian r) := by
  let d : (Fin k → Face p) → (Fin ℓ → Face p) → Fin n → Ξ → ℝ :=
    fun α β i a => c i α a * restorationTranslationCoefficient s α β (v i a)
  let w : (Fin k → Face p) → (Fin ℓ → Face p) → Vector r → ℝ :=
    fun α β g => selectorTupleWeight s (Fin.append α β) (A.mulVec g + x)
  let B := b * Real.exp ((k : ℝ) * R / s.bandwidth) *
    (Real.exp (R / s.bandwidth) - 1) ^ ℓ
  have hdm (α : Fin k → Face p) (β : Fin ℓ → Face p) (i : Fin n) :
      Measurable (d α β i) :=
    (hc i α).mul (measurable_restorationTranslationCoefficient_comp s α β (v i) (hv i))
  have hdb (α : Fin k → Face p) (β : Fin ℓ → Face p) (i : Fin n) (a : Ξ) :
      |d α β i a| ≤ B := by
    dsimp only [d]
    rw [abs_mul]
    calc
      _ ≤ b * (Real.exp ((k : ℝ) * R / s.bandwidth) *
          (Real.exp (R / s.bandwidth) - 1) ^ ℓ) :=
        mul_le_mul (hb i α a) (abs_restorationTranslationCoefficient_le s α β hR (hvb i a))
          (abs_nonneg _) hb0
      _ = B := by dsimp only [B]; ring
  have hwm (α : Fin k → Face p) (β : Fin ℓ → Face p) : Measurable (w α β) :=
    measurable_selectorTupleWeight_comp s _ _ (measurable_affine A x)
  have hwb (α : Fin k → Face p) (β : Fin ℓ → Face p) (g : Vector r) :
      |w α β g| ≤ 1 := by
    rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]
    exact selectorTupleWeight_le_one s _ _
  have hi (i : Fin n) (α : Fin k → Face p) (β : Fin ℓ → Face p) :
      Integrable (fun ag : Ξ × Vector r => d α β i ag.1 *
        (repeatedDirectionScore ag.2 (Z i ag.1) * w α β ag.2))
        (μ.prod (standardGaussian r)) :=
    integrable_restorationScore_product μ Z (d α β) hZ
      (fun i => (hdm α β i).aestronglyMeasurable) (hdb α β) _ (hwm α β) (hwb α β) i
  have hp (i : Fin n) (ag : Ξ × Vector r) :
      (∑ α : Fin k → Face p, (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          restorationSeriesTerm s α (A.mulVec ag.2 + x) (v i ag.1) ℓ) =
        ((-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ)) *
          ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
            d α β i ag.1 * (repeatedDirectionScore ag.2 (Z i ag.1) * w α β ag.2) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α _
    unfold restorationSeriesTerm
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    dsimp only [d, w]
    rw [selectorTupleWeight_append]
    ring
  symm
  simp_rw [hp, integral_const_mul]
  rw [← Finset.mul_sum]
  congr 1
  calc
    _ = ∑ i, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
        ∫ ag : Ξ × Vector r, d α β i ag.1 *
          (repeatedDirectionScore ag.2 (Z i ag.1) * w α β ag.2)
            ∂μ.prod (standardGaussian r) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [integral_finset_sum Finset.univ (fun α _ =>
        integrable_finset_sum Finset.univ (fun β _ => hi i α β))]
      apply Finset.sum_congr rfl
      intro α _
      exact integral_finset_sum Finset.univ (fun β _ => hi i α β)
    _ = _ := by
      rw [sum_three_rotate]
      apply Finset.sum_congr rfl
      intro α _
      apply Finset.sum_congr rfl
      intro β _
      exact sum_integral_restorationScore_product_eq_trace μ Z (d α β) hZ
        (fun i => (hdm α β i).aestronglyMeasurable) (hdb α β) (w α β) (hwm α β) (hwb α β)

/-- The exact convergent trace expansion for the actual translated
fresh-array experiment, with all series/integral interchanges proved. -/
theorem hasSum_fixedRestorationTraceOrder
    (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Ξ → Vector r) (c : Fin n → (Fin k → Face p) → Ξ → ℝ)
    (v : Fin n → Ξ → Vector p) {b R : ℝ}
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun a => Z i a j * Z i a l) μ)
    (hc : ∀ i α, Measurable (c i α)) (hv : ∀ i, Measurable (v i))
    (hb : ∀ i α a, |c i α a| ≤ b) (hb0 : 0 ≤ b)
    (hR : 0 ≤ R) (hvb : ∀ i a, ‖v i a‖ ≤ R)
    (hsmall : R / s.bandwidth < Real.log 2) :
    HasSum (fixedRestorationTraceOrder s μ A x Z c v)
      (fixedRestorationTranslatedExpectation s μ A x Z c v) := by
  have hs (i : Fin n) : HasSum (fun ℓ => ∫ ag : Ξ × Vector r,
      ∑ α : Fin k → Face p,
        (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          restorationSeriesTerm s α (A.mulVec ag.2 + x) (v i ag.1) ℓ
            ∂μ.prod (standardGaussian r))
      (∫ ag : Ξ × Vector r, ∑ α : Fin k → Face p,
        (c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1)) *
          selectorTupleWeight s α (A.mulVec ag.2 + x + v i ag.1)
            ∂μ.prod (standardGaussian r)) := by
    have hscore := measurable_repeatedDirectionScore_product (Z i) (hZm i)
    have hscorei : Integrable
        (fun ag : Ξ × Vector r => repeatedDirectionScore ag.2 (Z i ag.1))
        (μ.prod (standardGaussian r)) := by
      simpa only [one_mul, mul_one] using
        integrable_restorationScore_product μ Z (fun _ _ => 1) (b := 1) hZ
          (fun _ => measurable_const.aestronglyMeasurable) (by intro _ _; norm_num)
          (fun _ => 1) measurable_const (by intro _; norm_num) i
    apply hasSum_integral_restorationSeries s (μ.prod (standardGaussian r))
      (fun α ag => c i α ag.1 * repeatedDirectionScore ag.2 (Z i ag.1))
      (fun ag => A.mulVec ag.2 + x) (fun ag => v i ag.1)
      (fun ag => b * |repeatedDirectionScore ag.2 (Z i ag.1)|)
    · intro α; exact ((hc i α).comp measurable_fst).mul hscore
    · exact (measurable_affine A x).comp measurable_snd
    · exact (hv i).comp measurable_fst
    · exact hscorei.abs.const_mul b
    · intro ag; exact mul_nonneg hb0 (abs_nonneg _)
    · intro α ag
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right (hb i α ag.1) (abs_nonneg _)
    · exact hR
    · intro ag; exact hvb i ag.1
    · exact hsmall
  have ht := hasSum_sum (s := Finset.univ) (fun i _ => hs i)
  convert ht using 1
  funext ℓ
  exact fixedRestorationTraceOrder_eq_integral s μ A x Z c v hZ hc hv hb hb0 hR hvb ℓ

end
end RectangleCLT.Companion
