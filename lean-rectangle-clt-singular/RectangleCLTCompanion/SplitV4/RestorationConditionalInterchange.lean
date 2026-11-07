import RectangleCLTCompanion.SplitV4.RestorationConditionalSeries
import RectangleCLTCompanion.RestorationTraceSeries

/-! Genuine translated-selector series interchanges for B.2. The coarse
Gaussian-score majorant is used only for integrability; operator budgets
are applied to expected coefficients in the separate sharp estimate. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem hasSum_integral_restorationSeries_ae
    {X : Type*} [MeasurableSpace X] {p k : ℕ}
    (s : FaceSmoother p) (ρ : Measure X)
    (c : (Fin k → Face p) → X → ℝ) (U V : X → Vector p) (D : X → ℝ)
    (hc : ∀ α, Measurable (c α)) (hU : Measurable U) (hV : Measurable V)
    (hDi : Integrable D ρ) (hD : ∀ x, 0 ≤ D x)
    (hcb : ∀ α, ∀ᵐ x ∂ρ, |c α x| ≤ D x) {R : ℝ}
    (hR : 0 ≤ R) (hv : ∀ᵐ x ∂ρ, ‖V x‖ ≤ R) (hsmall : R / s.bandwidth < Real.log 2) :
    HasSum (fun ℓ : ℕ => ∫ x, ∑ α : Fin k → Face p,
      c α x * restorationSeriesTerm s α (U x) (V x) ℓ ∂ρ)
      (∫ x, ∑ α : Fin k → Face p,
        c α x * selectorTupleWeight s α (U x + V x) ∂ρ) := by
  let η := Real.exp (R / s.bandwidth) - 1
  let E := Real.exp ((k : ℝ) * R / s.bandwidth)
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη₁ : η < 1 := by
    have he := Real.exp_lt_exp.mpr hsmall
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    dsimp only [η]
    linarith
  have hs := hasSum_restoration_matrix_majorant k (C := 1) (η := η)
    (by norm_num) hη (by simpa only [one_mul] using hη₁)
  simp only [one_mul] at hs
  apply hasSum_integral_of_dominated_convergence
    (fun ℓ x => (((k + ℓ).choose ℓ : ℝ) * η ^ ℓ) * (E * D x))
  · intro ℓ
    exact (Finset.measurable_sum _ (fun α _ => (hc α).mul
      (measurable_restorationSeriesTerm_comp s α U V hU hV ℓ))).aestronglyMeasurable
  · intro ℓ
    filter_upwards [ae_all_iff.mpr hcb, hv] with x hcx hvx
    exact abs_sum_mul_restorationSeriesTerm_le s (fun α => c α x) (U x) hR hvx (hD x) hcx ℓ
  · exact ae_of_all _ (fun x => hs.summable.mul_right (E * D x))
  · have heq (x : X) : (∑' ℓ : ℕ, (((k + ℓ).choose ℓ : ℝ) * η ^ ℓ) * (E * D x)) =
        (1 / (1 - η) ^ (k + 1)) * (E * D x) := (hs.mul_right (E * D x)).tsum_eq
    simp_rw [heq]
    exact (hDi.const_mul E).const_mul _
  · filter_upwards [hv] with x hvx
    exact hasSum_sum (fun α _ => (hasSum_restorationSeriesTerm s α (U x) hR hvx hsmall).mul_left (c α x))

/-- The original translated finite selector sum is genuinely integrable
under the same actual moment majorant used for the interchange. -/
theorem integrable_translated_selector_sum_of_domination
    {X : Type*} [MeasurableSpace X] {p k : ℕ}
    (s : FaceSmoother p) (ρ : Measure X)
    (c : (Fin k → Face p) → X → ℝ) (U V : X → Vector p) (D : X → ℝ)
    (hc : ∀ α, Measurable (c α)) (hU : Measurable U) (hV : Measurable V)
    (hDi : Integrable D ρ) (hD : ∀ x, 0 ≤ D x)
    (hcb : ∀ α, ∀ᵐ x ∂ρ, |c α x| ≤ D x) :
    Integrable (fun x => ∑ α : Fin k → Face p,
      c α x * selectorTupleWeight s α (U x + V x)) ρ := by
  have hm : Measurable (fun x => ∑ α : Fin k → Face p,
      c α x * selectorTupleWeight s α (U x + V x)) :=
    Finset.measurable_sum _ (fun α _ => (hc α).mul (measurable_selectorTupleWeight_comp s α _ (hU.add hV)))
  apply hDi.mono' hm.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr hcb] with x hcx
  rw [Real.norm_eq_abs]
  calc
    _ ≤ ∑ α, |c α x| * |selectorTupleWeight s α (U x + V x)| := by
      simpa only [abs_mul] using Finset.abs_sum_le_sum_abs
        (fun α => c α x * selectorTupleWeight s α (U x + V x)) Finset.univ
    _ ≤ ∑ α, D x * selectorTupleWeight s α (U x + V x) := Finset.sum_le_sum (fun α _ => by
      rw [abs_of_nonneg (selectorTupleWeight_nonneg s α _)]
      exact mul_le_mul_of_nonneg_right (hcx α) (selectorTupleWeight_nonneg s α _))
    _ = D x * ∑ α, selectorTupleWeight s α (U x + V x) := (Finset.mul_sum _ _ _).symm
    _ ≤ D x * 1 := mul_le_mul_of_nonneg_left (sum_selectorTupleWeight_le_one s k _) (hD x)
    _ = D x := mul_one _

theorem integrable_restorationSeries_sum_of_domination
    {X : Type*} [MeasurableSpace X] {p k : ℕ}
    (s : FaceSmoother p) (ρ : Measure X)
    (c : (Fin k → Face p) → X → ℝ) (U V : X → Vector p) (D : X → ℝ)
    (hc : ∀ α, Measurable (c α)) (hU : Measurable U) (hV : Measurable V)
    (hDi : Integrable D ρ) (hD : ∀ x, 0 ≤ D x)
    (hcb : ∀ α, ∀ᵐ x ∂ρ, |c α x| ≤ D x) {R : ℝ}
    (hR : 0 ≤ R) (hv : ∀ᵐ x ∂ρ, ‖V x‖ ≤ R) (ℓ : ℕ) :
    Integrable (fun x => ∑ α : Fin k → Face p,
      c α x * restorationSeriesTerm s α (U x) (V x) ℓ) ρ := by
  have hm : Measurable (fun x => ∑ α : Fin k → Face p,
      c α x * restorationSeriesTerm s α (U x) (V x) ℓ) :=
    Finset.measurable_sum _ (fun α _ => (hc α).mul (measurable_restorationSeriesTerm_comp s α U V hU hV ℓ))
  apply ((hDi.const_mul (Real.exp ((k : ℝ) * R / s.bandwidth))).const_mul
    (((k + ℓ).choose ℓ : ℝ) * (Real.exp (R / s.bandwidth) - 1) ^ ℓ)).mono' hm.aestronglyMeasurable
  filter_upwards [ae_all_iff.mpr hcb, hv] with x hcx hvx
  exact abs_sum_mul_restorationSeriesTerm_le s (fun α => c α x) (U x) hR hvx (hD x) hcx ℓ

/-- The coarse Gaussian-score majorant is genuinely integrable under only
the second moments of the repeated direction. It is used for Fubini, not
as the final numerical restoration bound. -/
theorem integrable_random_repeatedDirectionScore
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ) :
    Integrable (fun z : Ω × Vector r => repeatedDirectionScore z.2 (Z z.1))
      (μ.prod (standardGaussian r)) := by
  simpa only [one_mul, mul_one] using
    integrable_restorationScore_product (b := 1) μ (fun _ : Fin 1 => Z) (fun _ _ => (1 : ℝ))
      (fun _ j k => hZ j k) (fun _ => measurable_const.aestronglyMeasurable)
      (by intro _ _; norm_num) (fun _ => (1 : ℝ)) measurable_const (by intro _; norm_num) (0 : Fin 1)

/-- One actual random translated score expectation is its common-base
selector series. All inputs and every series term are genuinely integrable;
the shift and coefficient envelopes hold only almost surely. -/
theorem translated_score_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j l, Integrable (fun ω => Z ω j * Z ω l) μ)
    (c : (Fin k → Face p) → Ω → ℝ) (hc : ∀ α, Measurable (c α))
    (v : Ω → Vector p) (hv : Measurable v) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ α, ∀ᵐ ω ∂μ, |c α ω| ≤ b) (hvb : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ R)
    (hsmall : R / s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ α : Fin k → Face p,
      (c α z.1 * repeatedDirectionScore z.2 (Z z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ α : Fin k → Face p,
      (c α z.1 * repeatedDirectionScore z.2 (Z z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v z.1) ℓ) (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
      (c α z.1 * repeatedDirectionScore z.2 (Z z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
        (c α z.1 * repeatedDirectionScore z.2 (Z z.1)) *
          selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v z.1) ∂μ.prod (standardGaussian r)) := by
  let ρ := μ.prod (standardGaussian r)
  let U : Ω × Vector r → Vector p := fun z => A.mulVec z.2 + V z.1
  let v' : Ω × Vector r → Vector p := fun z => v z.1
  let c' : (Fin k → Face p) → Ω × Vector r → ℝ :=
    fun α z => c α z.1 * repeatedDirectionScore z.2 (Z z.1)
  let D : Ω × Vector r → ℝ := fun z => b * |repeatedDirectionScore z.2 (Z z.1)|
  have hscore := measurable_repeatedDirectionScore_product Z hZm
  have hc' (α : Fin k → Face p) : Measurable (c' α) := ((hc α).comp measurable_fst).mul hscore
  have hU : Measurable U :=
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add (hV.comp measurable_fst)
  have hv' : Measurable v' := hv.comp measurable_fst
  have hDi : Integrable D ρ := (integrable_random_repeatedDirectionScore μ Z hZ).abs.const_mul b
  have hD : ∀ z, 0 ≤ D z := fun _ => mul_nonneg hb (abs_nonneg _)
  have hDmeas : Measurable D := hscore.abs.const_mul b
  have hcb' (α : Fin k → Face p) : ∀ᵐ z ∂ρ, |c' α z| ≤ D z := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (hc' α).abs hDmeas)).mpr
    filter_upwards [hcb α] with ω hω
    exact ae_of_all _ (fun g => by
      change |c α ω * repeatedDirectionScore g (Z ω)| ≤ b * |repeatedDirectionScore g (Z ω)|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
  have hvb' : ∀ᵐ z ∂ρ, ‖v' z‖ ≤ R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hv'.norm measurable_const)).mpr
    exact hvb.mono (fun _ hω => ae_of_all _ (fun _ => hω))
  exact ⟨integrable_translated_selector_sum_of_domination s ρ c' U v' D hc' hU hv' hDi hD hcb',
    fun ℓ => integrable_restorationSeries_sum_of_domination s ρ c' U v' D hc' hU hv' hDi hD hcb' hR hvb' ℓ,
    hasSum_integral_restorationSeries_ae s ρ c' U v' D hc' hU hv' hDi hD hcb' hR hvb' hsmall⟩

/-- The full auxiliary array may be dependent. The finite summand sum is
interchanged only after every Gaussian-score term has a genuine moment. -/
theorem translated_score_array_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ) (hc : ∀ i α, Measurable (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R / s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v i z.1) ℓ) (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
        (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
          selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1) ∂μ.prod (standardGaussian r)) := by
  have hi (i : Fin n) := translated_score_series_interchange s μ A V hV (Z i) (hZm i) (hZ i)
    (c i) (hc i) (v i) (hv i) hb hR (hcb i) (hvb i) hsmall
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),
    fun ℓ => integrable_finset_sum _ (fun i _ => (hi i).2.1 ℓ), ?_⟩
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => (hi i).2.2)
  have he (ℓ : ℕ) : (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r)) =
      ∑ i, ∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
        (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
          restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r) :=
    integral_finset_sum _ (fun i _ => (hi i).2.1 ℓ)
  rw [integral_finset_sum Finset.univ (fun i _ => (hi i).1)]
  simp_rw [he]
  exact hs

end

end RectangleCLT.Companion.SplitV4
