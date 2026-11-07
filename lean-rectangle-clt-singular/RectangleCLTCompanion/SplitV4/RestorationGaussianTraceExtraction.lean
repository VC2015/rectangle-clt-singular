import RectangleCLTCompanion.SplitV4.RestorationConditionalInterchange

/-! Exact coefficient extraction for one deterministic Gaussian order.
The redundant unit variable lets us reuse the historical proved product
identity while discharging all its genuine moment hypotheses concretely.
-/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem gaussian_restoration_order_eq_integral
    {p r n k : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p)
    (Z : Fin n → Vector r) (c : Fin n → (Fin k → Face p) → ℝ) (v : Fin n → Vector p)
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, |c i α| ≤ b) (hvb : ∀ i, ‖v i‖ ≤ R)
    (hsmall : R / s.bandwidth < Real.log 2) (ℓ : ℕ) :
    (-1 : ℝ) ^ ℓ * ((k + ℓ).choose ℓ : ℝ) *
      (∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
        Matrix.trace (restorationRankOneSum (fun i (_ : Unit) => Z i)
          (fun i (_ : Unit) => c i α * restorationTranslationCoefficient s α β (v i)) () *
            weightedScore (standardGaussian r) id
              (fun g => selectorTupleWeight s (Fin.append α β) (A.mulVec g + x)))) =
      ∫ g : Vector r, ∑ i, ∑ α : Fin k → Face p,
        (c i α * repeatedDirectionScore g (Z i)) * restorationSeriesTerm s α (A.mulVec g + x) (v i) ℓ
          ∂standardGaussian r := by
  let ν : Measure Unit := Measure.dirac ()
  haveI : IsProbabilityMeasure ν := by dsimp [ν]; infer_instance
  have hZunit (i : Fin n) (j l : Fin r) : Integrable (fun _ : Unit => Z i j * Z i l) ν :=
    integrable_const _
  have hs (i : Fin n) := translated_score_series_interchange s ν A (fun _ => x) measurable_const
    (fun _ => Z i) measurable_const (hZunit i) (fun α _ => c i α)
    (fun _ => measurable_const) (fun _ => v i) measurable_const hb hR
    (fun α => ae_of_all _ (fun _ => hcb i α)) (ae_of_all _ (fun _ => hvb i)) hsmall
  have hi (i : Fin n) : Integrable (fun g : Vector r => ∑ α : Fin k → Face p,
      (c i α * repeatedDirectionScore g (Z i)) * restorationSeriesTerm s α (A.mulVec g + x) (v i) ℓ)
      (standardGaussian r) := by
    have ha := ((hs i).2.1 ℓ).prod_right_ae
    obtain ⟨_, h⟩ := ha.exists
    exact h
  have hprod (i : Fin n) : (∫ z : Unit × Vector r, ∑ α : Fin k → Face p,
      (c i α * repeatedDirectionScore z.2 (Z i)) * restorationSeriesTerm s α (A.mulVec z.2 + x) (v i) ℓ
        ∂ν.prod (standardGaussian r)) =
      ∫ g : Vector r, ∑ α : Fin k → Face p,
        (c i α * repeatedDirectionScore g (Z i)) * restorationSeriesTerm s α (A.mulVec g + x) (v i) ℓ
          ∂standardGaussian r := by
    rw [integral_prod _ ((hs i).2.1 ℓ)]
    change (∫ _u : Unit, (∫ g : Vector r, ∑ α : Fin k → Face p,
      (c i α * repeatedDirectionScore g (Z i)) * restorationSeriesTerm s α (A.mulVec g + x) (v i) ℓ
        ∂standardGaussian r) ∂ν) = _
    rw [integral_const]
    simp only [measureReal_univ_eq_one, one_smul]
  have he := fixedRestorationTraceOrder_eq_integral s ν A x (fun i _ => Z i)
    (fun i α _ => c i α) (fun i _ => v i) hZunit (fun _ _ => measurable_const)
    (fun _ => measurable_const) (fun i α _ => hcb i α) hb hR (fun i _ => hvb i) ℓ
  have hcoef (α : Fin k → Face p) (β : Fin ℓ → Face p) :
      restorationCoefficient ν (fun i (_ : Unit) => Z i)
        (fun i _ => c i α * restorationTranslationCoefficient s α β (v i)) =
      restorationRankOneSum (fun i (_ : Unit) => Z i)
        (fun i _ => c i α * restorationTranslationCoefficient s α β (v i)) () := by
    ext j l
    simp only [restorationCoefficient, restorationRankOneSum, integral_const,
      measureReal_univ_eq_one, one_smul]
  simp only [fixedRestorationTraceOrder] at he
  simp_rw [hcoef] at he
  rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
  exact he.trans (Finset.sum_congr rfl (fun i _ => hprod i))

theorem translated_score_series_term_eq_orderIntegral
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ) (hc : ∀ i α, Measurable (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R / s.bandwidth < Real.log 2) (ℓ : ℕ) :
    (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        restorationSeriesTerm s α (A.mulVec z.2 + V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r)) =
      conditionalRestorationTraceOrderIntegral s μ A V Z c v ℓ := by
  have hi := (translated_score_array_series_interchange s μ A V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall).2.1 ℓ
  rw [integral_prod _ hi, conditionalRestorationTraceOrderIntegral, ← integral_const_mul]
  apply integral_congr_ae
  have hallc : ∀ᵐ ω ∂μ, ∀ i α, |c i α ω| ≤ b :=
    ae_all_iff.mpr (fun i => ae_all_iff.mpr (hcb i))
  filter_upwards [hallc, ae_all_iff.mpr hvb] with ω hcω hvω
  have he := gaussian_restoration_order_eq_integral s A (V ω) (fun i => Z i ω)
    (fun i α => c i α ω) (fun i => v i ω) hb hR hcω hvω hsmall ℓ
  simpa only [selectorGaussianScore] using he.symm

/-- The actual translated score expectation equals the absolutely
summable sequence of its actual common-base matrix coefficient orders. -/
theorem translated_score_hasSum_expected_orders
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
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
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1))
          (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) ∧
    HasSum (conditionalRestorationTraceOrderIntegral s μ A V Z c v)
      (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
        (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
          selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1) ∂μ.prod (standardGaussian r)) := by
  have hs := translated_score_array_series_interchange s μ A V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall
  refine ⟨hs.1, ?_⟩
  have he (ℓ : ℕ) := translated_score_series_term_eq_orderIntegral s μ A V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall ℓ
  simpa only [he] using hs.2.2

/-- Complete translated-selector restoration from genuine conditional
second moments and the actual B.4 averaged matrix estimate. This is the
weight-restoration stage before the two Stein identities and derivative
partition coefficients are inserted. -/
theorem conditional_translated_score_restoration
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V) {C T : ℝ}
    (hmatrix : @AveragedSelectorMatrixEstimate p r Ω mΩ s μ A V C T)
    (Z : Fin n → Ω → Vector r)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j * Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ)
    (hc : ∀ i α, @Measurable Ω ℝ mΩ inferInstance (c i α))
    (v : Fin n → Ω → Vector p)
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (hk : 1 ≤ k) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ᵐ ω ∂μ, ∀ u,
      matrixQuadratic (conditionalRestorationCoefficient (mΩ := mΩ) μ H Z (fun _ _ => 1) ω) u ≤ vectorNormSq u)
    (hC : 1 ≤ C) (hT : 0 ≤ T) (hsmall : C * (Real.exp (R / s.bandwidth) - 1) < 1) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1))
          (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) ∧
    |∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1 * repeatedDirectionScore z.2 (Z i z.1)) *
        selectorTupleWeight s α (A.mulVec z.2 + V z.1 + v i z.1)
          ∂(@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r))| ≤
      (b * Real.exp ((k : ℝ) * R / s.bandwidth) * C ^ (k + 1) * T) /
        (1 - C * (Real.exp (R / s.bandwidth) - 1)) ^ (k + 1) := by
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη₁ : Real.exp (R / s.bandwidth) - 1 < 1 :=
    (le_mul_of_one_le_left hη hC).trans_lt hsmall
  have hradius : R / s.bandwidth < Real.log 2 := by
    apply Real.exp_lt_exp.mp
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
    linarith
  have hVm : @Measurable Ω (Vector p) mΩ inferInstance V := hV.mono hH le_rfl
  have he := translated_score_hasSum_expected_orders (mΩ := mΩ) s μ A V hVm Z hZm hZ c hc v hv hb hR hcb hvb hradius
  have hbnd := conditional_restoration_expected_series_bound (mΩ := mΩ) s μ H hH A V hV hmatrix Z c v hk hZ
    (fun i α => (hc i α).aestronglyMeasurable) (fun i => (hv i).aestronglyMeasurable)
    hb hR hcb hvb hbudget hC hT hsmall
  refine ⟨he.1, ?_⟩
  rw [← he.2.tsum_eq]
  exact hbnd.2

end

end RectangleCLT.Companion.SplitV4
