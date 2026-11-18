import RectangleCLTArxivV1.HFourthCubicTrace

/-! Genuine Gaussian/product and infinite-series interchanges for H3 with
the first selector label retained as its Hermite direction. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem hFourth_cubic_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) μ)
    (c : Face p → Ω → ℝ) (hc : ∀ f, Measurable (c f))
    (v : Ω → Vector p) (hv : Measurable v) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ f, ∀ᵐ ω ∂μ, |c f ω| ≤ b) (hvb : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ f : Face p,
      (c f z.1*capThirdHermiteScore (U f) (Z z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ f : Face p,
      (c f z.1*capThirdHermiteScore (U f) (Z z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v z.1) ℓ)
          (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ f : Face p,
      (c f z.1*capThirdHermiteScore (U f) (Z z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ f : Face p,
        (c f z.1*capThirdHermiteScore (U f) (Z z.1) z.2)*
          selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v z.1) ∂μ.prod (standardGaussian r)) := by
  classical
  let ρ := μ.prod (standardGaussian r)
  let P := fun z : Ω × Vector r => A.mulVec z.2+V z.1
  let v' := fun z : Ω × Vector r => v z.1
  let c' := fun (α : Fin 1 → Face p) (z : Ω × Vector r) =>
    c (α 0) z.1*capThirdHermiteScore (U (α 0)) (Z z.1) z.2
  let D := fun z : Ω × Vector r => b*∑ f : Face p, |capThirdHermiteScore (U f) (Z z.1) z.2|
  have hs (f : Face p) := measurable_capThirdHermiteScore_product (U f) Z hZm
  have hc' (α : Fin 1 → Face p) : Measurable (c' α) :=
    ((hc (α 0)).comp measurable_fst).mul (hs (α 0))
  have hP : Measurable P :=
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)
  have hv' : Measurable v' := hv.comp measurable_fst
  have hDi : Integrable D ρ :=
    (integrable_finset_sum _ (fun f _ => (integrable_random_capThirdHermiteScore μ (U f) Z hZ).abs)).const_mul b
  have hD : ∀ z, 0 ≤ D z := fun z => mul_nonneg hb
    (Finset.sum_nonneg (fun f _ => abs_nonneg _))
  have hDm : Measurable D := (Finset.measurable_sum _ (fun f _ => (hs f).abs)).const_mul b
  have hcb' (α : Fin 1 → Face p) : ∀ᵐ z ∂ρ, |c' α z| ≤ D z := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (hc' α).abs hDm)).mpr
    filter_upwards [hcb (α 0)] with ω hcω
    exact ae_of_all _ (fun g => by
      change |c (α 0) ω*capThirdHermiteScore (U (α 0)) (Z ω) g| ≤
        b*∑ f, |capThirdHermiteScore (U f) (Z ω) g|
      rw [abs_mul]
      exact (mul_le_mul_of_nonneg_right hcω (abs_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (Finset.single_le_sum
          (fun f _ => abs_nonneg (capThirdHermiteScore (U f) (Z ω) g)) (Finset.mem_univ (α 0))) hb))
  have hvb' : ∀ᵐ z ∂ρ, ‖v' z‖ ≤ R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hv'.norm measurable_const)).mpr
    exact hvb.mono (fun _ hω => ae_of_all _ (fun _ => hω))
  have hi := integrable_translated_selector_sum_of_domination s ρ c' P v' D hc' hP hv' hDi hD hcb'
  have ho (ℓ : ℕ) := integrable_restorationSeries_sum_of_domination s ρ c' P v' D
    hc' hP hv' hDi hD hcb' hR hvb' ℓ
  have hh := hasSum_integral_restorationSeries_ae s ρ c' P v' D hc' hP hv' hDi hD hcb' hR hvb' hsmall
  simp_rw [hFourth_sum_singleton_tuples] at hi ho hh
  simpa only [c',P,v',ρ,Matrix.cons_val_zero] using And.intro hi (And.intro ho hh)

theorem hFourth_cubic_array_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → Face p → Ω → ℝ) (hc : ∀ i f, Measurable (c i f))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v i z.1) ℓ)
          (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
        (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
          selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)) := by
  have hi (i : Fin n) := hFourth_cubic_series_interchange s μ A U V hV (Z i) (hZm i)
    (hZ i) (c i) (hc i) (v i) (hv i) hb hR (hcb i) (hvb i) hsmall
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),
    fun ℓ => integrable_finset_sum _ (fun i _ => (hi i).2.1 ℓ), ?_⟩
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => (hi i).2.2)
  have he (ℓ : ℕ) : (∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r))=
      ∑ i, ∫ z : Ω × Vector r, ∑ f : Face p,
        (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
          restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r) :=
    integral_finset_sum _ (fun i _ => (hi i).2.1 ℓ)
  rw [integral_finset_sum _ (fun i _ => (hi i).1)]
  simpa only [he] using hs

/-- Each actual product-Gaussian series term equals the common-base
signed matrix order. All products have genuine moments before Fubini. -/
theorem hFourth_cubic_series_term_eq_order
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → Face p → Ω → ℝ) (hc : ∀ i f, Measurable (c i f))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) (ℓ : ℕ) :
    (∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        restorationSeriesTerm s ![f] (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r))=
      (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)*hFourthCubicRestorationOrder s μ A U V Z c v ℓ := by
  have hi := (hFourth_cubic_array_series_interchange s μ A U V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall).2.1 ℓ
  rw [integral_prod _ hi,hFourthCubicRestorationOrder,← integral_const_mul]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    have he := hFourth_fixed_cubic_restoration_order s A U (V ω) (fun i => Z i ω)
      (fun i f => c i f ω) (fun i => v i ω) ℓ
    simpa only [restorationRankOneSum] using he)

/-- The actual translated H3 contraction has precisely the signed
common-base matrix orders whose nuclear estimates are supplied in H. -/
theorem hFourth_cubic_hasSum_expected_orders
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (U : Face p → Vector r)
    (V : Ω → Vector p) (hV : Measurable V) (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (c : Fin n → Face p → Ω → ℝ) (hc : ∀ i f, Measurable (c i f))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i f, ∀ᵐ ω ∂μ, |c i f ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ f : Face p,
      (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
        selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1)) (μ.prod (standardGaussian r)) ∧
    HasSum (fun ℓ => (-1:ℝ)^ℓ*((1+ℓ).choose ℓ:ℝ)*hFourthCubicRestorationOrder s μ A U V Z c v ℓ)
      (∫ z : Ω × Vector r, ∑ i, ∑ f : Face p,
        (c i f z.1*capThirdHermiteScore (U f) (Z i z.1) z.2)*
          selectorTupleWeight s ![f] (A.mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)) := by
  have hh := hFourth_cubic_array_series_interchange s μ A U V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall
  refine ⟨hh.1, ?_⟩
  simpa only [hFourth_cubic_series_term_eq_order s μ A U V hV Z hZm hZ c hc v hv hb hR hcb hvb hsmall] using hh.2.2

end
end RectangleCLTArxivV1
