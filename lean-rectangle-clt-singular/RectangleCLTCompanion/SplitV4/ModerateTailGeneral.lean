import RectangleCLTCompanion.SplitV4.ModerateTail

/-! Lemma F.1 for arbitrary independent centered bounded scalar variables. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
universe u
namespace RectangleCLT.Companion.SplitV4
noncomputable section

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n → Ω → ℝ} {δ : ℝ}

theorem moderateIndependent_sum_identDistrib (hη : ∀ i, Measurable (η i)) (hind : iIndepFun η μ) :
    IdentDistrib (moderateScalarSum η) (fun z : Fin n → ℝ => ∑ i, z i)
      μ (Measure.pi (fun i => μ.map (η i))) := by
  have hmap := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hη i).aemeasurable)).mp hind
  have hident : IdentDistrib (fun ω i => η i ω) id μ (Measure.pi (fun i => μ.map (η i))) :=
    ⟨(measurable_pi_lambda _ hη).aemeasurable, measurable_id.aemeasurable, by rw [Measure.map_id]; exact hmap⟩
  exact hident.comp (Finset.measurable_sum _ (fun i _ => measurable_pi_apply i))

theorem moderateScalarTail_bound (hn : 1 ≤ n) (hη : ∀ i, Measurable (η i))
    (hind : iIndepFun η μ) (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1)
    {x : ℝ} (hx : 0 ≤ x) (hsmall : moderateTailSmallConstant * (δ * (1 + x)) ≤ 1) :
    0 < μ.real {ω | x < moderateScalarSum η ω} ∧
    |Real.log (μ.real {ω | x < moderateScalarSum η ω} / standardNormalUpperTail x) -
      moderateArrayGamma μ η * x ^ 3 / 6| ≤
        moderateTailRemainderConstant * (δ * (1 + x) + δ ^ 2 * x ^ 4) := by
  have hH := moderateTailSmallConstant_bounds
  have hC := moderateTailRemainderConstant_bounds
  have hdx : 0 ≤ δ * (1 + x) := by positivity
  by_cases hx2 : x ≤ 2
  · have hsmall' : scalarBerryEsseenConstant * δ / standardNormalUpperTail 2 ≤ 1 / 2 := by
      have hh := mul_le_mul_of_nonneg_right hH.2.2.2 hδ
      have hδ' : δ ≤ δ * (1 + x) := by nlinarith
      have hm := mul_le_mul_of_nonneg_left hδ' hH.1.le
      have hh' : 2 * (scalarBerryEsseenConstant * δ / standardNormalUpperTail 2) ≤ 1 := by
        convert hh.trans (hm.trans hsmall) using 1 <;> ring
      linarith only [hh']
    have hh := moderateScalarTail_small_threshold hn hη hind hδ hbound hc hv hx hx2 hsmall'
    refine ⟨hh.1, hh.2.trans ?_⟩
    have hd : δ ≤ δ * (1 + x) + δ ^ 2 * x ^ 4 := by
      have hh : 0 ≤ δ * x + δ ^ 2 * x ^ 4 := by positivity
      nlinarith only [hh]
    exact mul_le_mul hC.2.1 hd hδ hC.1.le
  · let ν : Fin n → Measure ℝ := fun i => μ.map (η i)
    letI (i : Fin n) : IsProbabilityMeasure (ν i) := isProbabilityMeasure_map (hη i).aemeasurable
    have hb (i : Fin n) : ∀ᵐ z ∂ν i, |z| ≤ δ := by
      exact (ae_map_iff (hη i).aemeasurable (measurableSet_le measurable_id.abs measurable_const)).mpr (hbound i)
    have hm (i : Fin n) (f : ℝ → ℝ) (hf : Measurable f) : (∫ z, f z ∂ν i) = ∫ ω, f (η i ω) ∂μ :=
      integral_map (hη i).aemeasurable hf.aestronglyMeasurable
    have hc' (i : Fin n) : (∫ z, z ∂ν i) = 0 := (hm i id measurable_id).trans (hc i)
    have hv' : (∑ i, ∫ z, z ^ 2 ∂ν i) = 1 := by
      calc
        _ = ∑ i, ∫ ω, η i ω ^ 2 ∂μ := Finset.sum_congr rfl (fun i _ => hm i (fun z => z ^ 2) (measurable_id.pow_const 2))
        _ = 1 := hv
    have ht := moderateProductTail_large_threshold ν hn hδ hb hc' hv' (le_of_not_ge hx2) hsmall
    have hsum := moderateIndependent_sum_identDistrib hη hind
    have htail : μ.real {ω | x < moderateScalarSum η ω} = (Measure.pi ν).real {z | x < ∑ i, z i} :=
      congrArg ENNReal.toReal (hsum.measure_mem_eq measurableSet_Ioi)
    have hgamma : moderateArrayGamma (Measure.pi ν) (fun i z => z i) = moderateArrayGamma μ η := by
      apply Finset.sum_congr rfl
      intro i _
      exact (moderateProduct_coordinate_integral ν i (fun z => z ^ 3) (measurable_id.pow_const 3)).trans
        (hm i (fun z => z ^ 3) (measurable_id.pow_const 3))
    rw [htail]
    simpa only [hgamma] using ht

/-- Absolute constants are selected before the dimension, sample size,
probability space, or marginal laws. This is the full strict-tail statement
of Lemma F.1, including arbitrary atoms and nonidentical summands. -/
theorem uniformScalarModerateTail : ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
      {n : ℕ} (η : Fin n → Ω → ℝ) (δ : ℝ),
      1 ≤ n → (∀ i, Measurable (η i)) → iIndepFun η μ → 0 < δ →
      (∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) → (∀ i, (∫ ω, η i ω ∂μ) = 0) →
      (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1 →
      ∀ x : ℝ, 0 ≤ x → δ * (1 + x) ≤ a →
        0 < μ.real {ω | x < ∑ i, η i ω} ∧
        |Real.log (μ.real {ω | x < ∑ i, η i ω} / standardNormalUpperTail x) -
          (∑ i, ∫ ω, η i ω ^ 3 ∂μ) * x ^ 3 / 6| ≤ C * (δ * (1 + x) + δ ^ 2 * x ^ 4) := by
  refine ⟨1 / moderateTailSmallConstant, moderateTailRemainderConstant,
    div_pos zero_lt_one moderateTailSmallConstant_bounds.1, moderateTailRemainderConstant_bounds.1, ?_⟩
  intro Ω _ μ _ n η δ hn hη hind hδ hb hc hv x hx hsmall
  have hs : moderateTailSmallConstant * (δ * (1 + x)) ≤ 1 := by
    have hh := (le_div_iff₀ moderateTailSmallConstant_bounds.1).mp hsmall
    nlinarith only [hh]
  exact moderateScalarTail_bound hn hη hind hδ.le hb hc hv hx hs


/-- The genuine aggregate tilted mean is strictly increasing, so the
inverse root used above is unique even before restricting its interval. -/
theorem moderateArrayMean_strictMono (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) : StrictMono (moderateArrayMean μ η) := by
  apply strictMono_of_deriv_pos
  intro t
  rw [(hasDerivAt_moderateArrayMean hη hbound t).deriv]
  exact (Real.exp_pos (-2 * |t| * δ)).trans_le (moderateArrayVariance_exp_bounds hη hδ hbound hc hv t).1

theorem existsUnique_moderateArrayMean_eq (hη : ∀ i, Measurable (η i)) (hδ : 0 ≤ δ)
    (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ) (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0)
    (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : 100 * moderateTaylorConstant * (δ * x) ≤ 1) :
    ∃! t, t ∈ Icc (0 : ℝ) (2 * x) ∧ moderateArrayMean μ η t = x := by
  obtain ⟨t, ht, hroot⟩ := exists_moderateArrayMean_eq hη hδ hbound hc hv hx hsmall
  refine ⟨t, ⟨ht, hroot⟩, ?_⟩
  intro y hy
  exact (moderateArrayMean_strictMono hη hδ hbound hc hv).injective (hy.2.trans hroot.symm)

end
end RectangleCLT.Companion.SplitV4
