import RectangleCLTCompanion.SplitV4.Printed.LowerModerateTail

/-! F.1 for every independent bounded array and every x>=0, through
actual product Esscher laws, literal independent-copy cumulant bounds,
and the nonnegative strict tilted Laplace comparison. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
universe u
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
  {n : ℕ} {η : Fin n→Ω→ℝ} {δ : ℝ}

theorem moderateScalarTail_bound_printed (hn : 1 ≤ n) (hη : ∀ i, Measurable (η i))
    (hind : iIndepFun η μ) (hδ : 0 ≤ δ) (hbound : ∀ i, ∀ᵐ ω ∂μ, |η i ω| ≤ δ)
    (hc : ∀ i, (∫ ω, η i ω ∂μ) = 0) (hv : (∑ i, ∫ ω, η i ω ^ 2 ∂μ) = 1)
    {x : ℝ} (hx : 0 ≤ x) (hsmall : moderateTailSmallConstant * (δ * (1 + x)) ≤ 1) :
    0 < μ.real {ω | x < moderateScalarSum η ω} ∧
    |Real.log (μ.real {ω | x < moderateScalarSum η ω} / standardNormalUpperTail x) -
      moderateArrayGamma μ η * x ^ 3 / 6| ≤
        moderateTailRemainderConstant * (δ * (1 + x) + δ ^ 2 * x ^ 4) := by
  let ν : Fin n → Measure ℝ := fun i => μ.map (η i)
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
  have ht := moderateProductTail_nonneg_printed ν hn hδ hb hc' hv' hx hsmall
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
theorem uniformScalarModerateTail_printed : ∃ a C : ℝ, 0 < a ∧ 0 < C ∧
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
  exact moderateScalarTail_bound_printed hn hη hind hδ.le hb hc hv hx hs



end
end RectangleCLT.Companion.SplitV4.Printed
