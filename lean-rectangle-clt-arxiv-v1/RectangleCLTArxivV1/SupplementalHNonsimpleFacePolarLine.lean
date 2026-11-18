import RectangleCLTArxivV1.SupplementalHNonsimpleFaceCone
import Mathlib.Data.Finset.Max

/-! Exact finite line clipping in a polyhedral polar slice.  Endpoints
are finite minimum ratios; all constraints remain present, old zeros
persist, and each endpoint creates a zero whose slope is nonzero. -/
namespace RectangleCLTArxivV1
open scoped BigOperators InnerProductSpace
noncomputable section

variable {ι : Type*} [Fintype ι]

theorem nonsimple_polar_positive_endpoint (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∀ i, a i = 0 → b i = 0)
    (hneg : ∃ i, b i < 0) :
    ∃ (t : ℝ) (j : ι), 0 < t ∧ b j < 0 ∧
      (∀ i, 0 ≤ a i+t*b i) ∧ a j+t*b j = 0 := by
  classical
  let S : Finset ι := Finset.univ.filter (fun i => b i < 0)
  obtain ⟨j₀,hj₀⟩ := hneg
  have hS : S.Nonempty := ⟨j₀,by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact hj₀⟩
  obtain ⟨j,hj,hmin⟩ := S.exists_min_image (fun i => a i/(-b i)) hS
  have hbj : b j < 0 := (Finset.mem_filter.mp hj).2
  have haj : 0 < a j := by
    by_contra hnot
    have hzero : a j = 0 := le_antisymm (le_of_not_gt hnot) (ha j)
    exact (ne_of_lt hbj) (hz j hzero)
  let t : ℝ := a j/(-b j)
  have ht : 0 < t := div_pos haj (neg_pos.mpr hbj)
  refine ⟨t,j,ht,hbj,?_,?_⟩
  · intro i
    by_cases hbi : b i < 0
    · have hi : i∈S := by simp only [S,Finset.mem_filter,Finset.mem_univ,true_and]; exact hbi
      have hbound : t ≤ a i/(-b i) := hmin i hi
      have hprod := (le_div_iff₀ (neg_pos.mpr hbi)).mp hbound
      nlinarith
    · exact add_nonneg (ha i) (mul_nonneg ht.le (le_of_not_gt hbi))
  · have hprod : t*(-b j) = a j := div_mul_cancel₀ _ (neg_ne_zero.mpr hbj.ne)
    nlinarith

theorem nonsimple_polar_negative_endpoint (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∀ i, a i = 0 → b i = 0)
    (hpos : ∃ i, 0 < b i) :
    ∃ (t : ℝ) (j : ι), t < 0 ∧ 0 < b j ∧
      (∀ i, 0 ≤ a i+t*b i) ∧ a j+t*b j = 0 := by
  obtain ⟨t,j,ht,hbj,hfeas,hzero⟩ := nonsimple_polar_positive_endpoint a (fun i => -b i) ha
    (fun i hi => by dsimp only; rw [hz i hi,neg_zero]) (by obtain ⟨i,hi⟩ := hpos; exact ⟨i,neg_neg_of_pos hi⟩)
  refine ⟨-t,j,neg_neg_of_pos ht,neg_neg_iff_pos.mp hbj,?_,?_⟩
  · intro i
    nlinarith [hfeas i]
  · nlinarith

/-- Actual two-sided finite endpoints, with a strict convex decomposition
of the original line parameter zero. No extrema or clipping conclusion
is supplied as a premise. -/
theorem nonsimple_polar_line_split (a b : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (hz : ∀ i, a i = 0 → b i = 0)
    (hpos : ∃ i, 0 < b i) (hneg : ∃ i, b i < 0) :
    ∃ (tminus tplus α β : ℝ) (jminus jplus : ι),
      tminus < 0 ∧ 0 < tplus ∧ 0 < α ∧ 0 < β ∧ α+β = 1 ∧
      α*tminus+β*tplus = 0 ∧
      0 < b jminus ∧ b jplus < 0 ∧
      a jminus+tminus*b jminus = 0 ∧ a jplus+tplus*b jplus = 0 ∧
      (∀ i, 0 ≤ a i+tminus*b i) ∧ (∀ i, 0 ≤ a i+tplus*b i) ∧
      (∀ i, a i = 0 → a i+tminus*b i = 0 ∧ a i+tplus*b i = 0) ∧
      ∀ t∈Set.Icc tminus tplus, ∀ i, 0 ≤ a i+t*b i := by
  obtain ⟨tm,jm,htm,hbm,hm,hzm⟩ := nonsimple_polar_negative_endpoint a b ha hz hpos
  obtain ⟨tp,jp,htp,hbp,hp,hzp⟩ := nonsimple_polar_positive_endpoint a b ha hz hneg
  have hden : 0 < tp-tm := by linarith
  let α : ℝ := tp/(tp-tm)
  let β : ℝ := (-tm)/(tp-tm)
  have hα : 0 < α := div_pos htp hden
  have hβ : 0 < β := div_pos (neg_pos.mpr htm) hden
  have hsum : α+β = 1 := by
    dsimp only [α,β]
    field_simp
    ring
  have htime : α*tm+β*tp = 0 := by
    dsimp only [α,β]
    field_simp
    ring
  refine ⟨tm,tp,α,β,jm,jp,htm,htp,hα,hβ,hsum,htime,hbm,hbp,hzm,hzp,hm,hp,?_,?_⟩
  · intro i hi
    simp only [hi,hz i hi,mul_zero,add_zero,and_self]
  · intro t ht i
    by_cases hbi : 0 ≤ b i
    · have hh := mul_le_mul_of_nonneg_right ht.1 hbi
      linarith [hm i]
    · have hh := mul_le_mul_of_nonpos_right ht.2 (le_of_not_ge hbi)
      linarith [hp i]

theorem nonsimple_polar_line_vector_decomposition
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (w v : E) (tm tp α β : ℝ) (hsum : α+β = 1) (htime : α*tm+β*tp = 0) :
    w = α • (w+tm • v)+β • (w+tp • v) := by
  calc
    w = (α+β) • w+(α*tm+β*tp) • v := by rw [hsum,htime,one_smul,zero_smul,add_zero]
    _ = _ := by module

theorem nonsimple_zero_sum_slopes_both_signs (b : ι → ℝ)
    (hsum : ∑ i, b i = 0) (hnonzero : ∃ i, b i ≠ 0) :
    (∃ i, 0 < b i) ∧ (∃ i, b i < 0) := by
  classical
  constructor
  · by_contra hnot
    push_neg at hnot
    have hall := (Finset.sum_eq_zero_iff_of_nonpos (fun i (_ : i∈Finset.univ) => hnot i)).mp hsum
    obtain ⟨i,hi⟩ := hnonzero
    exact hi (hall i (Finset.mem_univ i))
  · by_contra hnot
    push_neg at hnot
    have hall := (Finset.sum_eq_zero_iff_of_nonneg (fun i (_ : i∈Finset.univ) => hnot i)).mp hsum
    obtain ⟨i,hi⟩ := hnonzero
    exact hi (hall i (Finset.mem_univ i))

/-- Spanning generators force a nonzero direction of zero total slope
to have genuine positive and negative slopes. -/
theorem nonsimple_polar_inner_slopes_both_signs
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ι → E) (v : E) (hspan : Submodule.span ℝ (Set.range u) = ⊤)
    (hv : v ≠ 0) (hsum : ⟪∑ i, u i,v⟫_ℝ = 0) :
    (∃ i, 0 < ⟪u i,v⟫_ℝ) ∧ (∃ i, ⟪u i,v⟫_ℝ < 0) := by
  apply nonsimple_zero_sum_slopes_both_signs
  · simpa only [sum_inner] using hsum
  · by_contra hnot
    push_neg at hnot
    have hall : ∀ x ∈ Submodule.span ℝ (Set.range u), ⟪x,v⟫_ℝ = 0 := by
      intro x hx
      induction hx using Submodule.span_induction with
      | mem x hx => obtain ⟨i,rfl⟩ := hx; exact hnot i
      | zero => simp
      | add x y hx hy hx0 hy0 =>
          rw [inner_add_left,hx0,hy0,add_zero]
      | smul a x hx hx0 =>
          rw [inner_smul_left,conj_trivial,hx0,mul_zero]
    have hself := hall v (hspan ▸ Submodule.mem_top)
    exact hv (inner_self_eq_zero.mp hself)

theorem nonsimple_polar_inner_line_split
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (u : ι → E) (w v : E)
    (hw : ∀ i, 0 ≤ ⟪u i,w⟫_ℝ)
    (hz : ∀ i, ⟪u i,w⟫_ℝ = 0 → ⟪u i,v⟫_ℝ = 0)
    (hpos : ∃ i, 0 < ⟪u i,v⟫_ℝ) (hneg : ∃ i, ⟪u i,v⟫_ℝ < 0) :
    ∃ (tm tp α β : ℝ) (jm jp : ι), tm < 0 ∧ 0 < tp ∧ 0 < α ∧ 0 < β ∧
      α+β = 1 ∧ α*tm+β*tp = 0 ∧
      0 < ⟪u jm,v⟫_ℝ ∧ ⟪u jp,v⟫_ℝ < 0 ∧
      ⟪u jm,w+tm • v⟫_ℝ = 0 ∧ ⟪u jp,w+tp • v⟫_ℝ = 0 ∧
      (∀ i, 0 ≤ ⟪u i,w+tm • v⟫_ℝ) ∧ (∀ i, 0 ≤ ⟪u i,w+tp • v⟫_ℝ) ∧
      (∀ i, ⟪u i,w⟫_ℝ = 0 → ⟪u i,w+tm • v⟫_ℝ = 0 ∧ ⟪u i,w+tp • v⟫_ℝ = 0) ∧
      (∀ t∈Set.Icc tm tp, ∀ i, 0 ≤ ⟪u i,w+t • v⟫_ℝ) ∧
      w = α • (w+tm • v)+β • (w+tp • v) := by
  obtain ⟨tm,tp,α,β,jm,jp,htm,htp,hα,hβ,hs,ht,hjm,hjp,hzm,hzp,hm,hp,hzold,hall⟩ :=
    nonsimple_polar_line_split (fun i => ⟪u i,w⟫_ℝ) (fun i => ⟪u i,v⟫_ℝ) hw hz hpos hneg
  refine ⟨tm,tp,α,β,jm,jp,htm,htp,hα,hβ,hs,ht,hjm,hjp,?_,?_,?_,?_,?_,?_,?_⟩
  · simpa only [inner_add_right,inner_smul_right] using hzm
  · simpa only [inner_add_right,inner_smul_right] using hzp
  · simpa only [inner_add_right,inner_smul_right] using hm
  · simpa only [inner_add_right,inner_smul_right] using hp
  · simpa only [inner_add_right,inner_smul_right] using hzold
  · simpa only [inner_add_right,inner_smul_right] using hall
  · exact nonsimple_polar_line_vector_decomposition w v tm tp α β hs ht

end
end RectangleCLTArxivV1
