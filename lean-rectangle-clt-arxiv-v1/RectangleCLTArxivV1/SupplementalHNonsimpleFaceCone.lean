import Mathlib.Analysis.Convex.Cone.InnerDual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.Sequences

/-! Finite normal cones with a genuine strict polar vector.  A strict
polar vector makes every nonnegative coefficient bounded whenever its
physical positive combination is bounded.  Compactness then proves
closedness; no polyhedral cone identity is assumed. -/
namespace RectangleCLTArxivV1
open Set Filter Bornology
open scoped BigOperators InnerProductSpace Topology
noncomputable section

variable {ι E : Type*} [Fintype ι] [NormedAddCommGroup E]
  [InnerProductSpace ℝ E]

def nonsimpleGeneratedCone (u : ι → E) : ConvexCone ℝ E where
  carrier := {x | ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ x = ∑ i, a i • u i}
  smul_mem' := by
    rintro c hc x ⟨a,ha,rfl⟩
    exact ⟨fun i => c*a i, fun i => mul_nonneg hc.le (ha i), by simp [Finset.smul_sum,smul_smul]⟩
  add_mem' := by
    rintro x ⟨a,ha,rfl⟩ y ⟨b,hb,rfl⟩
    exact ⟨fun i => a i+b i, fun i => add_nonneg (ha i) (hb i), by simp [add_smul,Finset.sum_add_distrib]⟩

@[simp] theorem mem_nonsimpleGeneratedCone (u : ι → E) (x : E) :
    x ∈ nonsimpleGeneratedCone u ↔
      ∃ a : ι → ℝ, (∀ i, 0 ≤ a i) ∧ x = ∑ i, a i • u i := Iff.rfl

theorem zero_mem_nonsimpleGeneratedCone (u : ι → E) :
    (0 : E) ∈ nonsimpleGeneratedCone u := by
  exact ⟨0, fun _ => le_rfl, by simp⟩

theorem generator_mem_nonsimpleGeneratedCone (u : ι → E) (i : ι) :
    u i ∈ nonsimpleGeneratedCone u := by
  classical
  refine ⟨Pi.single i 1,?_,?_⟩
  · intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · simp [Pi.single_apply,ite_smul]

theorem nonsimpleGeneratedCone_innerDual (u : ι → E) :
    ((nonsimpleGeneratedCone u : Set E).innerDualCone : Set E) =
      {y | ∀ i, 0 ≤ ⟪u i,y⟫_ℝ} := by
  ext y
  constructor
  · intro hy i
    exact hy (u i) (generator_mem_nonsimpleGeneratedCone u i)
  · intro hy
    rintro x ⟨a,ha,rfl⟩
    simp only [sum_inner,inner_smul_left,conj_trivial]
    exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hy i))

theorem nonsimpleGeneratedCone_coefficient_bound (u : ι → E) (d : E)
    (hd : ∀ i, ⟪u i,d⟫_ℝ < 0) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i) (i : ι) :
    a i ≤ (‖∑ j, a j • u j‖*‖d‖)/(-⟪u i,d⟫_ℝ) := by
  classical
  have hterm : a i*(-⟪u i,d⟫_ℝ) ≤ ∑ j, a j*(-⟪u j,d⟫_ℝ) :=
    Finset.single_le_sum (fun j _ => mul_nonneg (ha j) (neg_nonneg.mpr (hd j).le))
      (Finset.mem_univ i)
  have he : (∑ j, a j*(-⟪u j,d⟫_ℝ)) = -⟪∑ j, a j • u j,d⟫_ℝ := by
    simp only [sum_inner,inner_smul_left,conj_trivial,←Finset.sum_neg_distrib,mul_neg]
  apply (le_div_iff₀ (neg_pos.mpr (hd i))).mpr
  exact hterm.trans (he ▸ (neg_le_abs _).trans (abs_real_inner_le_norm _ _))

theorem nonsimpleGeneratedCone_isClosed (u : ι → E) (d : E)
    (hd : ∀ i, ⟪u i,d⟫_ℝ < 0) : IsClosed (nonsimpleGeneratedCone u : Set E) := by
  classical
  apply isSeqClosed_iff_isClosed.mp
  intro x y hx hxy
  choose a ha hrep using hx
  obtain ⟨M,hM⟩ := (isBounded_iff_forall_norm_le.mp (Metric.isBounded_range_of_tendsto x hxy))
  let R : ι → ℝ := fun i => (M*‖d‖)/(-⟪u i,d⟫_ℝ)
  let B : Set (ι → ℝ) := Set.pi Set.univ (fun i => Set.Icc 0 (R i))
  have hcompact : IsCompact B := isCompact_univ_pi (fun i => isCompact_Icc)
  have hB (n : ℕ) : a n ∈ B := by
    intro i _
    refine ⟨ha n i,?_⟩
    apply (nonsimpleGeneratedCone_coefficient_bound u d hd (a n) (ha n) i).trans
    dsimp only [R]
    apply div_le_div_of_nonneg_right _ (neg_nonneg.mpr (hd i).le)
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg d)
    rw [←hrep n]
    exact hM (x n) (Set.mem_range_self n)
  obtain ⟨c,hc,φ,hφ,hac⟩ := hcompact.tendsto_subseq hB
  have hcont : Continuous (fun z : ι → ℝ => ∑ i, z i • u i) := by fun_prop
  have hsum := (hcont.tendsto c).comp hac
  have hlim := hxy.comp hφ.tendsto_atTop
  have heq : (fun n => ∑ i, a (φ n) i • u i) = x ∘ φ := by
    funext n
    exact (hrep (φ n)).symm
  change Tendsto (fun n => ∑ i, a (φ n) i • u i) atTop _ at hsum
  rw [heq] at hsum
  exact ⟨c,fun i => (hc i (Set.mem_univ i)).1,tendsto_nhds_unique hlim hsum⟩

theorem nonsimpleGeneratedCone_bipolar (u : ι → E) (d : E)
    [CompleteSpace E] (hd : ∀ i, ⟪u i,d⟫_ℝ < 0) :
    (((nonsimpleGeneratedCone u : Set E).innerDualCone : Set E).innerDualCone : Set E) =
      (nonsimpleGeneratedCone u : Set E) :=
  congrArg (fun K : ConvexCone ℝ E => (K : Set E))
    ((nonsimpleGeneratedCone u).innerDualCone_of_innerDualCone_eq_self
      ⟨0,zero_mem_nonsimpleGeneratedCone u⟩ (nonsimpleGeneratedCone_isClosed u d hd))

/-- A finite strict-polar Farkas theorem, with the signs used for outward
normal cones: every vector satisfying all active tangent inequalities
has nonpositive pairing with exactly the nonnegative generated cone. -/
theorem nonsimpleGeneratedCone_mem_iff_polar (u : ι → E) (d : E)
    [CompleteSpace E] (hd : ∀ i, ⟪u i,d⟫_ℝ < 0) (x : E) :
    x ∈ nonsimpleGeneratedCone u ↔
      ∀ y : E, (∀ i, ⟪u i,y⟫_ℝ ≤ 0) → ⟪x,y⟫_ℝ ≤ 0 := by
  constructor
  · rintro ⟨a,ha,rfl⟩ y hy
    simp only [sum_inner,inner_smul_left,conj_trivial]
    exact Finset.sum_nonpos (fun i _ => mul_nonpos_of_nonneg_of_nonpos (ha i) (hy i))
  · intro hx
    by_contra hnot
    obtain ⟨y,hy,hyx⟩ := (nonsimpleGeneratedCone u).hyperplane_separation_of_nonempty_of_isClosed_of_nmem
      ⟨0,zero_mem_nonsimpleGeneratedCone u⟩ (nonsimpleGeneratedCone_isClosed u d hd) hnot
    have hnegative (i : ι) : ⟪u i,-y⟫_ℝ ≤ 0 := by
      rw [inner_neg_right]
      exact neg_nonpos.mpr (hy (u i) (generator_mem_nonsimpleGeneratedCone u i))
    have h := hx (-y) hnegative
    rw [inner_neg_right] at h
    have hcomm := real_inner_comm x y
    linarith

theorem nonsimpleGeneratedCone_no_cancellation (u : ι → E) (d : E)
    (hd : ∀ i, ⟪u i,d⟫_ℝ < 0) (a : ι → ℝ) (ha : ∀ i, 0 ≤ a i)
    (hz : (∑ i, a i • u i) = 0) : ∀ i, a i = 0 := by
  intro i
  have hb := nonsimpleGeneratedCone_coefficient_bound u d hd a ha i
  rw [hz,norm_zero,zero_mul,zero_div] at hb
  exact le_antisymm hb (ha i)

/-- Active-family version, with no cardinality or simplicity restriction. -/
def nonsimpleActiveGeneratedCone (u : ι → E) (S : Finset ι) : ConvexCone ℝ E :=
  nonsimpleGeneratedCone (fun i : S => u i)

omit [Fintype ι] in
theorem nonsimpleActiveGeneratedCone_mem_iff (u : ι → E) (S : Finset ι) (x : E) :
    x ∈ nonsimpleActiveGeneratedCone u S ↔
      ∃ a : ι → ℝ, (∀ i ∈ S, 0 ≤ a i) ∧ x = ∑ i ∈ S, a i • u i := by
  classical
  constructor
  · rintro ⟨a,ha,hx⟩
    let c : ι → ℝ := fun i => if h : i ∈ S then a ⟨i,h⟩ else 0
    refine ⟨c,fun i hi => ?_,?_⟩
    · simpa only [c,dif_pos hi] using ha ⟨i,hi⟩
    · rw [hx,←S.sum_coe_sort (fun i => c i • u i)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [c,dif_pos i.property]
  · rintro ⟨a,ha,hx⟩
    refine ⟨fun i : S => a i,fun i => ha i i.property,?_⟩
    change x = ∑ i : S, a i.val • u i.val
    rw [S.sum_coe_sort (fun i => a i • u i)]
    exact hx

omit [Fintype ι] in
theorem nonsimpleActiveGeneratedCone_isClosed (u : ι → E) (S : Finset ι) (d : E)
    (hd : ∀ i ∈ S, ⟪u i,d⟫_ℝ < 0) :
    IsClosed (nonsimpleActiveGeneratedCone u S : Set E) :=
  nonsimpleGeneratedCone_isClosed (fun i : S => u i) d (fun i => hd i i.property)

omit [Fintype ι] in
theorem nonsimpleActiveGeneratedCone_mem_iff_polar (u : ι → E) (S : Finset ι) (d : E)
    [CompleteSpace E] (hd : ∀ i ∈ S, ⟪u i,d⟫_ℝ < 0) (x : E) :
    x ∈ nonsimpleActiveGeneratedCone u S ↔
      ∀ y : E, (∀ i ∈ S, ⟪u i,y⟫_ℝ ≤ 0) → ⟪x,y⟫_ℝ ≤ 0 := by
  simpa only [nonsimpleActiveGeneratedCone,Subtype.forall] using
    nonsimpleGeneratedCone_mem_iff_polar (fun i : S => u i) d (fun i => hd i i.property) x

end
end RectangleCLTArxivV1
