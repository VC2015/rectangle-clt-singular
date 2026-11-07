import RectangleCLTCompanion.SplitV4.IntrinsicCubeBoundary
import Mathlib.Order.Interval.Set.Infinite
import Mathlib.Analysis.SpecificLimits.Basic

/-! The finite-threshold perturbation and limiting steps printed in the
proof of Lemma C.1, manuscript lines 3204--3207. These complement the
existing direct supporting-branch proof; no final boundary estimate is
used to establish the perturbation or the event inclusion. -/

open Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The exact uniqueness condition used at the start of the printed proof.
It requires one strictly maximizing affine branch at each sign vertex. -/
def CubeUniqueMax {m n : ℕ} (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) : Prop :=
  ∀ x : Kane.Cube n, ∃ α : Fin m, ∀ β : Fin m, β ≠ α →
    cubeLinear (B β) x - a β < cubeLinear (B α) x - a α

/-- Arbitrarily small threshold perturbations make every pair of affine
values distinct at every vertex. A scalar perturbation avoids a finite
set of bad slopes; this also covers repeated coefficient rows. -/
theorem exists_small_threshold_perturbation {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a' : Fin m → ℝ, (∀ α, |a' α - a α| < ρ) ∧
      ∀ x : Kane.Cube n, Function.Injective (fun α => cubeLinear (B α) x - a' α) := by
  classical
  let bad : Finset ℝ := Finset.univ.image (fun z : Kane.Cube n × (Fin m × Fin m) =>
    ((cubeLinear (B z.2.1) z.1 - a z.2.1) - (cubeLinear (B z.2.2) z.1 - a z.2.2)) /
      ((z.2.1.val : ℝ) - (z.2.2.val : ℝ)))
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hi : (Set.Ioo (0 : ℝ) (ρ / ((m : ℝ) + 1))).Infinite :=
    Set.Ioo_infinite (div_pos hρ hm)
  obtain ⟨ε, hε, havoid⟩ := hi.exists_not_mem_finset bad
  let a' : Fin m → ℝ := fun α => a α + ε * (α.val : ℝ)
  refine ⟨a', ?_, ?_⟩
  · intro α
    have hα : (α.val : ℝ) ≤ (m : ℝ) + 1 := by
      exact_mod_cast (show α.val ≤ m + 1 by omega)
    have hb : ε * ((m : ℝ) + 1) < ρ := (lt_div_iff₀ hm).mp hε.2
    have he : a' α - a α = ε * (α.val : ℝ) := by dsimp [a']; ring
    rw [he, abs_of_nonneg (mul_nonneg hε.1.le (Nat.cast_nonneg _))]
    exact (mul_le_mul_of_nonneg_left hα hε.1.le).trans_lt hb
  · intro x α β heq
    by_contra hne
    have hnat : α.val ≠ β.val := fun he => hne (Fin.ext he)
    have hreal : (α.val : ℝ) ≠ (β.val : ℝ) := by exact_mod_cast hnat
    have hd : (α.val : ℝ) - (β.val : ℝ) ≠ 0 := sub_ne_zero.mpr hreal
    have hquot : ε =
        ((cubeLinear (B α) x - a α) - (cubeLinear (B β) x - a β)) /
          ((α.val : ℝ) - (β.val : ℝ)) := by
      apply (eq_div_iff hd).mpr
      dsimp [a'] at heq
      nlinarith only [heq]
    apply havoid
    apply Finset.mem_image.mpr
    refine ⟨(x, (α, β)), Finset.mem_univ _, ?_⟩
    exact hquot.symm

/-- The printed uniqueness perturbation, with a strict maximizing branch
at every cube vertex and the original coefficient matrix unchanged. -/
theorem exists_small_unique_threshold_perturbation {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ a' : Fin m → ℝ, (∀ α, |a' α - a α| < ρ) ∧ CubeUniqueMax B a' := by
  obtain ⟨a', hnear, hinj⟩ := exists_small_threshold_perturbation B a hρ
  refine ⟨a', hnear, ?_⟩
  intro x
  refine ⟨activeCubeBranch B a' x, ?_⟩
  intro β hβ
  have hle := affineCubeMaximum_supports B a' x β
  rw [activeCubeBranch_attains] at hle
  apply lt_of_le_of_ne hle
  intro he
  exact hβ ((hinj x) he)

/-- Uniform threshold control gives uniform control of the actual finite
maximum, independently of whether there are ties. -/
theorem affineCubeMaximum_threshold_stability {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a a' : Fin m → ℝ) {ρ : ℝ}
    (hnear : ∀ α, |a' α - a α| ≤ ρ) (x : Kane.Cube n) :
    |affineCubeMaximum B a' x - affineCubeMaximum B a x| ≤ ρ := by
  have hA := activeCubeBranch_attains B a x
  have hA' := activeCubeBranch_attains B a' x
  have hS := affineCubeMaximum_supports B a x (activeCubeBranch B a' x)
  have hS' := affineCubeMaximum_supports B a' x (activeCubeBranch B a x)
  have hn := abs_le.mp (hnear (activeCubeBranch B a x))
  have hn' := abs_le.mp (hnear (activeCubeBranch B a' x))
  apply abs_le.mpr
  constructor <;> linarith

/-- The closed original interval lies in the expanded perturbed interval.
The statement remains valid at atoms and needs no boundary-null assumption. -/
theorem cube_boundary_event_subset_perturbed {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a a' : Fin m → ℝ) (t h ρ : ℝ)
    (hnear : ∀ α, |a' α - a α| ≤ ρ) :
    {x | t ≤ affineCubeMaximum B a x ∧ affineCubeMaximum B a x ≤ t + h} ⊆
      {x | t - ρ ≤ affineCubeMaximum B a' x ∧
        affineCubeMaximum B a' x ≤ (t - ρ) + (h + 2 * ρ)} := by
  intro x hx
  have hs := abs_le.mp (affineCubeMaximum_threshold_stability B a a' hnear x)
  constructor <;> linarith [hx.1, hx.2]

theorem cube_boundary_indicator_le_perturbed {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a a' : Fin m → ℝ) (t h ρ : ℝ)
    (hnear : ∀ α, |a' α - a α| ≤ ρ) (x : Kane.Cube n) :
    cubeBoundaryIndicator B a t h x ≤ cubeBoundaryIndicator B a' (t - ρ) (h + 2 * ρ) x := by
  by_cases hx : t ≤ affineCubeMaximum B a x ∧ affineCubeMaximum B a x ≤ t + h
  · have hy : t - ρ ≤ affineCubeMaximum B a' x ∧
        affineCubeMaximum B a' x ≤ (t - ρ) + (h + 2 * ρ) :=
      cube_boundary_event_subset_perturbed B a a' t h ρ hnear hx
    unfold cubeBoundaryIndicator
    rw [if_pos hx, if_pos hy]
  · simp only [cubeBoundaryIndicator, if_neg hx]
    split_ifs <;> norm_num

/-- Passing through all positive perturbation radii recovers the exact
printed constant. Only continuity of the numerical bound is used; no
convergence of boundary-event indicators is asserted. -/
theorem cube_boundary_bound_of_all_positive_radii (P h b v M : ℝ)
    (hbound : ∀ ρ : ℝ, 0 < ρ → P ≤ (h + 2 * ρ + 8 * b) / v * M) :
    P ≤ (h + 8 * b) / v * M := by
  have hr : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have hh := (((tendsto_const_nhds (x := h)).add
    ((tendsto_const_nhds (x := (2 : ℝ))).mul hr)).add
      (tendsto_const_nhds (x := 8 * b))).div_const v |>.mul_const M
  simp only [mul_zero, add_zero] at hh
  apply ge_of_tendsto hh
  exact Filter.Eventually.of_forall (fun n => hbound _ (by positivity))

end
end RectangleCLT.Companion.SplitV4.Printed
