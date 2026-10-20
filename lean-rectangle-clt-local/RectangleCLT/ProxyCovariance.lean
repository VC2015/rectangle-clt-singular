import Mathlib.Data.Finset.Fold
import Mathlib.Data.Fintype.Prod
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Entrywise covariance discrepancy

Elementary covariance facts needed by the local covariance-proxy route.
These statements concern actual matrix entries and do not assume any
Gaussian approximation estimate.
-/

namespace RectangleCLT

noncomputable section

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Maximum entrywise covariance discrepancy, including the diagonal. -/
def proxyCovarianceDiscrepancy {p : ℕ}
    (S T : Fin p → Fin p → 𝕜) : 𝕜 :=
  (Finset.univ : Finset (Fin p × Fin p)).fold max 0
    (fun jk => |S jk.1 jk.2 - T jk.1 jk.2|)

theorem proxyCovarianceDiscrepancy_nonneg {p : ℕ}
    (S T : Fin p → Fin p → 𝕜) :
    0 ≤ proxyCovarianceDiscrepancy S T := by
  exact (Finset.le_fold_max (0 : 𝕜)).mpr (Or.inl le_rfl)

theorem abs_entry_sub_le_proxyCovarianceDiscrepancy {p : ℕ}
    (S T : Fin p → Fin p → 𝕜) (j k : Fin p) :
    |S j k - T j k| ≤ proxyCovarianceDiscrepancy S T := by
  apply (Finset.le_fold_max _).mpr
  exact Or.inr ⟨(j, k), Finset.mem_univ _, le_rfl⟩

/-- Entrywise perturbations lose at most their maximum discrepancy from
an off-diagonal correlation gap. -/
theorem proxy_pair_gap_stability {p : ℕ}
    (S T : Fin p → Fin p → 𝕜) (c : 𝕜)
    (hT : ∀ j k, j ≠ k → |T j k| ≤ 1 - c) :
    ∀ j k, j ≠ k →
      |S j k| ≤ 1 - (c - proxyCovarianceDiscrepancy S T) := by
  intro j k hjk
  calc
    |S j k| = |(S j k - T j k) + T j k| := by congr 1 <;> ring
    _ ≤ |S j k - T j k| + |T j k| := abs_add _ _
    _ ≤ proxyCovarianceDiscrepancy S T + (1 - c) :=
      add_le_add (abs_entry_sub_le_proxyCovarianceDiscrepancy S T j k) (hT j k hjk)
    _ = 1 - (c - proxyCovarianceDiscrepancy S T) := by ring

theorem proxy_pair_gap_stability_half {p : ℕ}
    (S T : Fin p → Fin p → 𝕜) (c : 𝕜)
    (hT : ∀ j k, j ≠ k → |T j k| ≤ 1 - c)
    (hsmall : proxyCovarianceDiscrepancy S T ≤ c / 2) :
    ∀ j k, j ≠ k → |S j k| ≤ 1 - c / 2 := by
  intro j k hjk
  have h := proxy_pair_gap_stability S T c hT j k hjk
  linarith

/-- Unit diagonal is preserved by the unequal-covariance Gaussian path. -/
theorem proxy_interpolated_unit_diagonal {p : ℕ}
    (S T : Fin p → Fin p → 𝕜)
    (hS : ∀ j, S j j = 1) (hT : ∀ j, T j j = 1) (t : 𝕜) :
    ∀ j, (1 - t) * S j j + t * T j j = 1 := by
  intro j
  rw [hS j, hT j]
  ring

end

end RectangleCLT
