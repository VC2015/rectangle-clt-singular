import RectangleCLTCompanion.SplitV4.LogisticPaddingLimits

/-! The full padded matrix limit displayed in printed B.4. The earlier
proof takes its original-coordinate block before Fatou; these theorems
verify entrywise and nuclear convergence of the full padded matrix first. -/

open MeasureTheory Filter
open scoped Topology BigOperators

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Conditional DCT in every entry of the full `(r+m)`-dimensional score
matrix, including the added coordinates and off-diagonal blocks. -/
theorem logisticPaddedScore_full_entry_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) (j l : Fin (r + m)) :
    Tendsto (fun n => logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPaddedBase (m := m) (lam n) x) j l) atTop
      (𝓝 (weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g)) j l)) := by
  let w (n : ℕ) (g : Vector (r + m)) :=
    logisticTupleWeight (logisticPaddedNormals u (lam n)) a h α
      (logisticPaddedBase (m := m) (lam n) x + σ • g)
  have hw (n : ℕ) : Measurable (w n) :=
    ((continuous_logisticTupleWeight (logisticPaddedNormals u (lam n)) a h hh α).comp
      (continuous_const.add (continuous_const.smul continuous_id))).measurable
  exact weightedScore_entry_tendsto_of_bounded_weights w _ hw
    (fun n g => logisticTupleWeight_abs_le_one _ a h hh α _)
    (fun g => logisticPaddedTupleWeight_tendsto u a h hh α lam hlam hlam0 hlam1 x g σ) j l

/-- Full padded nuclear norm continuity follows after conditional DCT,
just as in the printed order of steps. -/
theorem logisticPaddedScore_full_nuclear_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) :
    Tendsto (fun n => symmetricNuclearNorm
      (logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
        (logisticPaddedBase (m := m) (lam n) x))) atTop
      (𝓝 (symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g))))) := by
  apply continuous_symmetricNuclearNorm.continuousAt.tendsto.comp
  exact tendsto_pi_nhds.mpr (fun j => tendsto_pi_nhds.mpr (fun l =>
    logisticPaddedScore_full_entry_tendsto u a h hh α lam hlam hlam0 hlam1 x σ j l))

/-- The finite ordered-tuple sum of full nuclear norms also converges
pointwise at every original base point before the printed Fatou step. -/
theorem logisticPaddedScore_full_nuclear_sum_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) :
    Tendsto (fun n => ∑ α : Fin k → Fin m, symmetricNuclearNorm
      (logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
        (logisticPaddedBase (m := m) (lam n) x))) atTop
      (𝓝 (∑ α : Fin k → Fin m, symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g))))) :=
  tendsto_finset_sum Finset.univ (fun α _ =>
    logisticPaddedScore_full_nuclear_tendsto u a h hh α lam hlam hlam0 hlam1 x σ)

end
end RectangleCLT.Companion.SplitV4.Printed
