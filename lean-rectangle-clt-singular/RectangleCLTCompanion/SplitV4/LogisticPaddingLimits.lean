import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
import RectangleCLTCompanion.SplitV4.LogisticMatrixLimits

/-! Conditional dominated convergence for the actual padded logistic score
matrices. The limiting upper-left matrix is identified with the original
Gaussian score using the proved first-block Gaussian law.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem continuous_logisticTupleWeight {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m) :
    Continuous (logisticTupleWeight u a h α) := by
  have hc := (continuous_selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true))).comp
    (show Continuous (Matrix.mulVec u) from continuous_const.matrix_mulVec continuous_id)
  simpa only [Function.comp_def, upperFaceSmoother_selectorWeight] using hc

theorem logisticTupleWeight_abs_le_one {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m) (x : Vector r) :
    |logisticTupleWeight u a h α x| ≤ 1 := by
  rw [← upperFaceSmoother_selectorWeight u a h hh α x,
    abs_of_nonneg (selectorWeight_nonneg _ _ _)]
  exact selectorWeight_le_one _ _ _

def secondGaussianBlock {r s : ℕ} (g : Vector (r + s)) : Vector s :=
  fun j => g (Fin.natAdd r j)

theorem append_gaussianBlocks {r s : ℕ} (g : Vector (r + s)) :
    Fin.append (firstGaussianBlock g) (secondGaussianBlock g) = g := by
  funext j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  all_goals simp [firstGaussianBlock, secondGaussianBlock]

theorem logisticPaddedTupleWeight_tendsto {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (g : Vector (r + m)) (σ : ℝ) :
    Tendsto (fun n => logisticTupleWeight (logisticPaddedNormals u (lam n)) a h α
      (logisticPaddedBase (m := m) (lam n) x + σ • g)) atTop
      (𝓝 (logisticTupleWeight u a h α (x + σ • firstGaussianBlock g))) := by
  have hY : Tendsto (fun n => Matrix.mulVec (logisticPaddedNormals u (lam n))
      (logisticPaddedBase (m := m) (lam n) x + σ • g)) atTop
      (𝓝 (Matrix.mulVec u (x + σ • firstGaussianBlock g))) := by
    apply tendsto_pi_nhds.mpr
    intro j
    have hh' := logisticPaddedNormals_joint_projection_tendsto u lam hlam hlam0 hlam1 x
      (firstGaussianBlock g) (secondGaussianBlock g) σ j
    simpa only [append_gaussianBlocks] using hh'
  have ht := (continuous_selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true))).tendsto
    (Matrix.mulVec u (x + σ • firstGaussianBlock g)) |>.comp hY
  simpa only [Function.comp_def, upperFaceSmoother_selectorWeight] using ht

/-- Each original-coordinate entry of the actual padded Gaussian matrix
converges to the corresponding original matrix entry. This is conditional on
every base point; no base moment, covariance gap, or distinct row is assumed.
-/
theorem logisticPaddedScore_upperLeft_entry_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) (j l : Fin r) :
    Tendsto (fun n => logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPaddedBase (m := m) (lam n) x) (Fin.castAdd m j) (Fin.castAdd m l)) atTop
      (𝓝 (logisticGaussianScore u a h σ α x j l)) := by
  let w (n : ℕ) (g : Vector (r + m)) :=
    logisticTupleWeight (logisticPaddedNormals u (lam n)) a h α
      (logisticPaddedBase (m := m) (lam n) x + σ • g)
  let w₀ (g : Vector r) := logisticTupleWeight u a h α (x + σ • g)
  have hw (n : ℕ) : Measurable (w n) :=
    ((continuous_logisticTupleWeight (logisticPaddedNormals u (lam n)) a h hh α).comp
      (continuous_const.add (continuous_const.smul continuous_id))).measurable
  have hw₀ : Measurable w₀ := ((continuous_logisticTupleWeight u a h hh α).comp
    (continuous_const.add (continuous_const.smul continuous_id))).measurable
  have hbound (n : ℕ) (g : Vector (r + m)) : |w n g| ≤ 1 :=
    logisticTupleWeight_abs_le_one _ a h hh α _
  have hlim (g : Vector (r + m)) : Tendsto (fun n => w n g) atTop (𝓝 (w₀ (firstGaussianBlock g))) :=
    logisticPaddedTupleWeight_tendsto u a h hh α lam hlam hlam0 hlam1 x g σ
  have ht := weightedScore_entry_tendsto_of_bounded_weights w (fun g => w₀ (firstGaussianBlock g))
    hw hbound hlim (Fin.castAdd m j) (Fin.castAdd m l)
  have he := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M j l)
    (weightedScore_firstGaussianBlock (s := m) w₀ hw₀)
  change weightedScore (standardGaussian (r + m)) id (fun g => w₀ (firstGaussianBlock g))
    (Fin.castAdd m j) (Fin.castAdd m l) = weightedScore (standardGaussian r) id w₀ j l at he
  rw [he] at ht
  exact ht

theorem logisticPaddedScore_upperLeft_nuclear_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) :
    Tendsto (fun n => symmetricNuclearNorm
      ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
        (logisticPaddedBase (m := m) (lam n) x)).submatrix (Fin.castAdd m) (Fin.castAdd m))) atTop
      (𝓝 (symmetricNuclearNorm (logisticGaussianScore u a h σ α x))) := by
  have hM : Tendsto (fun n => fun j l => logisticGaussianScore (logisticPaddedNormals u (lam n))
      a h σ α (logisticPaddedBase (m := m) (lam n) x) (Fin.castAdd m j) (Fin.castAdd m l)) atTop
      (𝓝 (fun j l => logisticGaussianScore u a h σ α x j l)) :=
    tendsto_pi_nhds.mpr (fun j => tendsto_pi_nhds.mpr (fun l =>
      logisticPaddedScore_upperLeft_entry_tendsto u a h hh α lam hlam hlam0 hlam1 x σ j l))
  have hc : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  exact (hc.tendsto _).comp hM

theorem logisticPaddedScore_upperLeft_nuclear_sum_tendsto {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x : Vector r) (σ : ℝ) :
    Tendsto (fun n => ∑ α : Fin k → Fin m, symmetricNuclearNorm
      ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
        (logisticPaddedBase (m := m) (lam n) x)).submatrix (Fin.castAdd m) (Fin.castAdd m))) atTop
      (𝓝 (∑ α : Fin k → Fin m, symmetricNuclearNorm (logisticGaussianScore u a h σ α x))) :=
  tendsto_finset_sum Finset.univ (fun (α : Fin k → Fin m) _ =>
    logisticPaddedScore_upperLeft_nuclear_tendsto u a h hh α lam hlam hlam0 hlam1 x σ)

end

end RectangleCLT.Companion.SplitV4
