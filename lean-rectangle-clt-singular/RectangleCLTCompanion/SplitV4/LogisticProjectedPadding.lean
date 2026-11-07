import RectangleCLTCompanion.SplitV4.LogisticMatrixIntegrability
import RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound

/-! Private padding for an arbitrary face-valued base. No range condition
on a possibly singular Gaussian factor is imposed. -/

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def logisticPrivateBase {r m : ℕ} (lam : ℝ) (v : Vector m) : Vector (r + m) :=
  Fin.append 0 (lam⁻¹ • v)

@[fun_prop] theorem measurable_logisticPrivateBase {r m : ℕ} (lam : ℝ) :
    Measurable (logisticPrivateBase (r := r) (m := m) lam) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [logisticPrivateBase, Fin.append_left, Pi.zero_apply] using
      (measurable_const : Measurable (fun _ : Vector m => (0 : ℝ)))
  · simpa only [logisticPrivateBase, Fin.append_right, Pi.smul_apply, smul_eq_mul] using
      (show Measurable (fun v : Vector m => lam⁻¹ * v j) from by fun_prop)

theorem logisticPrivateBase_dot {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : lam ≠ 0) (v : Vector m) (j : Fin m) :
    faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v) = v j := by
  simp only [faceDot, logisticPaddedNormals, logisticPrivateBase, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, zero_add]
  simp [Pi.single_apply, hlam]

theorem logisticPrivateBase_projection {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : lam ≠ 0) (v : Vector m) :
    Matrix.mulVec (logisticPaddedNormals u lam) (logisticPrivateBase lam v) = v := by
  funext j
  exact logisticPrivateBase_dot u hlam v j

theorem logisticPrivateBase_projected_law {r m : ℕ}
    (μ : Measure (Vector m)) (u : Fin m → Vector r) {lam : ℝ} (hlam : lam ≠ 0) :
    (μ.map (logisticPrivateBase (r := r) lam)).map (Matrix.mulVec (logisticPaddedNormals u lam)) = μ := by
  rw [Measure.map_map (by fun_prop) (measurable_logisticPrivateBase lam)]
  have he : Matrix.mulVec (logisticPaddedNormals u lam) ∘ logisticPrivateBase lam = id := by
    funext v
    exact logisticPrivateBase_projection u hlam v
  rw [he, Measure.map_id]

theorem logisticPrivateBase_concentrated {r m : ℕ}
    (μ : Measure (Vector m)) [IsProbabilityMeasure μ] (u : Fin m → Vector r)
    {C δ L lam : ℝ} (hc : PolyhedralBaseConcentration μ
      (1 : Matrix (Fin m) (Fin m) ℝ) C δ L) (hlam : lam ≠ 0) :
    PolyhedralBaseConcentration (μ.map (logisticPrivateBase (r := r) lam))
      (logisticPaddedNormals u lam) C δ L := by
  intro a s hs
  have hS : MeasurableSet (gaussianPolyhedronLayer (logisticPaddedNormals u lam) a s) := by
    apply MeasurableSet.diff
    all_goals
      unfold facePolyhedron
      simp only [Set.setOf_forall]
      apply MeasurableSet.iInter
      intro j
      exact measurableSet_le (by unfold dotProduct; fun_prop) measurable_const
  rw [map_measureReal_apply (measurable_logisticPrivateBase lam) hS]
  have he : (logisticPrivateBase (r := r) lam) ⁻¹'
      gaussianPolyhedronLayer (logisticPaddedNormals u lam) a s =
        gaussianPolyhedronLayer (1 : Matrix (Fin m) (Fin m) ℝ) a s := by
    ext v
    simp only [gaussianPolyhedronLayer, Set.mem_preimage, Set.mem_diff, facePolyhedron, Set.mem_setOf_eq]
    change ((∀ j, faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v) ≤ a j + s) ∧
      ¬ (∀ j, faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v) ≤ a j - s)) ↔ _
    simp only [logisticPrivateBase_dot u hlam]
    simp only [dotProduct, Matrix.one_apply, ite_mul, one_mul, zero_mul,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [he]
  exact hc a s hs

def projectedLogisticGaussianScore {m r k : ℕ} (u : Fin m → Vector r) (a : Vector m)
    (h : ℝ) (hh : 0 < h) (σ : ℝ) (α : Fin k → Fin m) (v : Vector m) :
    Matrix (Fin r) (Fin r) ℝ :=
  selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) id (fun i => (α i, true)) v

theorem logisticPrivateBase_joint_projection {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : lam ≠ 0) (v : Vector m) (g : Vector (r + m)) (σ : ℝ) (j : Fin m) :
    faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v + σ • g) =
      v j + σ * logisticRegularizationScale lam * faceDot (u j) (firstGaussianBlock g) +
        σ * lam * secondGaussianBlock g j := by
  have he : faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v + σ • g) =
      faceDot (logisticPaddedNormals u lam j) (logisticPrivateBase lam v) +
        σ * faceDot (logisticPaddedNormals u lam j) g := by
    simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he, logisticPrivateBase_dot u hlam]
  rw [← append_gaussianBlocks g]
  simp only [faceDot, logisticPaddedNormals, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Pi.smul_apply, smul_eq_mul, firstGaussianBlock, secondGaussianBlock]
  simp only [Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  simp only [mul_assoc, ← Finset.mul_sum]
  ring

theorem logisticPrivateBase_weight_tendsto {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0)) (hlamne : ∀ n, lam n ≠ 0)
    (v : Vector m) (g : Vector (r + m)) (σ : ℝ) :
    Tendsto (fun n => logisticTupleWeight (logisticPaddedNormals u (lam n)) a h α
      (logisticPrivateBase (lam n) v + σ • g)) atTop
      (𝓝 (selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true))
        (Matrix.mulVec (σ • u) (firstGaussianBlock g) + v))) := by
  have hc := logisticRegularizationScale_tendsto hlam
  have hY : Tendsto (fun n => Matrix.mulVec (logisticPaddedNormals u (lam n))
      (logisticPrivateBase (lam n) v + σ • g)) atTop
      (𝓝 (Matrix.mulVec (σ • u) (firstGaussianBlock g) + v)) := by
    apply tendsto_pi_nhds.mpr
    intro j
    simp_rw [show ∀ n, Matrix.mulVec (logisticPaddedNormals u (lam n))
      (logisticPrivateBase (lam n) v + σ • g) j =
        v j + σ * logisticRegularizationScale (lam n) * faceDot (u j) (firstGaussianBlock g) +
          σ * lam n * secondGaussianBlock g j from
            fun n => logisticPrivateBase_joint_projection u (hlamne n) v g σ j]
    have ht : Tendsto (fun n => v j + σ * logisticRegularizationScale (lam n) *
        faceDot (u j) (firstGaussianBlock g) + σ * lam n * secondGaussianBlock g j) atTop
        (𝓝 (v j + σ * 1 * faceDot (u j) (firstGaussianBlock g) + σ * 0 * secondGaussianBlock g j)) :=
      (tendsto_const_nhds.add ((tendsto_const_nhds.mul hc).mul tendsto_const_nhds)).add
      ((tendsto_const_nhds.mul hlam).mul tendsto_const_nhds)
    have hp : Matrix.mulVec (σ • u) (firstGaussianBlock g) j =
        σ * faceDot (u j) (firstGaussianBlock g) := by
      simp only [Matrix.mulVec, dotProduct, faceDot, Pi.smul_apply, smul_eq_mul, mul_assoc,
        Finset.mul_sum]
    rw [Pi.add_apply, hp, add_comm (σ * faceDot (u j) (firstGaussianBlock g)) (v j)]
    simpa only [mul_one, mul_zero, zero_mul, add_zero] using ht
  have ht := ((continuous_selectorWeight (upperFaceSmoother a h hh)
    (fun i => (α i, true))).tendsto _).comp hY
  simpa only [Function.comp_def, upperFaceSmoother_selectorWeight] using ht

theorem logisticPrivateBase_score_entry_tendsto {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (α : Fin k → Fin m)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0)) (hlamne : ∀ n, lam n ≠ 0)
    (v : Vector m) (σ : ℝ) (j l : Fin r) :
    Tendsto (fun n => logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPrivateBase (lam n) v) (Fin.castAdd m j) (Fin.castAdd m l)) atTop
      (𝓝 (projectedLogisticGaussianScore u a h hh σ α v j l)) := by
  let w (n : ℕ) (g : Vector (r + m)) := logisticTupleWeight (logisticPaddedNormals u (lam n)) a h α
    (logisticPrivateBase (lam n) v + σ • g)
  let w₀ (g : Vector r) := selectorWeight (upperFaceSmoother a h hh) (fun i => (α i, true))
    (Matrix.mulVec (σ • u) g + v)
  have hw (n : ℕ) : Measurable (w n) :=
    ((continuous_logisticTupleWeight (logisticPaddedNormals u (lam n)) a h hh α).comp
      (continuous_const.add (continuous_const.smul continuous_id))).measurable
  have hw₀ : Measurable w₀ := ((continuous_selectorWeight (upperFaceSmoother a h hh)
    (fun i => (α i, true))).comp (by fun_prop)).measurable
  have hb (n : ℕ) (g : Vector (r + m)) : |w n g| ≤ 1 :=
    logisticTupleWeight_abs_le_one _ a h hh α _
  have ht := weightedScore_entry_tendsto_of_bounded_weights w (fun g => w₀ (firstGaussianBlock g))
    hw hb (fun g => logisticPrivateBase_weight_tendsto u a hh α lam hlam hlamne v g σ)
    (Fin.castAdd m j) (Fin.castAdd m l)
  have he := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M j l)
    (weightedScore_firstGaussianBlock (s := m) w₀ hw₀)
  change weightedScore (standardGaussian (r + m)) id (fun g => w₀ (firstGaussianBlock g))
    (Fin.castAdd m j) (Fin.castAdd m l) = weightedScore (standardGaussian r) id w₀ j l at he
  rw [he] at ht
  exact ht

theorem logisticPrivateBase_nuclear_sum_tendsto {r m k : ℕ} (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h)
    (lam : ℕ → ℝ) (hlam : Tendsto lam atTop (𝓝 0)) (hlamne : ∀ n, lam n ≠ 0)
    (v : Vector m) (σ : ℝ) :
    Tendsto (fun n => ∑ α : Fin k → Fin m, symmetricNuclearNorm
      ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
        (logisticPrivateBase (lam n) v)).submatrix (Fin.castAdd m) (Fin.castAdd m))) atTop
      (𝓝 (∑ α : Fin k → Fin m,
        symmetricNuclearNorm (projectedLogisticGaussianScore u a h hh σ α v))) := by
  apply tendsto_finset_sum
  intro α _
  have hM := tendsto_pi_nhds.mpr (fun j => tendsto_pi_nhds.mpr (fun l =>
    logisticPrivateBase_score_entry_tendsto u a hh α lam hlam hlamne v σ j l))
  have hc : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  exact (hc.tendsto _).comp hM

end

end RectangleCLT.Companion.SplitV4
