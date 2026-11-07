import RectangleCLTCompanion.SplitV4.ConcentratedBasePullback
import Mathlib.LinearAlgebra.LinearIndependent.Basic

/-! The actual padded-normal geometry used to remove linear-independence
restrictions in Appendix B.4. Its projected base is exactly the original
base, so signed-subsystem concentration pulls back without a new hypothesis
on the padded family.
-/

open MeasureTheory
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def logisticRegularizationScale (lam : ℝ) : ℝ := Real.sqrt (1 - lam ^ 2)

def logisticPaddedNormals {r m : ℕ} (u : Fin m → Vector r) (lam : ℝ) (j : Fin m) : Vector (r + m) :=
  Fin.append (logisticRegularizationScale lam • u j) (Pi.single j lam)

def logisticPaddedBase {r m : ℕ} (lam : ℝ) (x : Vector r) : Vector (r + m) :=
  Fin.append ((logisticRegularizationScale lam)⁻¹ • x) 0

theorem logisticRegularizationScale_pos {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    0 < logisticRegularizationScale lam := by
  apply Real.sqrt_pos.mpr
  nlinarith

theorem logisticPaddedNormals_unit {r m : ℕ} (u : Fin m → Vector r)
    (hu : ∀ j, vectorNormSq (u j) = 1) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) (j : Fin m) :
    vectorNormSq (logisticPaddedNormals u lam j) = 1 := by
  have hc : (logisticRegularizationScale lam) ^ 2 = 1 - lam ^ 2 := Real.sq_sqrt (by nlinarith)
  have hl : (∑ i : Fin r, (logisticRegularizationScale lam * u j i) ^ 2) =
      (logisticRegularizationScale lam) ^ 2 * vectorNormSq (u j) := by
    simp only [mul_pow, vectorNormSq, Finset.mul_sum]
  simp only [logisticPaddedNormals, vectorNormSq, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Pi.smul_apply, smul_eq_mul]
  rw [hl, hu, mul_one, hc]
  simp [Pi.single_apply, ite_pow]

/-- The private coordinate `lam e_j` gives actual linear independence for
every positive padding parameter, without an assumption on original rows. -/
theorem logisticPaddedNormals_linearIndependent {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : lam ≠ 0) : LinearIndependent ℝ (logisticPaddedNormals u lam) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc j
  have he := congrArg (fun x : Vector (r + m) => x (Fin.natAdd r j)) hc
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    logisticPaddedNormals, Fin.append_right] at he
  simp [Pi.single_apply] at he
  exact he.resolve_right hlam

theorem logisticPaddedNormals_base_dot {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) (x : Vector r) (j : Fin m) :
    faceDot (logisticPaddedNormals u lam j) (logisticPaddedBase (m := m) lam x) = faceDot (u j) x := by
  have hc := (logisticRegularizationScale_pos hlam hlam1).ne'
  simp only [faceDot, logisticPaddedNormals, logisticPaddedBase, Fin.sum_univ_add,
    Fin.append_left, Fin.append_right, Pi.smul_apply, smul_eq_mul, Pi.zero_apply,
    mul_zero, Finset.sum_const_zero, add_zero]
  exact Finset.sum_congr rfl (fun i _ => by field_simp [hc]; ring)

theorem logisticPaddedNormals_projected_base {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) (x : Vector r) :
    Matrix.mulVec (logisticPaddedNormals u lam) (logisticPaddedBase (m := m) lam x) = Matrix.mulVec u x := by
  funext j
  exact logisticPaddedNormals_base_dot u hlam hlam1 x j

theorem logisticPaddedNormals_joint_projection {r m : ℕ} (u : Fin m → Vector r)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) (x g : Vector r) (g' : Vector m)
    (σ : ℝ) (j : Fin m) :
    faceDot (logisticPaddedNormals u lam j)
      (logisticPaddedBase (m := m) lam x + σ • Fin.append g g') =
      faceDot (u j) x + σ * logisticRegularizationScale lam * faceDot (u j) g + σ * lam * g' j := by
  have hb := logisticPaddedNormals_base_dot u hlam hlam1 x j
  have he : faceDot (logisticPaddedNormals u lam j)
      (logisticPaddedBase (m := m) lam x + σ • Fin.append g g') =
      faceDot (logisticPaddedNormals u lam j) (logisticPaddedBase (m := m) lam x) +
        σ * faceDot (logisticPaddedNormals u lam j) (Fin.append g g') := by
    simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he, hb]
  simp only [faceDot, logisticPaddedNormals, Fin.sum_univ_add, Fin.append_left,
    Fin.append_right, Pi.smul_apply, smul_eq_mul]
  simp [Pi.single_apply, Finset.mul_sum, mul_assoc, mul_add]
  <;> ring

/-- The entire projected padded-base law is unchanged. The new normals
need not occur in opposite pairs; all signed subsystems are inherited by
pullback from the original opposite-pair family. -/
theorem logisticPaddedBase_projected_law {r m : ℕ} (μ : Measure (Vector r))
    (u : Fin m → Vector r) {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    μ.map (fun x => Matrix.mulVec (logisticPaddedNormals u lam) (logisticPaddedBase (m := m) lam x)) =
      μ.map (Matrix.mulVec u) := by
  congr 1
  exact funext (logisticPaddedNormals_projected_base u hlam hlam1)

theorem measurable_logisticPaddedBase {r m : ℕ} (lam : ℝ) :
    Measurable (logisticPaddedBase (r := r) (m := m) lam) := by
  apply measurable_pi_lambda
  intro j
  refine Fin.addCases (fun j => ?_) (fun j => ?_) j
  · simpa only [logisticPaddedBase, Fin.append_left, Pi.smul_apply, smul_eq_mul] using
      measurable_const.mul (measurable_pi_apply j)
  · simpa only [logisticPaddedBase, Fin.append_right, Pi.zero_apply] using
      (measurable_const : Measurable (fun _ : Vector r => (0 : ℝ)))

/-- The actual ambient padded-base law satisfies the original upper-face
concentration assumption with exactly the same numerical parameters. This
is directly usable by the linearly independent B.5 threshold theorem. -/
theorem logisticPaddedBase_concentrated {r m : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ] (u : Fin m → Vector r)
    {C δ L : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    PolyhedralBaseConcentration (μ.map (logisticPaddedBase (m := m) lam))
      (logisticPaddedNormals u lam) C δ L := by
  intro a s hs
  have hm := measurable_logisticPaddedBase (r := r) (m := m) lam
  have hp (b : Vector m) : MeasurableSet (facePolyhedron (logisticPaddedNormals u lam) b) := by
    unfold facePolyhedron
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le (by unfold dotProduct; fun_prop) measurable_const
  have hS : MeasurableSet (gaussianPolyhedronLayer (logisticPaddedNormals u lam) a s) :=
    (hp _).diff (hp _)
  rw [map_measureReal_apply hm hS]
  have he : (logisticPaddedBase (m := m) lam) ⁻¹'
      gaussianPolyhedronLayer (logisticPaddedNormals u lam) a s = gaussianPolyhedronLayer u a s := by
    ext x
    simp only [gaussianPolyhedronLayer, Set.mem_preimage, Set.mem_diff, facePolyhedron, Set.mem_setOf_eq]
    change ((∀ j, faceDot (logisticPaddedNormals u lam j) (logisticPaddedBase lam x) ≤ a j + s) ∧
      ¬ (∀ j, faceDot (logisticPaddedNormals u lam j) (logisticPaddedBase lam x) ≤ a j - s)) ↔ _
    simp only [logisticPaddedNormals_base_dot u hlam hlam1]
    rfl
  rw [he]
  exact hc a s hs

theorem logisticPaddedBase_transitionMassBound {r m : ℕ}
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ] (u : Fin m → Vector r)
    {C δ L h : ℝ} (hc : PolyhedralBaseConcentration μ u C δ L)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j) (hh : 0 < h)
    {lam : ℝ} (hlam : 0 ≤ lam) (hlam1 : lam < 1) :
    TransitionMassBound
      (μ.map (fun x => Matrix.mulVec (logisticPaddedNormals u lam) (logisticPaddedBase (m := m) lam x)))
      id h (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
  rw [logisticPaddedBase_projected_law μ u hlam hlam1]
  exact hc.transitionMassBound opposite hopp hh

theorem continuous_logisticRegularizationScale : Continuous logisticRegularizationScale := by
  unfold logisticRegularizationScale
  fun_prop

theorem logisticRegularizationScale_tendsto {lam : ℕ → ℝ}
    (hlam : Filter.Tendsto lam Filter.atTop (𝓝 0)) :
    Filter.Tendsto (fun n => logisticRegularizationScale (lam n)) Filter.atTop (𝓝 1) := by
  simpa only [logisticRegularizationScale, zero_pow (by norm_num : 2 ≠ 0), sub_zero,
    Real.sqrt_one] using (continuous_logisticRegularizationScale.tendsto 0).comp hlam

/-- The concrete perturbed projections converge to the original Gaussian
projections for every base point and every Gaussian sample. -/
theorem logisticPaddedNormals_joint_projection_tendsto {r m : ℕ} (u : Fin m → Vector r)
    (lam : ℕ → ℝ) (hlam : Filter.Tendsto lam Filter.atTop (𝓝 0))
    (hlam0 : ∀ n, 0 ≤ lam n) (hlam1 : ∀ n, lam n < 1)
    (x g : Vector r) (g' : Vector m) (σ : ℝ) (j : Fin m) :
    Filter.Tendsto (fun n => faceDot (logisticPaddedNormals u (lam n) j)
      (logisticPaddedBase (m := m) (lam n) x + σ • Fin.append g g'))
      Filter.atTop (𝓝 (faceDot (u j) (x + σ • g))) := by
  have hc := logisticRegularizationScale_tendsto hlam
  have hconst : Filter.Tendsto (fun _n : ℕ => faceDot (u j) x) Filter.atTop
      (𝓝 (faceDot (u j) x)) := tendsto_const_nhds
  have hh := (hconst.add ((hc.const_mul σ).mul_const (faceDot (u j) g))).add
    ((hlam.const_mul σ).mul_const (g' j))
  have he : faceDot (u j) (x + σ • g) = faceDot (u j) x + σ * faceDot (u j) g := by
    simp only [faceDot, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.sum_add_distrib, Finset.mul_sum]
    congr 1
    exact Finset.sum_congr rfl (fun i _ => by ring)
  rw [he]
  simpa only [logisticPaddedNormals_joint_projection u (hlam0 _) (hlam1 _),
    mul_one, mul_zero, zero_mul, add_zero] using hh

end

end RectangleCLT.Companion.SplitV4
