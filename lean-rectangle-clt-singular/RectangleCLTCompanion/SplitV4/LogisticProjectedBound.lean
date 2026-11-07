import RectangleCLTCompanion.SplitV4.LogisticProjectedPadding
import RectangleCLTCompanion.SplitV4.LogisticMatrixPaper

open MeasureTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem integrable_projectedLogistic_nuclear_sum {m r k : ℕ}
    (μ : Measure (Vector m)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) :
    Integrable (fun v => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (projectedLogisticGaussianScore u a h hh σ α v)) μ := by
  have ha := integrable_selector_nuclear_sum (k := k) μ (upperFaceSmoother a h hh)
    (σ • u) id measurable_id
  apply ha.mono'
    (Finset.measurable_sum _ (fun α _ => measurable_selectorGaussianScore_nuclear
      (upperFaceSmoother a h hh) (σ • u) id measurable_id (fun i => (α i, true)))).aestronglyMeasurable
  exact ae_of_all _ (fun v => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
      (fun α _ => symmetricNuclearNorm_nonneg _))]
    exact sum_upper_tuples_le_all_faces
      (fun β : Fin k → Face m => symmetricNuclearNorm
        (selectorGaussianScore (upperFaceSmoother a h hh) (σ • u) id β v))
      (fun β => symmetricNuclearNorm_nonneg _))

/-- Genuine projected-base extension. The base face values are arbitrary;
in particular they need not belong to the range of the Gaussian factor.
The two displayed concentration inputs are actual scalar base-law bounds,
and will be discharged by the active-face rectangle pullback. -/
theorem projected_logistic_matrix_bound {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector m)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hσ : 0 < σ)
    (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ (1 : Matrix (Fin m) (Fin m) ℝ) C δ L)
    (ht : TransitionMassBound μ id h (4 * C * h * Real.sqrt L)) (k : ℕ) (hk : 1 ≤ k) :
    (∫ v, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (projectedLogisticGaussianScore u a h hh σ α v) ∂μ) ≤
        logisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [lam, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using ht
  have hlampos (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlam0 (n : ℕ) : 0 ≤ lam n := (hlampos n).le
  have hlamne (n : ℕ) : lam n ≠ 0 := (hlampos n).ne'
  have hlam1 (n : ℕ) : lam n < 1 := by
    dsimp [lam]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → Vector m → ℝ := fun n v => ∑ α : Fin k → Fin m, symmetricNuclearNorm
    ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPrivateBase (lam n) v)).submatrix (Fin.castAdd m) (Fin.castAdd m))
  let f₀ : Vector m → ℝ := fun v => ∑ α : Fin k → Fin m,
    symmetricNuclearNorm (projectedLogisticGaussianScore u a h hh σ α v)
  have hfi (n : ℕ) : Integrable (f n) μ := integrable_logistic_upperLeft_nuclear_sum μ
    (logisticPrivateBase (r := r) (lam n)) (measurable_logisticPrivateBase _) _ a hh σ
  have hf₀i : Integrable f₀ μ := integrable_projectedLogistic_nuclear_sum μ u a hh σ
  apply integral_nonnegative_limit_le_uniform_bound μ f f₀ hfi hf₀i
    (fun n v => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun v => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun v => logisticPrivateBase_nuclear_sum_tendsto u a hh lam hlam hlamne v σ)
  intro n
  let U := logisticPaddedNormals u (lam n)
  let X : Vector m → Vector (r + m) := logisticPrivateBase (lam n)
  let ν := μ.map X
  have hX : Measurable X := measurable_logisticPrivateBase _
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hU : ∀ j, vectorNormSq (U j) = 1 := logisticPaddedNormals_unit u hu (hlam0 n) (hlam1 n)
  have hi : LinearIndependent ℝ U := logisticPaddedNormals_linearIndependent u (hlamne n)
  have hcν : PolyhedralBaseConcentration ν U C δ L := logisticPrivateBase_concentrated μ u hc (hlamne n)
  have hmap : ν.map (Matrix.mulVec U) = μ := logisticPrivateBase_projected_law μ u (hlamne n)
  have htν : TransitionMassBound ν (Matrix.mulVec U) h (4 * C * h * Real.sqrt L) := by
    apply transitionMassBound_of_map ν (Matrix.mulVec U) (by fun_prop)
    rw [hmap]
    exact ht
  have hn := logistic_matrix_bound_unit_independent hm ν U a hU hi hC hδ hh hσ hL hscale hcν htν k hk
  have hn' : (∫ y, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y) ∂ν) ≤
        logisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
    exact (integral_mono (integrable_logistic_nuclear_sum ν id measurable_id U a hh σ)
      (integrable_selector_nuclear_sum ν (upperFaceSmoother a h hh) (σ • U) (Matrix.mulVec U) (by fun_prop))
      (fun y => logisticGaussianScore_nuclear_sum_le_upper_selector U a h hh σ y)).trans hn
  have hmNative : AEStronglyMeasurable (fun y : Vector (r + m) => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y)) ν := by
    simpa only [id_eq] using
      (integrable_logistic_nuclear_sum (k := k) ν id measurable_id U a hh σ).aestronglyMeasurable
  rw [integral_map hX.aemeasurable hmNative] at hn'
  exact (integral_mono (hfi n) (integrable_logistic_nuclear_sum μ X hX U a hh σ)
    (fun v => Finset.sum_le_sum (fun α _ => symmetricNuclearNorm_upperLeft_le _))).trans hn'

end

end RectangleCLT.Companion.SplitV4
