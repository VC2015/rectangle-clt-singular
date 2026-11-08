import RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound
import RectangleCLTCompanion.SplitV4.Printed.MatrixSectorBound
import RectangleCLTCompanion.SplitV4.Printed.MatrixPaddingRoute

/-! The printed B.4 matrix estimate with its analytic threshold input
supplied by the separately checked full-sector and radial-tail route.
Earlier endpoints and their proof values remain unchanged. -/
open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
open SignedSurface

theorem sector_logistic_matrix_estimate {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [lam, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using ht
  have hlampos (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlam0 (n : ℕ) : 0 ≤ lam n := (hlampos n).le
  have hlam1 (n : ℕ) : lam n < 1 := by
    dsimp [lam]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → Vector r → ℝ := fun n x => ∑ α : Fin k → Fin m, symmetricNuclearNorm
    ((logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPaddedBase (m := m) (lam n) x)).submatrix (Fin.castAdd m) (Fin.castAdd m))
  let f₀ : Vector r → ℝ := fun x => ∑ α : Fin k → Fin m,
    symmetricNuclearNorm (logisticGaussianScore u a h σ α x)
  have hfi (n : ℕ) : Integrable (f n) μ := integrable_logistic_upperLeft_nuclear_sum μ
    (logisticPaddedBase (m := m) (lam n)) (measurable_logisticPaddedBase _) _ a hh σ
  have hf₀i : Integrable f₀ μ := integrable_logistic_nuclear_sum μ id measurable_id u a hh σ
  apply integral_nonnegative_limit_le_uniform_bound μ f f₀ hfi hf₀i
    (fun n x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => logisticPaddedScore_upperLeft_nuclear_sum_tendsto u a h hh lam hlam hlam0 hlam1 x σ)
  intro n
  let U := logisticPaddedNormals u (lam n)
  let X : Vector r → Vector (r + m) := logisticPaddedBase (m := m) (lam n)
  let ν := μ.map X
  have hX : Measurable X := measurable_logisticPaddedBase _
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hU : ∀ j, vectorNormSq (U j) = 1 := logisticPaddedNormals_unit u hu (hlam0 n) (hlam1 n)
  have hi : LinearIndependent ℝ U := logisticPaddedNormals_linearIndependent u (hlampos n).ne'
  have hcν : PolyhedralBaseConcentration ν U C δ L :=
    logisticPaddedBase_concentrated μ u hc (hlam0 n) (hlam1 n)
  have hmap : ν.map (Matrix.mulVec U) = μ.map (Matrix.mulVec u) := by
    rw [Measure.map_map (by fun_prop) hX]
    exact logisticPaddedBase_projected_law μ u (hlam0 n) (hlam1 n)
  have htm : TransitionMassBound (ν.map (Matrix.mulVec U)) id h
      (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
    rw [hmap]
    exact hc.transitionMassBound opposite hopp hh
  have htν : TransitionMassBound ν (Matrix.mulVec U) h (4 * C * h * Real.sqrt L) := by
    intro s hs z
    exact ((transitionMassBound_of_map ν (Matrix.mulVec U) (by fun_prop) htm) s hs z).trans
      (transition_budget_le_four hC.le hδh hh.le)
  have hn := sector_logistic_matrix_bound_unit_independent hm ν U a hU hi hC hδ hh hσ hL hscale hcν htν k hk
  have hnative : (∫ y, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y) ∂ν) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
    apply (integral_mono (integrable_logistic_nuclear_sum ν id measurable_id U a hh σ)
      (integrable_selector_nuclear_sum ν (upperFaceSmoother a h hh) (σ • U) (Matrix.mulVec U) (by fun_prop))
      (fun y => logisticGaussianScore_nuclear_sum_le_upper_selector U a h hh σ y)).trans hn
  have hmNative : AEStronglyMeasurable (fun y : Vector (r + m) => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y)) ν := by
    simpa only [id_eq] using
      (integrable_logistic_nuclear_sum (k := k) ν id measurable_id U a hh σ).aestronglyMeasurable
  rw [integral_map hX.aemeasurable hmNative] at hnative
  exact (integral_mono (hfi n)
    (integrable_logistic_nuclear_sum μ X hX U a hh σ)
    (fun x => Finset.sum_le_sum (fun α _ => symmetricNuclearNorm_upperLeft_le _))).trans hnative

theorem sector_logistic_matrix_estimate_rectangle {m r p : ℕ}
    (hm : 1 ≤ m) (hp : 1 ≤ p) (hmp : m ≤ 2 * p)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hscale : δ * Real.sqrt (dimensionLog p) ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ (dimensionLog p)) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C *
          (h * dimensionLog p * Real.sqrt (dimensionLog p)) :=
  sector_logistic_matrix_estimate hm μ u a hu opposite hopp hC hδ hh hδh hσ
    (threshold_dimensionLog_faces_le hm hp hmp) hscale hc k hk


/-- Identify the full limiting score with zero padding; this equality is
obtained from the actual entrywise DCT at the constant zero-padding sequence. -/
theorem fullPaddingLimitScore_eq_zero_padding {r m k : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (h : ℝ) (hh : 0 < h)
    (σ : ℝ) (α : Fin k → Fin m) (x : Vector r) :
    logisticGaussianScore (logisticPaddedNormals u 0) a h σ α (logisticPaddedBase (m := m) 0 x) =
      weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g)) := by
  ext j l
  have ht := logisticPaddedScore_full_entry_tendsto u a h hh α (fun _ : ℕ => 0)
    tendsto_const_nhds (fun _ => le_rfl) (fun _ => by norm_num) x σ j l
  exact tendsto_nhds_unique tendsto_const_nhds ht


theorem sector_logistic_matrix_full_padding_estimate {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g))) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
  let lam : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 2)
  have hlam : Tendsto lam atTop (𝓝 0) := by
    have ht := tendsto_one_div_add_atTop_nhds_zero_nat.comp (tendsto_add_atTop_nat 1)
    simpa only [lam, Function.comp_def, Nat.cast_add, Nat.cast_one, add_assoc,
      one_add_one_eq_two] using ht
  have hlampos (n : ℕ) : 0 < lam n := by dsimp [lam]; positivity
  have hlam0 (n : ℕ) : 0 ≤ lam n := (hlampos n).le
  have hlam1 (n : ℕ) : lam n < 1 := by
    dsimp [lam]
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 2)).mpr
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  let f : ℕ → Vector r → ℝ := fun n x => ∑ α : Fin k → Fin m, symmetricNuclearNorm
    (logisticGaussianScore (logisticPaddedNormals u (lam n)) a h σ α
      (logisticPaddedBase (m := m) (lam n) x))
  let f₀ : Vector r → ℝ := fun x => ∑ α : Fin k → Fin m,
    symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id
      (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g)))
  have hfi (n : ℕ) : Integrable (f n) μ := integrable_logistic_nuclear_sum μ
    (logisticPaddedBase (m := m) (lam n)) (measurable_logisticPaddedBase _) _ a hh σ
  have hf₀i : Integrable f₀ μ := by
    have hi := integrable_logistic_nuclear_sum (k := k) μ
      (logisticPaddedBase (m := m) 0) (measurable_logisticPaddedBase _) (logisticPaddedNormals u 0) a hh σ
    simpa only [f₀, fullPaddingLimitScore_eq_zero_padding u a h hh] using hi
  apply integral_nonnegative_limit_le_uniform_bound μ f f₀ hfi hf₀i
    (fun n x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => Finset.sum_nonneg (fun α _ => symmetricNuclearNorm_nonneg _))
    (fun x => logisticPaddedScore_full_nuclear_sum_tendsto u a h hh lam hlam hlam0 hlam1 x σ)
  intro n
  let U := logisticPaddedNormals u (lam n)
  let X : Vector r → Vector (r + m) := logisticPaddedBase (m := m) (lam n)
  let ν := μ.map X
  have hX : Measurable X := measurable_logisticPaddedBase _
  letI : IsProbabilityMeasure ν := isProbabilityMeasure_map hX.aemeasurable
  have hU : ∀ j, vectorNormSq (U j) = 1 := logisticPaddedNormals_unit u hu (hlam0 n) (hlam1 n)
  have hi : LinearIndependent ℝ U := logisticPaddedNormals_linearIndependent u (hlampos n).ne'
  have hcν : PolyhedralBaseConcentration ν U C δ L :=
    logisticPaddedBase_concentrated μ u hc (hlam0 n) (hlam1 n)
  have hmap : ν.map (Matrix.mulVec U) = μ.map (Matrix.mulVec u) := by
    rw [Measure.map_map (by fun_prop) hX]
    exact logisticPaddedBase_projected_law μ u (hlam0 n) (hlam1 n)
  have htm : TransitionMassBound (ν.map (Matrix.mulVec U)) id h
      (2 * (C * (h * Real.log 2 + δ) * Real.sqrt L)) := by
    rw [hmap]
    exact hc.transitionMassBound opposite hopp hh
  have htν : TransitionMassBound ν (Matrix.mulVec U) h (4 * C * h * Real.sqrt L) := by
    intro s hs z
    exact ((transitionMassBound_of_map ν (Matrix.mulVec U) (by fun_prop) htm) s hs z).trans
      (transition_budget_le_four hC.le hδh hh.le)
  have hn := sector_logistic_matrix_bound_unit_independent hm ν U a hU hi hC hδ hh hσ hL hscale hcν htν k hk
  have hnative : (∫ y, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y) ∂ν) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L) := by
    apply (integral_mono (integrable_logistic_nuclear_sum ν id measurable_id U a hh σ)
      (integrable_selector_nuclear_sum ν (upperFaceSmoother a h hh) (σ • U) (Matrix.mulVec U) (by fun_prop))
      (fun y => logisticGaussianScore_nuclear_sum_le_upper_selector U a h hh σ y)).trans hn
  have hmNative : AEStronglyMeasurable (fun y : Vector (r + m) => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore U a h σ α y)) ν := by
    simpa only [id_eq] using
      (integrable_logistic_nuclear_sum (k := k) ν id measurable_id U a hh σ).aestronglyMeasurable
  rw [integral_map hX.aemeasurable hmNative] at hnative
  exact hnative

/-- Fatou is applied to the full padded matrices before the original block is compressed. -/
theorem sector_logistic_matrix_estimate_full_first {m r : ℕ} (hm : 1 ≤ m)
    (μ : Measure (Vector r)) [IsProbabilityMeasure μ]
    (u : Fin m → Vector r) (a : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (opposite : Fin m → Fin m) (hopp : ∀ j, u (opposite j) = -u j)
    {C δ L h σ : ℝ} (hC : 0 < C) (hδ : 0 ≤ δ) (hh : 0 < h) (hδh : δ ≤ h)
    (hσ : 0 < σ) (hL : dimensionLog m ≤ 2 * L) (hscale : δ * Real.sqrt L ≤ σ)
    (hc : PolyhedralBaseConcentration μ u C δ L) (k : ℕ) (hk : 1 ≤ k) :
    (∫ x, ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α x) ∂μ) ≤
        sectorLogisticMatrixConstant ^ (k + 1) * C * (h * L * Real.sqrt L)  := by
  have hFull := sector_logistic_matrix_full_padding_estimate hm μ u a hu opposite hopp
    hC hδ hh hδh hσ hL hscale hc k hk
  have hOriginal := integrable_logistic_nuclear_sum (k := k) μ id measurable_id u a hh σ
  have hLimit : Integrable (fun x => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id
        (fun g => logisticTupleWeight u a h α (x + σ • firstGaussianBlock g)))) μ := by
    have hi := integrable_logistic_nuclear_sum (k := k) μ
      (logisticPaddedBase (m := m) 0) (measurable_logisticPaddedBase _) (logisticPaddedNormals u 0) a hh σ
    simpa only [fullPaddingLimitScore_eq_zero_padding u a h hh] using hi
  apply (integral_mono hOriginal hLimit (fun x => ?_)).trans hFull
  apply Finset.sum_le_sum
  intro α _
  let w : Vector r → ℝ := fun g => logisticTupleWeight u a h α (x + σ • g)
  have hw : Measurable w := ((continuous_logisticTupleWeight u a h hh α).comp
    (continuous_const.add (continuous_const.smul continuous_id))).measurable
  have he := weightedScore_firstGaussianBlock (s := m) w hw
  change symmetricNuclearNorm (weightedScore (standardGaussian r) id w) ≤
    symmetricNuclearNorm (weightedScore (standardGaussian (r + m)) id (fun g => w (firstGaussianBlock g)))
  rw [← he]
  exact symmetricNuclearNorm_upperLeft_le _

end
end RectangleCLT.Companion.SplitV4.Printed
