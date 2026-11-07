import RectangleCLTCompanion.SplitV4.LogisticPaddingLimits

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem measurable_logisticGaussianScore_entry
    {Ω : Type*} [MeasurableSpace Ω] {m r k : ℕ}
    (V : Ω → Vector r) (hV : Measurable V) (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) (α : Fin k → Fin m) (j l : Fin r) :
    Measurable (fun ω => logisticGaussianScore u a h σ α (V ω) j l) := by
  have he (ω : Ω) : logisticGaussianScore u a h σ α (V ω) =
      selectorGaussianScore (upperFaceSmoother a h hh) (σ • u)
        (fun ω => Matrix.mulVec u (V ω)) (fun i => (α i, true)) ω :=
    logisticGaussianScore_eq_upper_selector u a h hh σ α (V ω)
  simp_rw [he]
  exact measurable_selectorGaussianScore_entry _ _ _ (by fun_prop) _ j l

theorem measurable_logisticGaussianScore_nuclear
    {Ω : Type*} [MeasurableSpace Ω] {m r k : ℕ}
    (V : Ω → Vector r) (hV : Measurable V) (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) (α : Fin k → Fin m) :
    Measurable (fun ω => symmetricNuclearNorm (logisticGaussianScore u a h σ α (V ω))) := by
  have hc : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  exact hc.measurable.comp (measurable_pi_lambda _ (fun j => measurable_pi_lambda _
    (fun l => measurable_logisticGaussianScore_entry V hV u a hh σ α j l)))

theorem integrable_logistic_nuclear_sum
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {m r k : ℕ}
    (V : Ω → Vector r) (hV : Measurable V) (u : Fin m → Vector r)
    (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) :
    Integrable (fun ω => ∑ α : Fin k → Fin m,
      symmetricNuclearNorm (logisticGaussianScore u a h σ α (V ω))) ν := by
  have hAll := integrable_selector_nuclear_sum (k := k) ν (upperFaceSmoother a h hh)
    (σ • u) (fun ω => Matrix.mulVec u (V ω)) (by fun_prop)
  apply hAll.mono'
    (Finset.measurable_sum _ (fun α _ => measurable_logisticGaussianScore_nuclear V hV u a hh σ α)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
      (fun α _ => symmetricNuclearNorm_nonneg _))]
    exact logisticGaussianScore_nuclear_sum_le_upper_selector u a h hh σ (V ω))

theorem measurable_logisticGaussianScore_upperLeft_nuclear
    {Ω : Type*} [MeasurableSpace Ω] {m r s k : ℕ}
    (V : Ω → Vector (r + s)) (hV : Measurable V) (u : Fin m → Vector (r + s))
    (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) (α : Fin k → Fin m) :
    Measurable (fun ω => symmetricNuclearNorm
      ((logisticGaussianScore u a h σ α (V ω)).submatrix (Fin.castAdd s) (Fin.castAdd s))) := by
  have hc : Continuous (fun M : Fin r → Fin r → ℝ => symmetricNuclearNorm M) :=
    continuous_symmetricNuclearNorm
  exact hc.measurable.comp (measurable_pi_lambda _ (fun j => measurable_pi_lambda _
    (fun l => measurable_logisticGaussianScore_entry V hV u a hh σ α (Fin.castAdd s j) (Fin.castAdd s l))))

theorem integrable_logistic_upperLeft_nuclear_sum
    {Ω : Type*} [MeasurableSpace Ω] (ν : Measure Ω) [IsProbabilityMeasure ν] {m r s k : ℕ}
    (V : Ω → Vector (r + s)) (hV : Measurable V) (u : Fin m → Vector (r + s))
    (a : Vector m) {h : ℝ} (hh : 0 < h) (σ : ℝ) :
    Integrable (fun ω => ∑ α : Fin k → Fin m, symmetricNuclearNorm
      ((logisticGaussianScore u a h σ α (V ω)).submatrix (Fin.castAdd s) (Fin.castAdd s))) ν := by
  apply (integrable_logistic_nuclear_sum ν V hV u a hh σ).mono'
    (Finset.measurable_sum _ (fun α _ =>
      measurable_logisticGaussianScore_upperLeft_nuclear V hV u a hh σ α)).aestronglyMeasurable
  exact ae_of_all _ (fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg
      (fun α _ => symmetricNuclearNorm_nonneg _))]
    exact Finset.sum_le_sum (fun α _ => symmetricNuclearNorm_upperLeft_le _))

end

end RectangleCLT.Companion.SplitV4
