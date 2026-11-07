import RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
import RectangleCLTCompanion.SelectorConcentration

/-! Printed B.4: obtain the reference cap by sending all other thresholds
to infinity in the full logistic transition bound and applying dominated
convergence. The earlier singleton-smoother proof is retained. -/

open MeasureTheory Set Filter
open scoped Topology BigOperators

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- Keep the selected threshold fixed and increase every other threshold. -/
def oneFaceThresholds {m : ℕ} (a : Vector m) (j : Fin m) (t : ℝ) : Vector m :=
  fun l => a l + if l = j then 0 else t

/-- The actual full exponential sum converges to the selected-face term. -/
theorem oneFaceThresholds_exp_sum_tendsto {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (j : Fin m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) :
    Tendsto (fun t : ℝ => ∑ l, Real.exp ((faceDot (u l) x - oneFaceThresholds a j t l) / h))
      atTop (𝓝 (Real.exp ((faceDot (u j) x - a j) / h))) := by
  classical
  have hterm (l : Fin m) :
      Tendsto (fun t : ℝ => Real.exp ((faceDot (u l) x - oneFaceThresholds a j t l) / h))
        atTop (𝓝 (if l = j then Real.exp ((faceDot (u j) x - a j) / h) else 0)) := by
    by_cases hl : l = j
    · subst l
      simpa [oneFaceThresholds] using
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => Real.exp ((faceDot (u j) x - a j) / h))
          atTop (𝓝 (Real.exp ((faceDot (u j) x - a j) / h))))
    · have hlin : Tendsto (fun t : ℝ => (faceDot (u l) x - (a l + t)) / h) atTop atBot := by
        apply tendsto_atBot.2
        intro B
        filter_upwards [eventually_ge_atTop (faceDot (u l) x - a l - h * B)] with t ht
        apply (div_le_iff₀ hh).mpr
        linarith
      simpa only [oneFaceThresholds, if_neg hl] using Real.tendsto_exp_atBot.comp hlin
  simpa only [Finset.sum_ite_eq', Finset.mem_univ, if_true] using
    tendsto_finset_sum Finset.univ (fun l _ => hterm l)

/-- The actual full transition weight converges pointwise to the selected
single-face reference weight. -/
theorem oneFaceThresholds_transition_tendsto {m r : ℕ}
    (u : Fin m → Vector r) (a : Vector m) (j : Fin m) {h : ℝ} (hh : 0 < h)
    (x : Vector r) :
    Tendsto (fun t : ℝ =>
      (upperFaceSmoother (oneFaceThresholds a j t) h hh).F (Matrix.mulVec u x) *
      (upperFaceSmoother (oneFaceThresholds a j t) h hh).theta (Matrix.mulVec u x)) atTop
      (𝓝 (oneFaceReference (upperFaceSmoother a h hh) (j, true) (Matrix.mulVec u x))) := by
  have hT := oneFaceThresholds_exp_sum_tendsto u a j hh x
  have hF : Tendsto (fun t : ℝ => logisticNullWeight u (oneFaceThresholds a j t) h x)
      atTop (𝓝 (1 / (1 + Real.exp ((faceDot (u j) x - a j) / h)))) := by
    exact tendsto_const_nhds.div (tendsto_const_nhds.add hT) (by positivity)
  have htrans := hF.mul ((tendsto_const_nhds (x := (1 : ℝ))).sub hF)
  have he : (1 / (1 + Real.exp ((faceDot (u j) x - a j) / h))) *
      (1 - 1 / (1 + Real.exp ((faceDot (u j) x - a j) / h))) =
      oneFaceReference (upperFaceSmoother a h hh) (j, true) (Matrix.mulVec u x) := by
    simp only [oneFaceReference, upperFaceSmoother, FaceSmoother.faceScore,
      FaceSmoother.normalDot, Bool.true_eq, if_true, one_mul, Matrix.mulVec, dotProduct,
      faceDot]
    field_simp
    ring
  change Tendsto (fun t : ℝ =>
    (upperFaceSmoother (oneFaceThresholds a j t) h hh).F (Matrix.mulVec u x) *
      (1 - (upperFaceSmoother (oneFaceThresholds a j t) h hh).F (Matrix.mulVec u x))) _ _
  simpa only [upperFaceSmoother_F, he] using htrans

/-- The printed dominated-convergence argument establishes the one-face
cap from the full face-system caps, without invoking a singleton smoother.
`hcap` is exactly the incoming transition estimate printed in B.4. -/
theorem oneFaceReference_integral_le_via_threshold_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (u : Fin m → Vector r) (V : Ω → Vector r) (hV : Measurable V)
    (a : Vector m) (j : Fin m) {h M : ℝ} (hh : 0 < h)
    (hcap : ∀ c : Vector m,
      (∫ ω, (upperFaceSmoother c h hh).F (Matrix.mulVec u (V ω)) *
        (upperFaceSmoother c h hh).theta (Matrix.mulVec u (V ω)) ∂μ) ≤ M) :
    (∫ ω, oneFaceReference (upperFaceSmoother a h hh) (j, true)
      (Matrix.mulVec u (V ω)) ∂μ) ≤ M := by
  let H := fun t : ℝ => fun ω =>
    (upperFaceSmoother (oneFaceThresholds a j t) h hh).F (Matrix.mulVec u (V ω)) *
    (upperFaceSmoother (oneFaceThresholds a j t) h hh).theta (Matrix.mulVec u (V ω))
  have hW : Measurable (fun ω => Matrix.mulVec u (V ω)) := by fun_prop
  have hmeas (t : ℝ) : Measurable (H t) := by
    exact (((upperFaceSmoother (oneFaceThresholds a j t) h hh).continuous_F.measurable.comp hW).mul
      ((SignedSurface.continuous_smoother_theta _).measurable.comp hW))
  have hbound (t : ℝ) (ω : Ω) : ‖H t ω‖ ≤ 1 := by
    let s := upperFaceSmoother (oneFaceThresholds a j t) h hh
    have hF := s.F_pos (Matrix.mulVec u (V ω))
    have hθ := (s.weights (Matrix.mulVec u (V ω))).theta_nonneg
    have hθ₁ := (s.weights (Matrix.mulVec u (V ω))).theta_lt_one.le
    change 0 ≤ s.theta (Matrix.mulVec u (V ω)) at hθ
    change s.theta (Matrix.mulVec u (V ω)) ≤ 1 at hθ₁
    change ‖s.F _ * s.theta _‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hF.le hθ)]
    exact mul_le_one₀ (s.F_le_one _) hθ hθ₁
  have hlim := tendsto_integral_filter_of_dominated_convergence
    (μ := μ) (F := H)
    (f := fun ω => oneFaceReference (upperFaceSmoother a h hh) (j, true) (Matrix.mulVec u (V ω)))
    (fun _ => (1 : ℝ))
    (Eventually.of_forall (fun t => (hmeas t).aestronglyMeasurable))
    (Eventually.of_forall (fun t => ae_of_all _ (hbound t))) (integrable_const _)
    (ae_of_all _ (fun ω => oneFaceThresholds_transition_tendsto u a j hh (V ω)))
  exact le_of_tendsto hlim (Eventually.of_forall (fun t => hcap (oneFaceThresholds a j t)))

/-- The actual transition-mass hypothesis supplies every full-threshold cap;
the conclusion is obtained through the newly verified printed limiting route. -/
theorem TransitionMassBound.oneFace_via_threshold_limit
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m r : ℕ} (u : Fin m → Vector r) (V : Ω → Vector r) (hV : Measurable V)
    {h M : ℝ} (hbound : TransitionMassBound μ (fun ω => Matrix.mulVec u (V ω)) h M)
    (a : Vector m) (j : Fin m) (hh : 0 < h) :
    (∫ ω, oneFaceReference (upperFaceSmoother a h hh) (j, true)
      (Matrix.mulVec u (V ω)) ∂μ) ≤ M := by
  apply oneFaceReference_integral_le_via_threshold_limit μ u V hV a j hh
  intro c
  simpa only [add_zero] using hbound (upperFaceSmoother c h hh) rfl 0

end
end RectangleCLT.Companion.SplitV4.Printed
