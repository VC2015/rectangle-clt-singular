import RectangleCLTCompanion.LowerAtomObstruction

/-! Uniform consistency forces the normalized envelope to vanish. The
counterexample is the actual iid two-point array in every coordinate,
with identity covariance and an explicit positive atomic discrepancy. -/

open MeasureTheory Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

theorem pairGap_identity (p : ℕ) : pairGap (1 : Matrix (Fin p) (Fin p) ℝ) = 1 := by
  have hentry : ∀ jk : Fin p × Fin p,
      (if jk.1 = jk.2 then 0 else |(1 : Matrix (Fin p) (Fin p) ℝ) jk.1 jk.2|) = 0 := by
    intro jk
    by_cases hjk : jk.1 = jk.2 <;> simp [hjk, Matrix.one_apply]
  simp only [pairGap, maxOffDiagonal, hentry]
  have hf : (Finset.univ : Finset (Fin p × Fin p)).fold max (0 : ℝ) (fun _ => 0) = 0 :=
    le_antisymm ((Finset.fold_max_le _).mpr ⟨le_rfl, fun _ _ => le_rfl⟩)
      ((Finset.le_fold_max _).mpr (Or.inl le_rfl))
  rw [hf]
  norm_num

/-- No model class with a nonvanishing normalized envelope can have
uniform error below this fixed positive constant. The exhibited law
has identity covariance and therefore belongs to every gap class `c₀≤1`. -/
theorem not_fixedGapClassBound_of_envelope
    {c₀ B ε : ℝ} {p n : ℕ} (hc₀ : c₀ ≤ 1) (hB : 1 ≤ B)
    (hp : 1 ≤ p) (hn : 1 ≤ n) (hε : 0 < ε) (hδ : ε ≤ B / Real.sqrt n) :
    ¬ FixedGapClassBound.{0} c₀ B p n (Real.exp (-1 / ε ^ 2)) := by
  intro hclass
  let j : Fin p := ⟨0, by omega⟩
  have hcov := lowerNormalizedRows_covariance hB (p := p) hn
  have hunit : ∀ k, covariance (lowerArrayLaw B n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p))) k k = 1 := by
    intro k
    rw [hcov]
    simp
  have hgap : c₀ ≤ pairGap (covariance (lowerArrayLaw B n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p)))) := by
    rw [hcov, pairGap_identity]
    exact hc₀
  have hfactor : (1 : Matrix (Fin p) (Fin p) ℝ) *
      (1 : Matrix (Fin p) (Fin p) ℝ).transpose =
      covariance (lowerArrayLaw B n p)
        (sumVector (lowerNormalizedRows (n := n) (p := p))) := by
    rw [hcov]
    simp
  have hb := hclass (lowerArrayLaw B n p) lowerNormalizedRows 1
    (lowerNormalizedRows_boundedIndependent hB n p) hunit hgap hfactor
    (lowerCoordinateAtomRectangle j (lowerAllNegativeValue B n))
  have hlower := lower_atom_error_ge_of_envelope hB hn hε hδ j
  exact (not_lt_of_ge hlower) hb

/-- The first necessary condition in Theorem 5. The probability class is
the full fixed-gap class; the proof tests an explicit identity-covariance
member, with no distributional premise or lower-bound assumption. -/
theorem fixedGapUniformConsistency_envelope_tendsto_zero
    {c₀ : ℝ} {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hc₀ : c₀ ≤ 1) (hB : ∀ n, 2 ≤ B n) (hp : ∀ n, 1 ≤ p n)
    (hcons : FixedGapUniformConsistency.{0} c₀ B p) :
    Tendsto (fun n => B n / Real.sqrt (n : ℝ)) atTop (𝓝 0) := by
  apply tendsto_order.mpr
  constructor
  · intro a ha
    apply Filter.Eventually.of_forall
    intro n
    have hBn : 0 ≤ B n := by linarith only [hB n]
    exact ha.trans_le (div_nonneg hBn (Real.sqrt_nonneg _))
  · intro ε hε
    have hclass := hcons (Real.exp (-1 / ε ^ 2)) (Real.exp_pos _)
    filter_upwards [hclass, eventually_ge_atTop 1] with n hnclass hn
    by_contra hnot
    exact (not_fixedGapClassBound_of_envelope hc₀ (by linarith only [hB n])
      (hp n) hn hε (le_of_not_gt hnot)) hnclass

end

end RectangleCLT.Companion
