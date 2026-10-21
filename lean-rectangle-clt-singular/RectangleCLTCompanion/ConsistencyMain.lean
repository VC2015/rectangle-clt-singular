import RectangleCLTCompanion.GeneralConsistency
import RectangleCLTCompanion.ZeroSkewConsistency
import RectangleCLTCompanion.UniformWorstError

/-! Companion Theorem 5 with the literal supremum errors M_n and M_n^0.
Both necessity and sufficiency concern the entire class of laws. -/

open Filter
open scoped Topology

universe u

namespace RectangleCLT.Companion

noncomputable section

/-- The first assertion of Theorem 5, for arbitrary growing envelopes. -/
theorem fixedGapWorstError_iff_rate
    {c₀ : ℝ} {B : ℕ → ℝ} {p : ℕ → ℕ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1)
    (hB : ∀ n, 2 ≤ B n) (hp : ∀ n, 1 ≤ p n) :
    Tendsto (fun n => fixedGapWorstError.{u} c₀ (B n) (p n) n) atTop (𝓝 0) ↔
      Tendsto (fun n => B n * dimensionLog (p n) ^ (3/2 : ℝ) / Real.sqrt n)
        atTop (𝓝 0) := by
  have hh := (fixedGapWorstError_tendsto_zero_iff.{u} c₀ B p).trans
    (fixedGapUniformConsistency_iff hc₀ hc₁ hB hp)
  have heq : (fun n : ℕ => B n / Real.sqrt n * dimensionLog (p n) ^ (3/2 : ℝ)) =
      (fun n => B n * dimensionLog (p n) ^ (3/2 : ℝ) / Real.sqrt n) := by
    ext n
    ring
  rw [heq] at hh
  exact hh

/-- The second assertion of Theorem 5, for each fixed envelope B≥1. -/
theorem zeroSkewWorstError_iff_log_rate
    {c₀ B : ℝ} {p : ℕ → ℕ} (hc₀ : 0 < c₀) (hc₁ : c₀ ≤ 1) (hB : 1 ≤ B)
    (hp : ∀ n, 1 ≤ p n) :
    Tendsto (fun n => zeroSkewFixedGapWorstError.{u} c₀ B (p n) n) atTop (𝓝 0) ↔
      Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0) :=
  (zeroSkewFixedGapWorstError_tendsto_zero_iff.{u} c₀ B p).trans
    (zeroSkewFixedGapUniformConsistency_iff hc₀ hc₁ hB hp)

/-- The exact two conclusions of companion Theorem 5. The supremum is
formed before the asymptotic limit, and the probability model is unrestricted
within the manuscript's class. -/
def UniformConsistencyTheorem : Prop :=
  ∀ c₀ : ℝ, 0 < c₀ → c₀ ≤ 1 →
    (∀ (B : ℕ → ℝ) (p : ℕ → ℕ), (∀ n, 2 ≤ B n) → (∀ n, 1 ≤ p n) →
      (Tendsto (fun n => fixedGapWorstError.{u} c₀ (B n) (p n) n) atTop (𝓝 0) ↔
        Tendsto (fun n => B n * dimensionLog (p n) ^ (3/2 : ℝ) / Real.sqrt n)
          atTop (𝓝 0))) ∧
    (∀ (B : ℝ) (p : ℕ → ℕ), 1 ≤ B → (∀ n, 1 ≤ p n) →
      (Tendsto (fun n => zeroSkewFixedGapWorstError.{u} c₀ B (p n) n) atTop (𝓝 0) ↔
        Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 0)))

theorem uniformConsistencyTheorem : UniformConsistencyTheorem.{u} := by
  intro c₀ hc₀ hc₁
  exact ⟨fun B p hB hp => fixedGapWorstError_iff_rate hc₀ hc₁ hB hp,
    fun B p hB hp => zeroSkewWorstError_iff_log_rate hc₀ hc₁ hB hp⟩

end

end RectangleCLT.Companion
