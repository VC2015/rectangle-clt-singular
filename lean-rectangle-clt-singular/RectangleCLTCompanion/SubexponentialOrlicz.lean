import RectangleCLTCompanion.SubexponentialStatement
import RectangleCLTCompanion.SubexponentialClipping
import Mathlib.Order.ConditionallyCompleteLattice.Basic

/-! The manuscript's Orlicz infimum convention and its bridge to genuine
integrable exponential moments. The empty set of admissible scales has norm
`∞`, so totalized real infima and Bochner integrals cannot introduce a false
finite-tail hypothesis. A factor two avoids any endpoint-closedness premise. -/

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

universe u

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

/-- Positive scales with a genuine exponential moment at most two. -/
def psi1Scales {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : Set ℝ :=
  {t | 0 < t ∧ Integrable (fun ω => Real.exp (|X ω| / t)) μ ∧
    (∫ ω, Real.exp (|X ω| / t) ∂μ) ≤ 2}

/-- The manuscript's `ψ₁` infimum, with the usual value `∞` when no
admissible scale exists. For finite norm the real infimum is nonnegative. -/
def psi1Norm {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (X : Ω → ℝ) : ℝ≥0∞ := by
  classical
  exact if (psi1Scales μ X).Nonempty then
    ENNReal.ofReal (sInf (psi1Scales μ X)) else ∞

variable {Ω : Type u} [MeasurableSpace Ω] {μ : Measure Ω} {X : Ω → ℝ}

theorem psi1Scales_bddBelow (μ : Measure Ω) (X : Ω → ℝ) :
    BddBelow (psi1Scales μ X) :=
  ⟨0, fun _ ht => ht.1.le⟩

/-- Increasing a positive scale preserves admissibility, by pointwise
domination of both the exponential and its norm. -/
theorem psi1Scales_mono (hX : Measurable X) {s t : ℝ}
    (hs : s ∈ psi1Scales μ X) (hst : s ≤ t) : t ∈ psi1Scales μ X := by
  have ht : 0 < t := hs.1.trans_le hst
  have hpoint (ω : Ω) : Real.exp (|X ω| / t) ≤ Real.exp (|X ω| / s) := by
    exact Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (abs_nonneg _) hs.1 hst)
  have hm : Measurable (fun ω => Real.exp (|X ω| / t)) :=
    ((continuous_abs.measurable.comp hX).div_const t).exp
  have hi : Integrable (fun ω => Real.exp (|X ω| / t)) μ :=
    hs.2.1.mono' hm.aestronglyMeasurable (ae_of_all _ fun ω => by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)] using hpoint ω)
  exact ⟨ht, hi, (integral_mono hi hs.2.1 hpoint).trans hs.2.2⟩

theorem psi1Norm_eq_top_of_scales_empty
    (h : ¬(psi1Scales μ X).Nonempty) : psi1Norm μ X = ∞ := by
  simp only [psi1Norm, if_neg h]

/-- A finite upper bound on the Orlicz norm includes existence of an
admissible scale; the empty-infimum convention cannot satisfy this bound. -/
theorem psi1Norm_le_iff {K : ℝ} (hK : 0 ≤ K) :
    psi1Norm μ X ≤ ENNReal.ofReal K ↔
      (psi1Scales μ X).Nonempty ∧ sInf (psi1Scales μ X) ≤ K := by
  classical
  by_cases hs : (psi1Scales μ X).Nonempty
  · rw [psi1Norm, if_pos hs]
    simp only [ENNReal.ofReal_le_ofReal_iff hK, hs, true_and]
  · rw [psi1Norm, if_neg hs]
    constructor
    · intro hle
      exact False.elim ((not_le_of_gt ENNReal.ofReal_lt_top) hle)
    · rintro ⟨hne, _⟩
      exact False.elim (hs hne)

/-- A norm upper bound at `K` gives genuine exponential moments at `2K`.
The factor two permits an elementary infimum argument without assuming
attainment of the Orlicz infimum. -/
theorem two_mul_mem_psi1Scales_of_norm_le (hX : Measurable X) {K : ℝ}
    (hK : 0 < K) (hnorm : psi1Norm μ X ≤ ENNReal.ofReal K) :
    2 * K ∈ psi1Scales μ X := by
  obtain ⟨hne, hle⟩ := (psi1Norm_le_iff (μ := μ) (X := X) hK.le).mp hnorm
  have hlt : sInf (psi1Scales μ X) < 2 * K := hle.trans_lt (by linarith)
  obtain ⟨s, hs, hst⟩ :=
    (csInf_lt_iff (psi1Scales_bddBelow μ X) hne).mp hlt
  exact psi1Scales_mono hX hs hst.le

theorem ExponentialMomentBound.of_psi1Norm_le (hX : Measurable X) {K : ℝ}
    (hK : 0 < K) (hnorm : psi1Norm μ X ≤ ENNReal.ofReal K) :
    ExponentialMomentBound μ X (2 * K) := by
  obtain ⟨ht, hi, hb⟩ := two_mul_mem_psi1Scales_of_norm_le hX hK hnorm
  exact ⟨hX, ht, hi, hb⟩

/-- Independent centered observations under the exact infimum-based
Orlicz-norm hypothesis in the research manuscript. -/
structure Psi1IndependentHypotheses
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (X : Fin n → Ω → Vector p) (K : ℝ) : Prop where
  measurable : ∀ i, Measurable (X i)
  independent : iIndepFun X μ
  centered : ∀ i j, (∫ ω, X i ω j ∂μ) = 0
  psi1_le : ∀ i j, psi1Norm μ (fun ω => X i ω j) ≤ ENNReal.ofReal K
  one_le_scale : 1 ≤ K

/-- The Orlicz contract supplies the exponential-moment contract at twice
the stated tail scale. Absolute constants absorb this fixed factor. -/
theorem Psi1IndependentHypotheses.exponentialHypotheses
    {p n : ℕ} {Y : Fin n → Ω → Vector p} {K : ℝ}
    (h : Psi1IndependentHypotheses μ Y K) :
    SubexponentialIndependentHypotheses μ Y (2 * K) := by
  have hK : 0 < K := zero_lt_one.trans_le h.one_le_scale
  have hm (i : Fin n) (j : Fin p) : Measurable (fun ω => Y i ω j) :=
    (measurable_pi_apply j).comp (h.measurable i)
  have hs (i : Fin n) (j : Fin p) :=
    two_mul_mem_psi1Scales_of_norm_le (hm i j) hK (h.psi1_le i j)
  exact
    { measurable := h.measurable
      independent := h.independent
      centered := h.centered
      integrable_exp := fun i j => (hs i j).2.1
      exponential_moment := fun i j => (hs i j).2.2
      one_le_scale := by linarith [h.one_le_scale] }

end
end RectangleCLT.Companion
