import RectangleCLTCompanion.FourthIdentityFreshPairs
import RectangleCLTCompanion.SupportRows

/-! The translated bases in the exact fourth-order identity are actual
small shifts of the full path, even after singular support reduction. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- Restore the deleted actual row and translate by the independent fresh
row used in an integral remainder. -/
def fourthRestorationShift {Ω : Type*} {r n : ℕ}
    (ζ : Fin n → Ω → Vector r) (mask : Kane.Cube n) (i : Fin n)
    (ω : Ω) (fresh : Vector r) (t s : ℝ) : Vector r :=
  (thinningScale t * s) • fresh -
    thinningScale t • (if mask i then ζ i ω else 0)

theorem leaveOne_line_eq_full_shift {Ω : Type*} {r n : ℕ}
    (ζ : Fin n → Ω → Vector r) (mask : Kane.Cube n) (i : Fin n)
    (ω : Ω) (x fresh : Vector r) (t s : ℝ) :
    FaceSmoother.line
      (x + thinningScale t • maskObservationSum ζ (Function.update mask i false) ω)
      fresh (thinningScale t * s) =
      (x + thinningScale t • maskObservationSum ζ mask ω) +
        fourthRestorationShift ζ mask i ω fresh t s := by
  rw [maskObservationSum_eq_leaveOne_add ζ mask i ω, smul_add]
  change (x + thinningScale t • maskObservationSum ζ (Function.update mask i false) ω) +
    (thinningScale t * s) • fresh = _
  unfold fourthRestorationShift
  abel

/-- The observable maximum-norm shift is at most `4δ`; no inverse singular
value or norm bound on a whitening operator is used. -/
theorem projected_fourthRestorationShift_le {Ω : Type*} {p r n : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (ζ : Fin n → Ω → Vector r)
    (mask : Kane.Cube n) (i : Fin n) (ω : Ω) (fresh : Vector r)
    {δ t s : ℝ} (hδ : 0 ≤ δ)
    (hactual : ‖A.mulVec (ζ i ω)‖ ≤ δ) (hfresh : ‖A.mulVec fresh‖ ≤ δ)
    (ht : 0 ≤ t) (ht1 : t ≤ 1) (hs : 0 ≤ s) (hs1 : s ≤ 1) :
    ‖A.mulVec (fourthRestorationShift ζ mask i ω fresh t s)‖ ≤ 4 * δ := by
  have ha : 0 ≤ thinningScale t := (thinningScale_pos ht).le
  have has : 0 ≤ thinningScale t * s := mul_nonneg ha hs
  have has2 : thinningScale t * s ≤ 2 :=
    (mul_le_mul_of_nonneg_left hs1 ha).trans (by simpa using thinningScale_le_two ht1)
  have hfirst : ‖(thinningScale t * s) • A.mulVec fresh‖ ≤ 2 * δ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg has]
    exact mul_le_mul has2 hfresh (norm_nonneg _) (by norm_num)
  have hsecond : ‖thinningScale t • A.mulVec (if mask i then ζ i ω else 0)‖ ≤ 2 * δ := by
    cases hm : mask i
    · simp only [hm, Bool.false_eq_true, ↓reduceIte, Matrix.mulVec_zero, smul_zero, norm_zero]
      positivity
    · simp only [hm, ↓reduceIte, norm_smul, Real.norm_eq_abs, abs_of_nonneg ha]
      exact mul_le_mul (thinningScale_le_two ht1) hactual (norm_nonneg _) (by norm_num)
  unfold fourthRestorationShift
  rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Matrix.mulVec_smul]
  exact (norm_sub_le _ _).trans ((add_le_add hfirst hsecond).trans (by ring_nf; rfl))

theorem fourthRestorationShift_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {r n : ℕ}
    (ζ : Fin n → Ω → Vector r) (hζ : ∀ i, Measurable (ζ i))
    (Z : Ξ → Vector r) (hZ : Measurable Z)
    (mask : Kane.Cube n) (i : Fin n) (t s : ℝ) :
    Measurable (fun y : Ω × Ξ => fourthRestorationShift ζ mask i y.1 (Z y.2) t s) := by
  unfold fourthRestorationShift
  apply (measurable_const.smul (hZ.comp measurable_snd)).sub
  apply measurable_const.smul
  cases hm : mask i
  · simpa only [hm, Bool.false_eq_true, ↓reduceIte] using
      (measurable_const : Measurable (fun _ : Ω × Ξ => (0 : Vector r)))
  · simpa only [hm, ↓reduceIte] using (hζ i).comp measurable_fst

end
end RectangleCLT.Companion
