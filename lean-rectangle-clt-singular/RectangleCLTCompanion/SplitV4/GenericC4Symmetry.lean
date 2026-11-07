import RectangleCLTCompanion.SplitV4.GenericC4Taylor

/-! Slot symmetry of the genuine fourth derivative under C4 regularity.
This proves that reversed currying conventions give the ordinary tensor. -/

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option maxRecDepth 4096
set_option synthInstance.maxSize 10000
set_option maxSynthPendingDepth 16

private theorem canonical_third_right {p : ℕ} (F : Vector p → ℝ) (x a b c : Vector p) :
    iteratedFDeriv ℝ 3 F x ![a,b,c] =
      fderiv ℝ (fderiv ℝ (fderiv ℝ F)) x a b c := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

private theorem canonical_fourth_right {p : ℕ} (F : Vector p → ℝ) (x a b c d : Vector p) :
    iteratedFDeriv ℝ 4 F x ![a,b,c,d] =
      fderiv ℝ (fderiv ℝ (fderiv ℝ (fderiv ℝ F))) x a b c d := by
  rw [iteratedFDeriv_succ_apply_right, iteratedFDeriv_succ_apply_right, iteratedFDeriv_two_apply]
  rfl

theorem canonical_second_swap {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b : Vector p) : iteratedFDeriv ℝ 2 F x ![a,b] = iteratedFDeriv ℝ 2 F x ![b,a] := by
  rw [iteratedFDeriv_two_apply, iteratedFDeriv_two_apply]
  exact hF.contDiffAt.isSymmSndFDerivAt (by norm_num [minSmoothness] <;> decide) a b

theorem canonical_third_swap_first {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c : Vector p) : iteratedFDeriv ℝ 3 F x ![a,b,c] = iteratedFDeriv ℝ 3 F x ![b,a,c] := by
  rw [canonical_third_right, canonical_third_right]
  have hD : ContDiff ℝ 3 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hh := (hD.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num [minSmoothness] <;> decide) a b
  exact congrArg (fun L => L c) hh

theorem canonical_third_swap_last {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c : Vector p) : iteratedFDeriv ℝ 3 F x ![a,b,c] = iteratedFDeriv ℝ 3 F x ![a,c,b] := by
  have h₁ := hasDerivAt_iteratedFDeriv_segment hF (k := 2) (by decide) x a ![b,c] 1 0
  have h₂ := hasDerivAt_iteratedFDeriv_segment hF (k := 2) (by decide) x a ![c,b] 1 0
  simp only [one_mul, mul_zero, zero_smul, add_zero] at h₁ h₂
  have he : (fun t : ℝ => iteratedFDeriv ℝ 2 F (x+t • a) ![b,c]) =
      fun t => iteratedFDeriv ℝ 2 F (x+t • a) ![c,b] :=
    funext (fun t => canonical_second_swap hF (x+t • a) b c)
  rw [he] at h₁
  exact h₁.unique h₂

theorem canonical_fourth_swap_first {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c d : Vector p) : iteratedFDeriv ℝ 4 F x ![a,b,c,d] = iteratedFDeriv ℝ 4 F x ![b,a,c,d] := by
  rw [canonical_fourth_right, canonical_fourth_right]
  have hD : ContDiff ℝ 3 (fderiv ℝ F) := hF.fderiv_right (by norm_num)
  have hD₂ : ContDiff ℝ 2 (fderiv ℝ (fderiv ℝ F)) := hD.fderiv_right (by norm_num)
  have hh := (hD₂.contDiffAt (x := x)).isSymmSndFDerivAt (by norm_num [minSmoothness] <;> decide) a b
  exact congrArg (fun L => L c d) hh

theorem canonical_fourth_swap_middle {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c d : Vector p) : iteratedFDeriv ℝ 4 F x ![a,b,c,d] = iteratedFDeriv ℝ 4 F x ![a,c,b,d] := by
  have h₁ := hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x a ![b,c,d] 1 0
  have h₂ := hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x a ![c,b,d] 1 0
  simp only [one_mul, mul_zero, zero_smul, add_zero] at h₁ h₂
  have he : (fun t : ℝ => iteratedFDeriv ℝ 3 F (x+t • a) ![b,c,d]) =
      fun t => iteratedFDeriv ℝ 3 F (x+t • a) ![c,b,d] :=
    funext (fun t => canonical_third_swap_first hF (x+t • a) b c d)
  rw [he] at h₁
  exact h₁.unique h₂

theorem canonical_fourth_swap_last {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c d : Vector p) : iteratedFDeriv ℝ 4 F x ![a,b,c,d] = iteratedFDeriv ℝ 4 F x ![a,b,d,c] := by
  have h₁ := hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x a ![b,c,d] 1 0
  have h₂ := hasDerivAt_iteratedFDeriv_segment hF (k := 3) (by decide) x a ![b,d,c] 1 0
  simp only [one_mul, mul_zero, zero_smul, add_zero] at h₁ h₂
  have he : (fun t : ℝ => iteratedFDeriv ℝ 3 F (x+t • a) ![b,c,d]) =
      fun t => iteratedFDeriv ℝ 3 F (x+t • a) ![b,d,c] :=
    funext (fun t => canonical_third_swap_last hF (x+t • a) b c d)
  rw [he] at h₁
  exact h₁.unique h₂

/-- Exact equivalence of the two fourth-jet currying orders. -/
theorem canonical_fourth_reverse {p : ℕ} {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F)
    (x a b c d : Vector p) : iteratedFDeriv ℝ 4 F x ![a,b,c,d] = iteratedFDeriv ℝ 4 F x ![d,c,b,a] := by
  calc
    _ = iteratedFDeriv ℝ 4 F x ![b,a,c,d] := canonical_fourth_swap_first hF x a b c d
    _ = iteratedFDeriv ℝ 4 F x ![b,c,a,d] := canonical_fourth_swap_middle hF x b a c d
    _ = iteratedFDeriv ℝ 4 F x ![b,c,d,a] := canonical_fourth_swap_last hF x b c a d
    _ = iteratedFDeriv ℝ 4 F x ![c,b,d,a] := canonical_fourth_swap_first hF x b c d a
    _ = iteratedFDeriv ℝ 4 F x ![c,d,b,a] := canonical_fourth_swap_middle hF x c b d a
    _ = iteratedFDeriv ℝ 4 F x ![d,c,b,a] := canonical_fourth_swap_first hF x c d b a

end
end RectangleCLT.Companion.SplitV4
