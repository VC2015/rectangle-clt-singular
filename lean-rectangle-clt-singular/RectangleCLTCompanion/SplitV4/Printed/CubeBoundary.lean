import RectangleCLTCompanion.SplitV4.Printed.CubePrintedEdge

/-! The printed proof of Lemma C.1: the unique-maximizer edge/ramp
calculation, followed by a generic threshold perturbation, enlarged closed
window and the radius-to-zero limit. The existing final C.1 theorem is not
used in this route. -/

open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

/-- The unique case has genuine derivatives at each vertex. The edge
calculation reuses the already checked pointwise ramp and discrete-IBP
identities, rather than the existing final boundary bound. -/
theorem cube_boundary_unique_case {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b v : ℝ)
    (hu : CubeUniqueMax B a) (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    (∀ x : Kane.Cube n, HasFDerivAt (realAffineCubeMaximum B a)
      (cubeLinearCLM (B (activeCubeBranch B a x))) (cubeVertex x)) ∧
    Kane.avg (cubeBoundaryIndicator B a t h) ≤
      (h + 8 * b) / v * intrinsicCubeMean B := by
  refine ⟨hu.hasFDerivAt_maximum, ?_⟩
  have hb := cube_coefficient_bound_pos B hv hcoeff hrow
  have hH : 0 < h + 8 * b := by positivity
  have hlower := hu.avg_gradient_radial_lower t h b v hh hv hcoeff hrow
  have hupper := hu.avg_gradient_radial_upper (t - 6 * b) hH
  have hbound := hlower.trans hupper
  calc
    _ = ((h + 8 * b) / v) *
        ((v / (h + 8 * b)) * Kane.avg (cubeBoundaryIndicator B a t h)) := by
      field_simp
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbound (div_nonneg hH.le hv.le)



/-- The full intrinsic bound by the perturbation/limit route printed in
C.1. The closed-window inclusion handles ties and atoms without an
unjustified continuity assertion about event indicators. -/
theorem intrinsic_cube_boundary_printed_avg {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b v : ℝ)
    (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    Kane.avg (cubeBoundaryIndicator B a t h) ≤
      (h + 8 * b) / v * intrinsicCubeMean B := by
  apply cube_boundary_bound_of_all_positive_radii
  intro ρ hρ
  obtain ⟨a', hnear, hu⟩ := exists_small_unique_threshold_perturbation B a hρ
  have havg := Kane.avg_mono
    (cube_boundary_indicator_le_perturbed B a a' t h ρ (fun α => (hnear α).le))
  have hb := (cube_boundary_unique_case B a' (t - ρ) (h + 2 * ρ) b v hu
    (by linarith) hv hcoeff hrow).2
  exact havg.trans hb

/-- The actual probability/expectation formulation of the printed C.1
argument, with the original coefficient matrix and exact intrinsic mean. -/
theorem intrinsic_cube_boundary_printed {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b v : ℝ)
    (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    (cubeUniformLaw n).real {x | t ≤ affineCubeMaximum B a x ∧
      affineCubeMaximum B a x ≤ t + h} ≤
      (h + 8 * b) / v * ∫ x, positiveLinearMaximum B x ∂cubeUniformLaw n := by
  rw [cubeUniformLaw_boundary_eq_avg, integral_cubeUniformLaw_eq_avg]
  exact intrinsic_cube_boundary_printed_avg B a t h b v hh hv hcoeff hrow

end
end RectangleCLT.Companion.SplitV4.Printed
