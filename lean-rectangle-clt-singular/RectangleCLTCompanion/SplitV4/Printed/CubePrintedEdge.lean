import RectangleCLTCompanion.SplitV4.Printed.CubeRampGeometry

/-! The two displayed gradient estimates in the unique-maximizer part of
the printed proof of C.1. Both gradients are actual Fréchet derivatives;
the lower bound uses the printed edge/ramp and cube integration-by-parts
calculation, and the upper bound uses the normalized ramp in `[0,1]`. -/

open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem cube_coefficient_bound_pos {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) {b v : ℝ} (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    0 < b := by
  by_contra hb
  have hb : b ≤ 0 := le_of_not_gt hb
  have hz (i : Fin n) : B (0 : Fin m) i = 0 := by
    exact abs_eq_zero.mp (le_antisymm ((hcoeff _ i).trans hb) (abs_nonneg _))
  have hr := hrow (0 : Fin m)
  simp only [hz, zero_pow (by decide : 2 ≠ 0), Finset.sum_const_zero] at hr
  linarith

theorem CubeUniqueMax.gradient_radial_upper {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (c : ℝ) {H : ℝ} (hH : 0 < H) (x : Kane.Cube n) :
    cubeGradientRadial (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a) x ≤
      positiveLinearMaximum B x := by
  rw [hu.gradient_radial_eq]
  calc
    _ ≤ normalizedCubeRamp c H (affineCubeMaximum B a x) *
        positiveLinearMaximum B x :=
      mul_le_mul_of_nonneg_left (cubeLinear_le_positiveMaximum B x _)
        (normalizedCubeRamp_nonneg c hH _)
    _ ≤ 1 * positiveLinearMaximum B x :=
      mul_le_mul_of_nonneg_right (normalizedCubeRamp_le_one c hH _)
        (positiveLinearMaximum_nonneg B x)
    _ = _ := one_mul _

/-- The displayed lower gradient estimate, with `v = σ²`, `H = h+8b`
and `c=t-6b`. The boundary event is closed at both endpoints. -/
theorem CubeUniqueMax.avg_gradient_radial_lower {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (t h b v : ℝ) (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    (v / (h + 8 * b)) * Kane.avg (cubeBoundaryIndicator B a t h) ≤
      Kane.avg (cubeGradientRadial
        (cubeRampPrimitive (t - 6 * b) (h + 8 * b) ∘ realAffineCubeMaximum B a)) := by
  have hb := cube_coefficient_bound_pos B hv hcoeff hrow
  have hH : 0 < h + 8 * b := by positivity
  have hlower (x : Kane.Cube n) :
      v * cubeBoundaryIndicator B a t h x ≤
        ∑ i, affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i := by
    have hI : 0 ≤ cubeBoundaryIndicator B a t h x := by
      unfold cubeBoundaryIndicator
      split_ifs <;> norm_num
    calc
      _ ≤ (∑ i, (activeCubeSlope B a x i) ^ 2) * cubeBoundaryIndicator B a t h x :=
        mul_le_mul_of_nonneg_right (hrow (activeCubeBranch B a x)) hI
      _ = ∑ i, cubeBoundaryIndicator B a t h x * (activeCubeSlope B a x i) ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        cube_boundary_indicator_energy_le_flux B a t h b hb.le hcoeff x i)
  have hs : v * Kane.avg (cubeBoundaryIndicator B a t h) ≤
      Kane.avg (fun x => ∑ i, affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i) := by
    rw [← Kane.avg_const_mul]
    exact Kane.avg_mono hlower
  rw [hu.avg_gradient_radial_eq_flux]
  calc
    _ = (v * Kane.avg (cubeBoundaryIndicator B a t h)) / (h + 8 * b) := by ring
    _ ≤ _ := div_le_div_of_nonneg_right hs hH.le

theorem CubeUniqueMax.avg_gradient_radial_upper {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (c : ℝ) {H : ℝ} (hH : 0 < H) :
    Kane.avg (cubeGradientRadial (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a)) ≤
      intrinsicCubeMean B :=
  Kane.avg_mono (hu.gradient_radial_upper c hH)

end
end RectangleCLT.Companion.SplitV4.Printed
