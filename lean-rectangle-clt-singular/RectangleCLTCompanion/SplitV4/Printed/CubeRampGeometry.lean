import RectangleCLTCompanion.SplitV4.Printed.CubeGeometry
import Mathlib.Analysis.Convex.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus

/-! The normalized ramp, its genuine antiderivative, and the convex
composition appearing in the printed unique-maximizer proof of C.1. -/

open MeasureTheory Set
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def normalizedCubeRamp (c H x : ℝ) : ℝ := cubeRamp c H x / H

theorem continuous_normalizedCubeRamp (c H : ℝ) : Continuous (normalizedCubeRamp c H) := by
  unfold normalizedCubeRamp cubeRamp
  exact (continuous_const.max (continuous_const.min (continuous_id.sub continuous_const))).div_const H

theorem normalizedCubeRamp_nonneg (c : ℝ) {H : ℝ} (hH : 0 < H) (x : ℝ) :
    0 ≤ normalizedCubeRamp c H x := div_nonneg (cubeRamp_nonneg c H x) hH.le

theorem normalizedCubeRamp_le_one (c : ℝ) {H : ℝ} (hH : 0 < H) (x : ℝ) :
    normalizedCubeRamp c H x ≤ 1 := by
  exact (div_le_one hH).mpr (cubeRamp_le_width c H x hH.le)

theorem monotone_normalizedCubeRamp (c : ℝ) {H : ℝ} (hH : 0 < H) :
    Monotone (normalizedCubeRamp c H) := by
  intro x y hxy
  exact div_le_div_of_nonneg_right (cubeRamp_monotone c H hxy) hH.le

def cubeRampPrimitive (c H x : ℝ) : ℝ := ∫ t in (0 : ℝ)..x, normalizedCubeRamp c H t

theorem hasDerivAt_cubeRampPrimitive (c H x : ℝ) :
    HasDerivAt (cubeRampPrimitive c H) (normalizedCubeRamp c H x) x := by
  have hc := continuous_normalizedCubeRamp c H
  exact intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable 0 x)
    hc.aestronglyMeasurable.stronglyMeasurableAtFilter hc.continuousAt

theorem monotone_cubeRampPrimitive (c : ℝ) {H : ℝ} (hH : 0 < H) :
    Monotone (cubeRampPrimitive c H) :=
  monotone_of_hasDerivAt_nonneg (hasDerivAt_cubeRampPrimitive c H)
    (normalizedCubeRamp_nonneg c hH)

theorem convexOn_cubeRampPrimitive (c : ℝ) {H : ℝ} (hH : 0 < H) :
    ConvexOn ℝ univ (cubeRampPrimitive c H) := by
  have hd : Differentiable ℝ (cubeRampPrimitive c H) :=
    fun x => (hasDerivAt_cubeRampPrimitive c H x).differentiableAt
  have he : deriv (cubeRampPrimitive c H) = normalizedCubeRamp c H :=
    funext (fun x => (hasDerivAt_cubeRampPrimitive c H x).deriv)
  apply Monotone.convexOn_univ_of_deriv hd
  rw [he]
  exact monotone_normalizedCubeRamp c hH

theorem convexOn_realAffineCubeMaximum {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) :
    ConvexOn ℝ univ (realAffineCubeMaximum B a) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ s t hs ht hst
  obtain ⟨α, hα⟩ := finiteFamilyMaximum_attains
    (fun α => (∑ i, B α i * (s • x + t • y) i) - a α)
  change finiteFamilyMaximum (fun α => (∑ i, B α i * (s • x + t • y) i) - a α) ≤ _
  rw [hα]
  have hx := le_finiteFamilyMaximum (fun α => (∑ i, B α i * x i) - a α) α
  have hy := le_finiteFamilyMaximum (fun α => (∑ i, B α i * y i) - a α) α
  have he : (∑ i, B α i * (s • x + t • y) i) - a α =
      s * ((∑ i, B α i * x i) - a α) + t * ((∑ i, B α i * y i) - a α) := by
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add, Finset.sum_add_distrib]
    simp only [← Finset.mul_sum, mul_assoc, ← Finset.mul_sum, mul_left_comm (B α _)]
    have hsuma : (s + t) * a α = a α := by rw [hst, one_mul]
    nlinarith only [hsuma]
  rw [he]
  exact add_le_add (mul_le_mul_of_nonneg_left hx hs) (mul_le_mul_of_nonneg_left hy ht)

/-- The printed convex nondecreasing antiderivative composed with the
convex maximum is genuinely convex. No differentiability at ties is needed
for this structural convexity statement. -/
theorem convexOn_cubeRampPrimitive_comp_maximum {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (c : ℝ) {H : ℝ} (hH : 0 < H) :
    ConvexOn ℝ univ (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a) := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy s t hs ht hst
  have hmax := (convexOn_realAffineCubeMaximum B a).2 hx hy hs ht hst
  have hmono := (monotone_cubeRampPrimitive c hH) hmax
  have hprim := (convexOn_cubeRampPrimitive c hH).2
    (mem_univ (realAffineCubeMaximum B a x))
    (mem_univ (realAffineCubeMaximum B a y)) hs ht hst
  exact hmono.trans hprim

@[simp] theorem cubeLinearCLM_single {n : ℕ} (b : Fin n → ℝ) (i : Fin n) :
    cubeLinearCLM b (Pi.single i 1) = b i := by
  simp [cubeLinearCLM_apply, Pi.single_apply, mul_ite]

/-- The derivative of the printed convex composition at a unique vertex
is exactly the ramp times the derivative of its active affine branch. -/
theorem CubeUniqueMax.hasFDerivAt_ramp_composition {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (c H : ℝ) (x : Kane.Cube n) :
    HasFDerivAt (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a)
      (normalizedCubeRamp c H (affineCubeMaximum B a x) •
        cubeLinearCLM (B (activeCubeBranch B a x))) (cubeVertex x) := by
  have hd := (hasDerivAt_cubeRampPrimitive c H
    (realAffineCubeMaximum B a (cubeVertex x))).comp_hasFDerivAt
      (cubeVertex x) (hu.hasFDerivAt_maximum x)
  simpa only [realAffineCubeMaximum_vertex] using hd

def cubeGradientRadial {n : ℕ} (g : (Fin n → ℝ) → ℝ) (x : Kane.Cube n) : ℝ :=
  ∑ i, cubeSign x i * (fderiv ℝ g (cubeVertex x)) (Pi.single i 1)

theorem CubeUniqueMax.gradient_radial_eq {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (c H : ℝ) (x : Kane.Cube n) :
    cubeGradientRadial (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a) x =
      normalizedCubeRamp c H (affineCubeMaximum B a x) *
        cubeLinear (B (activeCubeBranch B a x)) x := by
  unfold cubeGradientRadial
  rw [(hu.hasFDerivAt_ramp_composition c H x).fderiv]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, cubeLinearCLM_single, cubeLinear]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem CubeUniqueMax.gradient_energy_eq {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (x : Kane.Cube n) :
    (∑ i, ((fderiv ℝ (realAffineCubeMaximum B a) (cubeVertex x)) (Pi.single i 1)) ^ 2) =
      ∑ i, (B (activeCubeBranch B a x) i) ^ 2 := by
  rw [(hu.hasFDerivAt_maximum x).fderiv]
  simp only [cubeLinearCLM_single]

/-- Exact cube integration by parts for the actual gradient in the printed
unique case, expressed through the already proved endpoint edge flux. -/
theorem CubeUniqueMax.avg_gradient_radial_eq_flux {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (c H : ℝ) :
    Kane.avg (cubeGradientRadial (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a)) =
      Kane.avg (fun x => ∑ i, affineCubeEdgeFlux B a c H x i) / H := by
  have hf : cubeGradientRadial (cubeRampPrimitive c H ∘ realAffineCubeMaximum B a) =
      (fun x => normalizedCubeRamp c H (affineCubeMaximum B a x) *
        cubeLinear (B (activeCubeBranch B a x)) x) :=
    funext (hu.gradient_radial_eq c H)
  rw [hf]
  rw [avg_affineCubeEdgeFlux_sum]
  have he : (fun x => normalizedCubeRamp c H (affineCubeMaximum B a x) *
      cubeLinear (B (activeCubeBranch B a x)) x) =
      (fun x => (cubeRamp c H (affineCubeMaximum B a x) *
        cubeLinear (B (activeCubeBranch B a x)) x) / H) := by
    funext x
    unfold normalizedCubeRamp
    ring
  rw [he]
  simp only [div_eq_mul_inv]
  exact Kane.avg_mul_const _ _

end
end RectangleCLT.Companion.SplitV4.Printed
