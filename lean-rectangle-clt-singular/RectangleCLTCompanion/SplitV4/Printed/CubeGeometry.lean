import RectangleCLTCompanion.SplitV4.Printed.CubePerturbation
import RectangleCLTCompanion.SplitV4.CubeContraction
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod

/-! At a vertex with a unique active affine branch, the supporting slope
used in the finite edge calculation is the actual Fréchet derivative.
This verifies the derivative interpretation in the printed unique case. -/

open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

def cubeVertex {n : ℕ} (x : Kane.Cube n) : Fin n → ℝ := fun i => cubeSign x i

def cubeLinearCLM {n : ℕ} (b : Fin n → ℝ) : (Fin n → ℝ) →L[ℝ] ℝ :=
  ∑ i, b i • ContinuousLinearMap.proj i

@[simp] theorem cubeLinearCLM_apply {n : ℕ} (b y : Fin n → ℝ) :
    cubeLinearCLM b y = ∑ i, b i * y i := by
  simp [cubeLinearCLM]

def realAffineCubeMaximum {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (y : Fin n → ℝ) : ℝ :=
  finiteFamilyMaximum (fun α => (∑ i, B α i * y i) - a α)

@[simp] theorem realAffineCubeMaximum_vertex {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (x : Kane.Cube n) :
    realAffineCubeMaximum B a (cubeVertex x) = affineCubeMaximum B a x := rfl

theorem CubeUniqueMax.strict_active {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (x : Kane.Cube n) (β : Fin m) (hβ : β ≠ activeCubeBranch B a x) :
    cubeLinear (B β) x - a β <
      cubeLinear (B (activeCubeBranch B a x)) x - a (activeCubeBranch B a x) := by
  obtain ⟨α, hα⟩ := hu x
  have he : activeCubeBranch B a x = α := by
    by_contra hn
    have hlt := hα _ hn
    have hle := affineCubeMaximum_supports B a x α
    rw [activeCubeBranch_attains] at hle
    linarith
  rw [he] at hβ ⊢
  exact hα β hβ

theorem CubeUniqueMax.eventually_eq_active {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (x : Kane.Cube n) :
    realAffineCubeMaximum B a =ᶠ[𝓝 (cubeVertex x)]
      (fun y => (∑ i, B (activeCubeBranch B a x) i * y i) - a (activeCubeBranch B a x)) := by
  let α := activeCubeBranch B a x
  have hβ (β : Fin m) : ∀ᶠ y in 𝓝 (cubeVertex x),
      (∑ i, B β i * y i) - a β ≤ (∑ i, B α i * y i) - a α := by
    by_cases he : β = α
    · subst β
      exact Filter.Eventually.of_forall (fun _ => le_rfl)
    · have hs : (∑ i, B β i * cubeVertex x i) - a β <
          (∑ i, B α i * cubeVertex x i) - a α := hu.strict_active x β he
      have hcβ : ContinuousAt (fun y : Fin n → ℝ => (∑ i, B β i * y i) - a β) (cubeVertex x) := by
        simpa only [cubeLinearCLM_apply] using
          ((cubeLinearCLM (B β)).continuous.sub continuous_const).continuousAt
      have hcα : ContinuousAt (fun y : Fin n → ℝ => (∑ i, B α i * y i) - a α) (cubeVertex x) := by
        simpa only [cubeLinearCLM_apply] using
          ((cubeLinearCLM (B α)).continuous.sub continuous_const).continuousAt
      exact (hcβ.eventually_lt hcα hs).mono (fun _ h => h.le)
  have hall := Filter.eventually_all.mpr hβ
  filter_upwards [hall] with y hy
  change finiteFamilyMaximum (fun β => (∑ i, B β i * y i) - a β) = _
  apply le_antisymm
  · unfold finiteFamilyMaximum
    exact Finset.sup'_le _ _ (fun β _ => hy β)
  · exact le_finiteFamilyMaximum (fun β => (∑ i, B β i * y i) - a β)
      (activeCubeBranch B a x)

theorem CubeUniqueMax.hasFDerivAt_maximum {m n : ℕ} [NeZero m]
    {B : Fin m → Fin n → ℝ} {a : Fin m → ℝ} (hu : CubeUniqueMax B a)
    (x : Kane.Cube n) :
    HasFDerivAt (realAffineCubeMaximum B a)
      (cubeLinearCLM (B (activeCubeBranch B a x))) (cubeVertex x) := by
  have h := ((cubeLinearCLM (B (activeCubeBranch B a x))).hasFDerivAt
    (x := cubeVertex x)).sub_const
    (a (activeCubeBranch B a x))
  apply h.congr_of_eventuallyEq
  simpa only [cubeLinearCLM_apply] using hu.eventually_eq_active x

end
end RectangleCLT.Companion.SplitV4.Printed
