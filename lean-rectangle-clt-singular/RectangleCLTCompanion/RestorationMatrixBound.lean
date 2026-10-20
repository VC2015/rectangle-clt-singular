import RectangleCLTCompanion.RestorationSeries
import RectangleCLTCompanion.RestorationScore

/-! The precise averaged matrix interface consumed by restoration.  This is
an explicit hypothesis in intermediate lemmas, not an axiom or an asserted
surface estimate.  Its numerical scale is left as `T` so the independently
proved selector matrix estimate can supply `h * L^(3/2)` directly. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section
set_option autoImplicit false

variable {p r : ℕ} {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]

def selectorGaussianScore (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    {q : ℕ} (α : Fin q → Face p) (ω : Ω) : Matrix (Fin r) (Fin r) ℝ :=
  weightedScore (standardGaussian r) id
    (fun g => selectorTupleWeight s α (A.mulVec g + V ω))

/-- Actual averaged trace-family estimate.  The coefficient matrices may
depend measurably on the bounded-array base, and the estimate is taken after
averaging that base.  No conditional concentration is assumed. -/
def AveragedSelectorMatrixEstimate (s : FaceSmoother p) (ν : Measure Ω)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (C T : ℝ) : Prop :=
  ∀ q : ℕ, 1 ≤ q → ∀ b : ℝ, 0 ≤ b →
    ∀ B : (Fin q → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ,
      (∀ α j k, Measurable (fun ω => B α ω j k)) →
      (∀ α ω u, |matrixQuadratic (B α ω) u| ≤ b * vectorNormSq u) →
      Integrable (fun ω => ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)|) ν ∧
      (∫ ω, ∑ α, |Matrix.trace (B α ω * selectorGaussianScore s A V α ω)| ∂ν) ≤
        b * C ^ (q + 1) * T

def translatedRestorationCoefficient (s : FaceSmoother p) (μ : Measure Ξ)
    {n k ℓ : ℕ} (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) (ω : Ω) :
    Matrix (Fin r) (Fin r) ℝ :=
  restorationCoefficient μ (Z ω)
    (fun i a => c i α ω a * restorationTranslationCoefficient s α β (v i ω a))

omit [MeasurableSpace Ω] in
/-- A direct consequence of the covariance budget for each realization of
the base.  The fresh multipliers can depend on all fresh directions. -/
theorem translatedRestorationCoefficient_quadratic_le
    (s : FaceSmoother p) (μ : Measure Ξ) {n k ℓ : ℕ}
    (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p) {b K R : ℝ}
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hc : ∀ i α ω, AEStronglyMeasurable (fun a => c i α ω a) μ)
    (hv : ∀ i ω, Measurable (v i ω))
    (hb : ∀ i α ω a, |c i α ω a| ≤ b) (hb0 : 0 ≤ b)
    (hR : 0 ≤ R) (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤
      K * vectorNormSq u)
    (α : Fin k → Face p) (β : Fin ℓ → Face p) (ω : Ω) (u : Vector r) :
    |matrixQuadratic (translatedRestorationCoefficient s μ Z c v α β ω) u| ≤
      (b * Real.exp ((k : ℝ) * R / s.bandwidth) *
        (Real.exp (R / s.bandwidth) - 1) ^ ℓ * K) * vectorNormSq u := by
  have hm : ∀ i, AEStronglyMeasurable
      (fun a => c i α ω a * restorationTranslationCoefficient s α β (v i ω a)) μ := by
    intro i
    apply (hc i α ω).mul
    unfold restorationTranslationCoefficient translationIncrement
    apply Measurable.aestronglyMeasurable
    apply Measurable.mul
    · exact (((Finset.measurable_sum _ (fun j _ =>
        (FaceSmoother.continuous_normalDot (α j)).measurable.comp (hv i ω))).div_const _).exp)
    · exact Finset.measurable_prod _ (fun j _ =>
        ((((FaceSmoother.continuous_normalDot (β j)).measurable.comp (hv i ω)).div_const _).exp).sub_const 1)
  have hcb (i : Fin n) (a : Ξ) :
      |c i α ω a * restorationTranslationCoefficient s α β (v i ω a)| ≤
        b * Real.exp ((k : ℝ) * R / s.bandwidth) *
          (Real.exp (R / s.bandwidth) - 1) ^ ℓ := by
    rw [abs_mul]
    calc
      _ ≤ b * |restorationTranslationCoefficient s α β (v i ω a)| :=
        mul_le_mul_of_nonneg_right (hb i α ω a) (abs_nonneg _)
      _ ≤ b * (Real.exp ((k : ℝ) * R / s.bandwidth) *
          (Real.exp (R / s.bandwidth) - 1) ^ ℓ) :=
        mul_le_mul_of_nonneg_left
          (abs_restorationTranslationCoefficient_le s α β hR (hvb i ω a)) hb0
      _ = _ := by ring
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  exact abs_matrixQuadratic_restorationCoefficient_le μ (Z ω) _
    (hZ ω) hm hcb (by positivity) (hbudget ω) u

/-- A pair of ordered face tuples is a single ordered tuple, with no
face-count or factorial factor. -/
theorem sum_faceTuples_append {k ℓ : ℕ}
    (f : (Fin k → Face p) → (Fin ℓ → Face p) → ℝ) :
    (∑ α, ∑ β, f α β) =
      ∑ γ : Fin (k + ℓ) → Face p,
        f (fun i => γ (Fin.castAdd ℓ i)) (fun i => γ (Fin.natAdd k i)) := by
  calc
    _ = ∑ ab : (Fin k → Face p) × (Fin ℓ → Face p), f ab.1 ab.2 :=
      (Fintype.sum_prod_type (fun ab => f ab.1 ab.2)).symm
    _ = _ := ((Fin.appendEquiv k ℓ).symm.sum_comp (fun ab => f ab.1 ab.2)).symm

theorem selectorTupleWeight_append {k ℓ : ℕ}
    (s : FaceSmoother p) (α : Fin k → Face p) (β : Fin ℓ → Face p) (x : Vector p) :
    selectorTupleWeight s (Fin.append α β) x =
      selectorTupleWeight s α x * ∏ i, s.pi x (β i) := by
  unfold selectorTupleWeight
  rw [Fin.prod_univ_add]
  simp only [Fin.append_left, Fin.append_right, mul_assoc]

/-- The actual averaged matrix estimate applied at a fixed order of the
translated series.  Its only analytic estimate premise is the displayed
`AveragedSelectorMatrixEstimate`. -/
theorem averaged_translatedRestorationCoefficient_order_le
    (s : FaceSmoother p) (ν : Measure Ω) (μ : Measure Ξ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) {n k ℓ : ℕ}
    (Z : Ω → Fin n → Ξ → Vector r)
    (c : Fin n → (Fin k → Face p) → Ω → Ξ → ℝ)
    (v : Fin n → Ω → Ξ → Vector p) {b K R C T : ℝ}
    (hmatrix : AveragedSelectorMatrixEstimate s ν A V C T)
    (hk : 1 ≤ k)
    (hZ : ∀ ω i j l, Integrable (fun a => Z ω i a j * Z ω i a l) μ)
    (hc : ∀ i α ω, AEStronglyMeasurable (fun a => c i α ω a) μ)
    (hv : ∀ i ω, Measurable (v i ω))
    (hb : ∀ i α ω a, |c i α ω a| ≤ b) (hb0 : 0 ≤ b) (hK : 0 ≤ K)
    (hR : 0 ≤ R) (hvb : ∀ i ω a, ‖v i ω a‖ ≤ R)
    (hbudget : ∀ ω u, ∑ i, ∫ a, (faceDot u (Z ω i a)) ^ 2 ∂μ ≤
      K * vectorNormSq u)
    (hBm : ∀ (α : Fin k → Face p) (β : Fin ℓ → Face p) (j l : Fin r),
      Measurable (fun ω => translatedRestorationCoefficient s μ Z c v α β ω j l)) :
    (∫ ω, ∑ α : Fin k → Face p, ∑ β : Fin ℓ → Face p,
      |Matrix.trace (translatedRestorationCoefficient s μ Z c v α β ω *
        selectorGaussianScore s A V (Fin.append α β) ω)| ∂ν) ≤
      (b * Real.exp ((k : ℝ) * R / s.bandwidth) *
        (Real.exp (R / s.bandwidth) - 1) ^ ℓ * K) * C ^ (k + ℓ + 1) * T := by
  let B : (Fin (k + ℓ) → Face p) → Ω → Matrix (Fin r) (Fin r) ℝ :=
    fun γ => translatedRestorationCoefficient s μ Z c v
      (fun i => γ (Fin.castAdd ℓ i)) (fun i => γ (Fin.natAdd k i))
  have hη : 0 ≤ Real.exp (R / s.bandwidth) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hs := hmatrix (k + ℓ) (by omega)
    (b * Real.exp ((k : ℝ) * R / s.bandwidth) *
      (Real.exp (R / s.bandwidth) - 1) ^ ℓ * K) (by positivity) B
    (fun γ j l => hBm _ _ j l)
    (fun γ ω u => translatedRestorationCoefficient_quadratic_le s μ Z c v
      hZ hc hv hb hb0 hR hvb hbudget _ _ ω u)
  convert hs.2 using 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only
    rw [sum_faceTuples_append]
    apply Finset.sum_congr rfl
    intro γ _
    simp only [B, Fin.append_castAdd_natAdd])

end
end RectangleCLT.Companion
