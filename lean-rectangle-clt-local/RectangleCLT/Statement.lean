import Mathlib.Probability.Distributions.Gaussian
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Real
import Mathlib.Topology.Instances.Matrix
import Mathlib.Order.Interval.Set.OrdConnected
import Mathlib.Data.Finset.Fold
import Mathlib.Tactic.Linarith

/-!
# A concrete statement of the bounded rectangle CLT

This file defines the intended theorem; `BoundedRectangleCLT` and
`BoundedRectangleCLTExists` are propositions, not proved CLT declarations.
The target Gaussian is an explicit linear image of independent standard
normal coordinates. Its factor is required to have the actual covariance
of the sum. Rectangles include every open, closed, mixed, and unbounded
coordinate interval, as well as empty intervals.
-/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

noncomputable section

/-- The native norm on this finite real product is the maximum norm. -/
abbrev Vector (p : ℕ) := Fin p → ℝ

/-- A measurable axis-aligned rectangle, with every endpoint convention. -/
structure Rect (p : ℕ) where
  interval : Fin p → Set ℝ
  ordConnected : ∀ j, Set.OrdConnected (interval j)
  measurable : ∀ j, MeasurableSet (interval j)

def Rect.carrier {p : ℕ} (R : Rect p) : Set (Vector p) :=
  Set.pi Set.univ R.interval

theorem Rect.measurableSet_carrier {p : ℕ} (R : Rect p) :
    MeasurableSet R.carrier :=
  MeasurableSet.pi Set.countable_univ (fun j _ => R.measurable j)

def Rect.univ (p : ℕ) : Rect p where
  interval := fun _ => Set.univ
  ordConnected := fun _ => Set.ordConnected_univ
  measurable := fun _ => MeasurableSet.univ

/-- All coordinate intervals are empty. Its carrier is empty when `p > 0`,
as required by the CLT statement; the empty product in dimension zero is a singleton. -/
def Rect.empty (p : ℕ) : Rect p where
  interval := fun _ => ∅
  ordConnected := fun _ => Set.ordConnected_empty
  measurable := fun _ => MeasurableSet.empty

def Rect.closedBox {p : ℕ} (lo hi : Vector p) : Rect p where
  interval := fun j => Set.Icc (lo j) (hi j)
  ordConnected := fun _ => Set.ordConnected_Icc
  measurable := fun _ => measurableSet_Icc

/-- The sum of the independent observations; no normalization is implicit. -/
def sumVector {Ω : Type u} {p n : ℕ} (ξ : Fin n → Ω → Vector p)
    (ω : Ω) : Vector p := ∑ i, ξ i ω

/-- Actual covariance, defined from the coordinate integrals. -/
def covariance {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) : Matrix (Fin p) (Fin p) ℝ :=
  fun j k => (∫ ω, W ω j * W ω k ∂μ) -
    (∫ ω, W ω j ∂μ) * (∫ ω, W ω k ∂μ)

theorem covariance_transpose {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) :
    (covariance μ W).transpose = covariance μ W := by
  ext j k
  simp only [Matrix.transpose_apply, covariance, mul_comm]

/-- Joint standard normal law, with independent coordinates. -/
def standardGaussian (p : ℕ) : Measure (Vector p) :=
  Measure.pi (fun _ : Fin p => gaussianReal 0 1)

instance standardGaussian_isProbability (p : ℕ) :
    IsProbabilityMeasure (standardGaussian p) := by
  unfold standardGaussian
  infer_instance

/-- A concrete centered Gaussian vector with factor `A`. -/
def gaussianLaw {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : Measure (Vector p) :=
  (standardGaussian p).map A.mulVec

theorem measurable_mulVec {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    Measurable A.mulVec :=
  (continuous_const.matrix_mulVec continuous_id).measurable

instance gaussianLaw_isProbability {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) :
    IsProbabilityMeasure (gaussianLaw A) := by
  exact isProbabilityMeasure_map (measurable_mulVec A).aemeasurable

/-- Maximum absolute entry of the *summed* third-moment tensor.
The absolute value is taken after summing over observations. -/
def gamma3 {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : ℝ :=
  (Finset.univ : Finset (Fin p × Fin p × Fin p)).fold max 0 fun jkl =>
    |∑ i, ∫ ω, ξ i ω jkl.1 * ξ i ω jkl.2.1 * ξ i ω jkl.2.2 ∂μ|

/-- Maximum coordinate sum of fourth moments. The initial zero only matters
in dimension zero, which the intended CLT excludes. -/
def gamma4 {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : ℝ :=
  (Finset.univ : Finset (Fin p)).fold max 0 fun j =>
    ∑ i, ∫ ω, (ξ i ω j) ^ 4 ∂μ

theorem gamma3_nonneg {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : 0 ≤ gamma3 μ ξ := by
  exact (Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl)

theorem gamma4_nonneg {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) : 0 ≤ gamma4 μ ξ := by
  exact (Finset.le_fold_max (0 : ℝ)).mpr (Or.inl le_rfl)

def dimensionLog (p : ℕ) : ℝ := Real.log (Real.exp 1 * (p : ℝ))

/-- The rate in bounded Theorem 1. The factor `L^(3/2)` is written
`L * sqrt L`; the target assumes `p ≥ 1`, hence `L ≥ 1`. -/
def boundedRate {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ b : ℝ) : ℝ :=
  (gamma3 μ ξ * dimensionLog p * Real.sqrt (dimensionLog p) +
    Real.sqrt (gamma4 μ ξ) * dimensionLog p +
    δ * Real.sqrt (dimensionLog p)) / b ^ 2

/-- The substantive probabilistic hypotheses of bounded Theorem 1.
Independence is between whole vector observations; the coordinates within
each observation may be dependent. -/
structure BoundedHypotheses {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (δ b : ℝ) : Prop where
  measurable : ∀ i, Measurable (ξ i)
  independent : iIndepFun ξ μ
  centered : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0
  bounded : ∀ i, ∀ᵐ ω ∂μ, ‖ξ i ω‖ ≤ δ
  delta_nonneg : 0 ≤ δ
  b_pos : 0 < b
  b_le_one : b ≤ 1
  unit_diagonal : ∀ j, covariance μ (sumVector ξ) j j = 1
  spectral_lower : ∀ v : Vector p,
    b ^ 2 * (∑ j, (v j) ^ 2) ≤
      ∑ j, ∑ k, v j * covariance μ (sumVector ξ) j k * v k

/-- The probability discrepancy at one concrete rectangle. -/
def rectangleError {Ω : Type u} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) : ℝ :=
  |μ.real (W ⁻¹' R.carrier) - (gaussianLaw A).real R.carrier|

/-- Precise target statement for a fixed absolute constant.
The factor equality forces the Gaussian to use the covariance of the actual
sum. There is no Gaussian-approximation hypothesis hidden in the inputs. -/
def BoundedRectangleCLT (C : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (p n : ℕ), 1 ≤ p → 1 ≤ n →
    ∀ (ξ : Fin n → Ω → Vector p) (δ b : ℝ)
      (A : Matrix (Fin p) (Fin p) ℝ),
      BoundedHypotheses μ ξ δ b →
      A * A.transpose = covariance μ (sumVector ξ) →
      ∀ R : Rect p, rectangleError μ (sumVector ξ) A R ≤
        C * min 1 (boundedRate μ ξ δ b)

/-- The intended absolute-constant theorem, stated as a proposition.
The constant is chosen before the space, dimensions, distributions, and
parameters, and is required to be at least one. -/
def BoundedRectangleCLTExists : Prop :=
  ∃ C : ℝ, 1 ≤ C ∧ BoundedRectangleCLT.{u} C

/-- The elementary saturated probability bound; this is not a CLT rate. -/
theorem rectangleError_le_one {Ω : Type u} [MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] {p : ℕ}
    (W : Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p) :
    rectangleError μ W A R ≤ 1 := by
  unfold rectangleError
  have hμ0 : 0 ≤ μ.real (W ⁻¹' R.carrier) := measureReal_nonneg
  have hμ1 : μ.real (W ⁻¹' R.carrier) ≤ 1 := measureReal_le_one
  have hG0 : 0 ≤ (gaussianLaw A).real R.carrier := measureReal_nonneg
  have hG1 : (gaussianLaw A).real R.carrier ≤ 1 := measureReal_le_one
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end RectangleCLT
