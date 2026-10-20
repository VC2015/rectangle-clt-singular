import RectangleCLTCompanion.SharpComparisonCubicPath

/-! Concrete half-Gaussian base law for the sharp comparison. The retained
observations keep their actual full Bernoulli mixture law. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- Each independent Gaussian half has variance `t/2`. -/
def splitGaussianScale (t : ℝ) : ℝ := Real.sqrt (t / 2)

/-- The actual retained-array law together with the first independent
standard Gaussian. The second Gaussian is reserved for integration by parts. -/
def splitBaseLaw {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (t : ℝ) :
    Measure ((Fin n → Vector p) × Vector p) :=
  (bernoulliArrayLaw μ ξ t).prod (standardGaussian p)

def splitBaseValue {p n : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) (z : (Fin n → Vector p) × Vector p) : Vector p :=
  x + arraySum z.1 + (splitGaussianScale t • A).mulVec z.2

theorem measurable_splitBaseValue {p n : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (t : ℝ) : Measurable (splitBaseValue (n := n) A x t) :=
  (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
    ((measurable_mulVec _).comp measurable_snd)

theorem splitBaseLaw_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) : IsProbabilityMeasure (splitBaseLaw μ ξ t) := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  unfold splitBaseLaw
  infer_instance

theorem splitGaussianScale_pos {t : ℝ} (ht : 0 < t) : 0 < splitGaussianScale t :=
  Real.sqrt_pos.mpr (by linarith)

theorem splitGaussianScale_sq {t : ℝ} (ht : 0 ≤ t) : splitGaussianScale t ^ 2 = t / 2 :=
  Real.sq_sqrt (by positivity)

end
end RectangleCLT.Companion
