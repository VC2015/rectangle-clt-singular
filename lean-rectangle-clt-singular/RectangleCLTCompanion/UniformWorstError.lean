import RectangleCLTCompanion.ConsistencyStatement
import Mathlib.Topology.Algebra.Order.LiminfLimsup

/-! The literal worst rectangle errors over the full probability classes
in Theorem 5. The supremum ranges over all sample spaces in the selected
universe, all admissible laws and observations, and all rectangles.
Including zero gives the usual zero value for an empty admissible class. -/

open MeasureTheory Filter
open scoped Topology
universe u
namespace RectangleCLT.Companion
noncomputable section

def uniformClassErrors (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) : Set ℝ :=
  {e | e=0 ∨ ∃ (Ω : Type u) (mΩ : MeasurableSpace Ω),
    letI := mΩ
    ∃ (μ : Measure Ω), IsProbabilityMeasure μ ∧
    ∃ (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ) (R : Rect p),
      BoundedIndependentHypotheses μ ξ (B/Real.sqrt n) ∧
      (∀j,covariance μ (sumVector ξ) j j=1) ∧
      c₀≤pairGap (covariance μ (sumVector ξ)) ∧
      A*A.transpose=covariance μ (sumVector ξ) ∧
      (zeroSkew=true → AggregateThirdMomentsVanish μ ξ) ∧
      e=rectangleError μ (sumVector ξ) A R}

def uniformWorstError (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) : ℝ :=
  sSup (uniformClassErrors.{u} zeroSkew c₀ B p n)

def fixedGapWorstError (c₀ B : ℝ) (p n : ℕ) : ℝ :=
  uniformWorstError.{u} false c₀ B p n

def zeroSkewFixedGapWorstError (c₀ B : ℝ) (p n : ℕ) : ℝ :=
  uniformWorstError.{u} true c₀ B p n

def uniformModelClassBound (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) (ε : ℝ) : Prop :=
  ∀ {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ),
    BoundedIndependentHypotheses μ ξ (B/Real.sqrt n) →
    (∀j,covariance μ (sumVector ξ) j j=1) →
    c₀≤pairGap (covariance μ (sumVector ξ)) →
    A*A.transpose=covariance μ (sumVector ξ) →
    (zeroSkew=true → AggregateThirdMomentsVanish μ ξ) →
    ∀R : Rect p,rectangleError μ (sumVector ξ) A R<ε

theorem uniformModelClassBound_false (c₀ B : ℝ) (p n : ℕ) (ε : ℝ) :
    uniformModelClassBound.{u} false c₀ B p n ε ↔ FixedGapClassBound.{u} c₀ B p n ε := by
  simp [uniformModelClassBound,FixedGapClassBound]

theorem uniformModelClassBound_true (c₀ B : ℝ) (p n : ℕ) (ε : ℝ) :
    uniformModelClassBound.{u} true c₀ B p n ε ↔ ZeroSkewFixedGapClassBound.{u} c₀ B p n ε := by
  simp [uniformModelClassBound,ZeroSkewFixedGapClassBound]

theorem zero_mem_uniformClassErrors (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) :
    0∈uniformClassErrors.{u} zeroSkew c₀ B p n := Or.inl rfl

theorem uniformClassErrors_le_one {zeroSkew : Bool} {c₀ B e : ℝ} {p n : ℕ}
    (he : e∈uniformClassErrors.{u} zeroSkew c₀ B p n) : e≤1 := by
  rcases he with rfl | ⟨Ω,mΩ,h⟩
  · norm_num
  · letI := mΩ
    rcases h with ⟨μ,hprob,ξ,A,R,hdata,hunit,hgap,hfactor,hcancel,rfl⟩
    letI := hprob
    exact rectangleError_le_one μ (sumVector ξ) A R

theorem uniformClassErrors_bddAbove (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) :
    BddAbove (uniformClassErrors.{u} zeroSkew c₀ B p n) :=
  ⟨1,fun _ he => uniformClassErrors_le_one he⟩

theorem uniformWorstError_nonneg (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) :
    0≤uniformWorstError.{u} zeroSkew c₀ B p n :=
  le_csSup (uniformClassErrors_bddAbove _ _ _ _ _) (zero_mem_uniformClassErrors _ _ _ _ _)

theorem uniformWorstError_le_one (zeroSkew : Bool) (c₀ B : ℝ) (p n : ℕ) :
    uniformWorstError.{u} zeroSkew c₀ B p n≤1 :=
  csSup_le ⟨0,zero_mem_uniformClassErrors _ _ _ _ _⟩ (fun _ he => uniformClassErrors_le_one he)

theorem rectangleError_mem_uniformClassErrors
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {zeroSkew : Bool} {c₀ B : ℝ}
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ (B/Real.sqrt n))
    (hunit : ∀j,covariance μ (sumVector ξ) j j=1)
    (hgap : c₀≤pairGap (covariance μ (sumVector ξ)))
    (hfactor : A*A.transpose=covariance μ (sumVector ξ))
    (hcancel : zeroSkew=true → AggregateThirdMomentsVanish μ ξ) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R∈uniformClassErrors.{u} zeroSkew c₀ B p n :=
  Or.inr ⟨Ω,inferInstance,μ,inferInstance,ξ,A,R,hdata,hunit,hgap,hfactor,hcancel,rfl⟩

theorem rectangleError_le_uniformWorstError
    {Ω : Type u} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {p n : ℕ} {zeroSkew : Bool} {c₀ B : ℝ}
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdata : BoundedIndependentHypotheses μ ξ (B/Real.sqrt n))
    (hunit : ∀j,covariance μ (sumVector ξ) j j=1)
    (hgap : c₀≤pairGap (covariance μ (sumVector ξ)))
    (hfactor : A*A.transpose=covariance μ (sumVector ξ))
    (hcancel : zeroSkew=true → AggregateThirdMomentsVanish μ ξ) (R : Rect p) :
    rectangleError μ (sumVector ξ) A R≤uniformWorstError.{u} zeroSkew c₀ B p n :=
  le_csSup (uniformClassErrors_bddAbove _ _ _ _ _)
    (rectangleError_mem_uniformClassErrors μ ξ A hdata hunit hgap hfactor hcancel R)

theorem uniformModelClassBound_of_worstError_lt
    {zeroSkew : Bool} {c₀ B ε : ℝ} {p n : ℕ}
    (h : uniformWorstError.{u} zeroSkew c₀ B p n<ε) :
    uniformModelClassBound.{u} zeroSkew c₀ B p n ε := by
  intro Ω _ μ _ ξ A hdata hunit hgap hfactor hcancel R
  exact (rectangleError_le_uniformWorstError μ ξ A hdata hunit hgap hfactor hcancel R).trans_lt h

theorem uniformWorstError_le_of_classBound
    {zeroSkew : Bool} {c₀ B ε : ℝ} {p n : ℕ} (hε : 0≤ε)
    (h : uniformModelClassBound.{u} zeroSkew c₀ B p n ε) :
    uniformWorstError.{u} zeroSkew c₀ B p n≤ε := by
  apply csSup_le ⟨0,zero_mem_uniformClassErrors _ _ _ _ _⟩
  intro e he
  rcases he with rfl | ⟨Ω,mΩ,hh⟩
  · exact hε
  · letI := mΩ
    rcases hh with ⟨μ,hprob,ξ,A,R,hdata,hunit,hgap,hfactor,hcancel,rfl⟩
    letI := hprob
    exact (h μ ξ A hdata hunit hgap hfactor hcancel R).le

theorem uniformWorstError_tendsto_zero_iff
    (zeroSkew : Bool) (c₀ : ℝ) (B : ℕ → ℝ) (p : ℕ → ℕ) :
    Tendsto (fun n => uniformWorstError.{u} zeroSkew c₀ (B n) (p n) n) atTop (𝓝 0) ↔
      ∀ε : ℝ,0<ε → ∀ᶠ n in atTop,uniformModelClassBound.{u} zeroSkew c₀ (B n) (p n) n ε := by
  constructor
  · intro h ε hε
    filter_upwards [h.eventually (eventually_lt_nhds hε)] with n hn
    exact uniformModelClassBound_of_worstError_lt hn
  · intro h
    apply tendsto_order.mpr
    constructor
    · intro a ha
      exact Eventually.of_forall (fun n => ha.trans_le (uniformWorstError_nonneg _ _ _ _ _))
    · intro a ha
      filter_upwards [h (a/2) (by linarith)] with n hn
      exact (uniformWorstError_le_of_classBound (by linarith) hn).trans_lt (by linarith)

/-- Literal numerical form of uniform consistency for the full class. -/
theorem fixedGapWorstError_tendsto_zero_iff (c₀ : ℝ) (B : ℕ → ℝ) (p : ℕ → ℕ) :
    Tendsto (fun n => fixedGapWorstError.{u} c₀ (B n) (p n) n) atTop (𝓝 0) ↔
      FixedGapUniformConsistency.{u} c₀ B p := by
  simpa only [fixedGapWorstError,FixedGapUniformConsistency,uniformModelClassBound_false] using
    uniformWorstError_tendsto_zero_iff.{u} false c₀ B p

/-- Literal numerical form for the class with full mixed-tensor cancellation. -/
theorem zeroSkewFixedGapWorstError_tendsto_zero_iff (c₀ B : ℝ) (p : ℕ → ℕ) :
    Tendsto (fun n => zeroSkewFixedGapWorstError.{u} c₀ B (p n) n) atTop (𝓝 0) ↔
      ZeroSkewFixedGapUniformConsistency.{u} c₀ B p := by
  simpa only [zeroSkewFixedGapWorstError,ZeroSkewFixedGapUniformConsistency,
    uniformModelClassBound_true] using
    uniformWorstError_tendsto_zero_iff.{u} true c₀ (fun _ => B) p

end
end RectangleCLT.Companion
