import RectangleCLTArxivV1.SupplementalGParallel

/-! Scalar and finite-face closure of the complementary remainder pieces. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capSingleComplementaryConstant : ℝ := 480*Real.exp (1/2)*Real.sqrt (Real.pi/capGaussianExponent)
def capSmallPairComplementaryConstant : ℝ := 7168*Real.exp 6*Real.pi^3
def capLargePairComplementaryConstant : ℝ := 9216*Real.exp 1*Real.pi^3
def capComplementaryConstant : ℝ := max capSingleComplementaryConstant
  (max capSmallPairComplementaryConstant capLargePairComplementaryConstant)

theorem capComplementaryConstant_nonneg : 0 ≤ capComplementaryConstant := by
  have hs : 0 ≤ capSingleComplementaryConstant := by unfold capSingleComplementaryConstant; positivity
  exact hs.trans (le_max_left _ _)

theorem capComplementaryConstant_ge_single : capSingleComplementaryConstant ≤ capComplementaryConstant := le_max_left _ _
theorem capComplementaryConstant_ge_smallPair : capSmallPairComplementaryConstant ≤ capComplementaryConstant :=
  (le_max_left _ _).trans (le_max_right _ _)
theorem capComplementaryConstant_ge_largePair : capLargePairComplementaryConstant ≤ capComplementaryConstant :=
  (le_max_right _ _).trans (le_max_right _ _)

/-- The two actual pair estimates remove the correlation angle. -/
theorem cap_pair_geometric_mean {z C δ r h ν σ : ℝ}
    (hC : 0 ≤ C) (hr : 0 ≤ r) (hh : 0 < h) (hν : 0 < ν) (hσ : 0 < σ)
    (hsmall : |z| ≤ C*δ^2*ν/h^2) (hlarge : |z| ≤ C*r*δ^2/(ν*σ^2)) :
    |z| ≤ C*Real.sqrt r*δ^2/(h*σ) := by
  have hA : 0 ≤ C*δ^2*ν/h^2 := by positivity
  have hB : 0 ≤ C*Real.sqrt r*δ^2/(h*σ) := by positivity
  have hs := mul_le_mul hsmall hlarge (abs_nonneg z) hA
  have he : (C*δ^2*ν/h^2)*(C*r*δ^2/(ν*σ^2)) = (C*Real.sqrt r*δ^2/(h*σ))^2 := by
    field_simp only [hh.ne',hν.ne',hσ.ne']
    simp only [mul_pow]
    rw [Real.sq_sqrt hr]
    ring
  rw [he] at hs
  exact (sq_le_sq₀ (abs_nonneg z) hB).mp (by simpa only [pow_two] using hs)

theorem cap_sum_faces_abs_le {p : ℕ} (s : FaceSmoother p) (F : Face p → ℝ) {B : ℝ}
    (hzero : ∀ f, f ∉ s.faces → F f=0) (hF : ∀ f ∈ s.faces, |F f| ≤ B) :
    |∑ f, F f| ≤ (s.faces.card : ℝ)*B := by
  have he : (∑ f ∈ s.faces, F f) = ∑ f, F f := Finset.sum_subset (Finset.subset_univ s.faces)
    (fun f _ hf => hzero f hf)
  rw [← he]
  calc
    _ ≤ ∑ f ∈ s.faces, |F f| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _f ∈ s.faces, B := Finset.sum_le_sum (fun f hf => hF f hf)
    _ = _ := by simp

theorem cap_sum_pair_faces_abs_le {p : ℕ} (s : FaceSmoother p) (F : Face p → Face p → ℝ) {B : ℝ}
    (hzero : ∀ f g, f ∉ s.faces ∨ g ∉ s.faces → F f g=0)
    (hF : ∀ f ∈ s.faces, ∀ g ∈ s.faces, |F f g| ≤ B) :
    |∑ f, ∑ g, F f g| ≤ (s.faces.card : ℝ)^2*B := by
  have ht := cap_sum_faces_abs_le s (fun f => ∑ g, F f g)
    (fun f hf => Finset.sum_eq_zero (fun g _ => hzero f g (Or.inl hf)))
    (fun f hf => cap_sum_faces_abs_le s (F f) (fun g hg => hzero f g (Or.inr hg)) (hF f hf))
  exact ht.trans_eq (by ring)

theorem cap_seeded_single_contribution_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p) (f : Face p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift| ≤
      capSingleComplementaryConstant*δ^2*(r : ℝ)/(seededSplitGaussianScale ε t)^3 := by
  exact cap_seeded_single_pattern_bound h A hA hunit hr s hband x f hε ht hθ hpos freshY freshW freshShift

theorem cap_seeded_single_sum_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1) (hr : 1 ≤ r)
    (s : FaceSmoother p) (hband : 16*δ ≤ s.bandwidth) (x : Vector p)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0 : ℝ) 1) (hθ : θ ∈ Set.Icc (0 : ℝ) 1)
    (hpos : 0 < t+ε) (freshY freshW freshShift : Bool) :
    |∑ f, capSeededSingleContribution s μ ξ A x ε t θ f freshY freshW freshShift| ≤
      (s.faces.card : ℝ)*(capSingleComplementaryConstant*δ^2*(r : ℝ)/(seededSplitGaussianScale ε t)^3) := by
  apply cap_sum_faces_abs_le
  · intro f hf
    exact cap_seeded_single_inactive s μ ξ A x ε t θ f hf freshY freshW freshShift
  · intro f _
    exact cap_seeded_single_contribution_bound h A hA hunit hr s hband x f hε ht hθ hpos freshY freshW freshShift

end
end RectangleCLTArxivV1
