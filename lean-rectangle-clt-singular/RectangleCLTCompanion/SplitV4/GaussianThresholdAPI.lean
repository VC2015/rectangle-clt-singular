import RectangleCLTCompanion.SplitV4.GaussianThresholdDiagonal

/-! Dimension-independent public hard-threshold derivative API. A unit
normal rules out ambient dimension zero whenever a derivative is indexed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false

theorem gaussianThresholdFirst_eq_normal_section {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdFirst u b j = gaussianPDFReal 0 1 (b j) *
      gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) (b j) := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact gaussianThresholdFirst_eq_section u b j hu hi

theorem gaussianThresholdMixed_eq_two_normal_section {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) (hjl : j ≠ l)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j l = gaussianThresholdMixedSection u b j l := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact gaussianThresholdMixed_eq_section u b j l hjl hu hi

theorem gaussianThreshold_diagonal_formula {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    gaussianThresholdMixed u b j j = -b j * gaussianThresholdFirst u b j -
      ∑ l ∈ Finset.univ.erase j, faceDot (u j) (u l) * gaussianThresholdMixed u b j l := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact gaussianThreshold_diagonal_identity u b j hu hi

theorem gaussianThreshold_mixed_symmetry {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (hu : ∀ j, vectorNormSq (u j) = 1)
    (hi : LinearIndependent ℝ u) (j l : Fin m) :
    gaussianThresholdMixed u b j l = gaussianThresholdMixed u b l j := by
  cases r with
  | zero => have hj := hu j; norm_num [vectorNormSq] at hj
  | succ n => exact gaussianThresholdMixed_symm u b hu hi j l

theorem hasDerivAt_gaussianThresholdCDF_coordinate {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdCDF u (Function.update b j t))
      (gaussianThresholdFirst u (Function.update b j c) j) c := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact hasDerivAt_gaussianThresholdCDF_update_first u b j hu hi c

theorem hasDerivAt_gaussianThresholdFirst_coordinate {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdFirst u (Function.update b l t) j)
      (gaussianThresholdMixed u (Function.update b l c) j l) c := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact hasDerivAt_gaussianThresholdFirst_update_mixed u b j l hu hi c

theorem continuous_gaussianThresholdFirst_of_unit_independent {m r : ℕ}
    (u : Fin m → Vector r) (j : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdFirst u b j) := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact continuous_gaussianThresholdFirst u j hu hi

theorem continuous_gaussianThresholdMixed_of_unit_independent {m r : ℕ}
    (u : Fin m → Vector r) (j l : Fin m)
    (hu : vectorNormSq (u j) = 1) (hi : LinearIndependent ℝ u) :
    Continuous (fun b => gaussianThresholdMixed u b j l) := by
  cases r with
  | zero => norm_num [vectorNormSq] at hu
  | succ n => exact continuous_gaussianThresholdMixed u j l hu hi

end
end RectangleCLT.Companion.SplitV4
