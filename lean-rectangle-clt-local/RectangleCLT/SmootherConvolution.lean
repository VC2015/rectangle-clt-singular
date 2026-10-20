import RectangleCLT.SmootherHigherDerivatives
import Mathlib.Analysis.Calculus.ParametricIntegral
import Mathlib.Tactic.FunProp

/-! Differentiation of actual probability-shift convolutions of the rational
rectangle smoother. The dominating functions below are integrable constants;
no Gaussian face estimate or concentration assumption is used. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT

/-- Translation convolution against an actual measure. -/
noncomputable def shiftIntegral {p : ℕ} (ν : Measure (Fin p → ℝ))
    (G : (Fin p → ℝ) → ℝ) (x : Fin p → ℝ) : ℝ := ∫ z, G (x + z) ∂ν

/-- An actual ordinary coordinate derivative of a scalar function. -/
noncomputable def coordinatePartial {p : ℕ} (G : (Fin p → ℝ) → ℝ)
    (j : Fin p) (x : Fin p → ℝ) : ℝ :=
  deriv (fun t => G (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t)) 0

private theorem abs_entry_le_total3 {p : ℕ} (A : Fin p → Fin p → Fin p → ℝ)
    (j k l : Fin p) : |A j k l| ≤ ∑ a, ∑ b, ∑ c, |A a b c| := by
  calc
    _ ≤ ∑ c, |A j k c| := Finset.single_le_sum
      (fun c _ => abs_nonneg (A j k c)) (Finset.mem_univ l)
    _ ≤ ∑ b, ∑ c, |A j b c| := Finset.single_le_sum
      (fun b _ => Finset.sum_nonneg (fun c _ => abs_nonneg (A j b c))) (Finset.mem_univ k)
    _ ≤ ∑ a, ∑ b, ∑ c, |A a b c| := Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
        (fun c _ => abs_nonneg (A a b c)))) (Finset.mem_univ j)

private theorem abs_entry_le_total4 {p : ℕ} (A : Fin p → Fin p → Fin p → Fin p → ℝ)
    (j k l m : Fin p) : |A j k l m| ≤ ∑ a, ∑ b, ∑ c, ∑ d, |A a b c d| := by
  calc
    _ ≤ ∑ d, |A j k l d| := Finset.single_le_sum
      (fun d _ => abs_nonneg (A j k l d)) (Finset.mem_univ m)
    _ ≤ ∑ c, ∑ d, |A j k c d| := Finset.single_le_sum
      (fun c _ => Finset.sum_nonneg (fun d _ => abs_nonneg (A j k c d))) (Finset.mem_univ l)
    _ ≤ ∑ b, ∑ c, ∑ d, |A j b c d| := Finset.single_le_sum
      (fun b _ => Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
        (fun d _ => abs_nonneg (A j b c d)))) (Finset.mem_univ k)
    _ ≤ ∑ a, ∑ b, ∑ c, ∑ d, |A a b c d| := Finset.single_le_sum
      (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
        (fun c _ => Finset.sum_nonneg (fun d _ => abs_nonneg (A a b c d))))) (Finset.mem_univ j)

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

@[fun_prop] theorem continuous_normalDot (f : Face p) : Continuous (normalDot f) := by
  change Continuous (fun x : Fin p → ℝ => if f.2 then x f.1 else -x f.1)
  cases hf : f.2
  · simpa only [hf, Bool.false_eq_true, ↓reduceIte] using
      (continuous_apply f.1 : Continuous (fun x : Fin p → ℝ => x f.1)).neg
  · simpa only [hf, ↓reduceIte] using
      (continuous_apply f.1 : Continuous (fun x : Fin p → ℝ => x f.1))

@[fun_prop] theorem continuous_faceScore (f : Face p) : Continuous (s.faceScore f) :=
  (continuous_normalDot f).sub continuous_const

@[fun_prop] theorem continuous_weight (f : Face p) :
    Continuous (fun x => (s.weights x).weight f) := by
  by_cases hf : f ∈ s.faces
  · simpa only [weights, hf, ↓reduceIte] using
      ((s.continuous_faceScore f).div_const s.bandwidth).rexp
  · simpa only [weights, hf, ↓reduceIte] using
      (continuous_const : Continuous (fun _ : Fin p → ℝ => (0 : ℝ)))

@[fun_prop] theorem continuous_T : Continuous (fun x => (s.weights x).T) := by
  unfold FaceWeights.T
  exact continuous_finset_sum _ (fun f _ => s.continuous_weight f)

@[fun_prop] theorem continuous_F : Continuous s.F :=
  continuous_const.div (continuous_const.add s.continuous_T)
    (fun x => ne_of_gt (s.weights x).denominator_pos)

@[fun_prop] theorem continuous_pi (f : Face p) :
    Continuous (fun x => (s.weights x).pi f) :=
  (s.continuous_weight f).div (continuous_const.add s.continuous_T)
    (fun x => ne_of_gt (s.weights x).denominator_pos)

@[fun_prop] theorem continuous_v (j : Fin p) : Continuous (fun x => (s.weights x).v j) :=
  (s.continuous_pi (j, true)).sub (s.continuous_pi (j, false))

@[fun_prop] theorem continuous_coordinateMass (j : Fin p) :
    Continuous (fun x => (s.weights x).coordinateMass j) :=
  (s.continuous_pi (j, true)).add (s.continuous_pi (j, false))

@[fun_prop] theorem continuous_diagonalMass (j k : Fin p) :
    Continuous (fun x => (s.weights x).diagonalMass j k) := by
  unfold FaceWeights.diagonalMass
  split_ifs
  · exact s.continuous_coordinateMass j
  · exact continuous_const

@[fun_prop] theorem continuous_firstDerivative (j : Fin p) :
    Continuous (fun x => s.coordinateDerivativeF x j) := by
  simp_rw [s.coordinateDerivativeF_eq]
  fun_prop

@[fun_prop] theorem continuous_secondDerivative (j k : Fin p) :
    Continuous (fun x => s.mixedSecondDerivativeF x j k) := by
  simp_rw [s.mixedSecondDerivativeF_eq]
  fun_prop

@[fun_prop] theorem continuous_thirdDiagonalMass (j k l : Fin p) :
    Continuous (fun x => (s.weights x).thirdDiagonalMass j k l) := by
  unfold FaceWeights.thirdDiagonalMass
  split_ifs
  · exact s.continuous_v j
  · exact continuous_const

@[fun_prop] theorem continuous_fourthDiagonalMass (j k l m : Fin p) :
    Continuous (fun x => (s.weights x).fourthDiagonalMass j k l m) := by
  unfold FaceWeights.fourthDiagonalMass
  split_ifs
  · exact s.continuous_coordinateMass j
  · exact continuous_const

@[fun_prop] theorem continuous_thirdDerivative (j k l : Fin p) :
    Continuous (fun x => s.mixedThirdDerivativeF x j k l) := by
  simp_rw [s.mixedThirdDerivativeF_eq]
  unfold FaceWeights.thirdFactor
  fun_prop

@[fun_prop] theorem continuous_fourthDerivative (j k l m : Fin p) :
    Continuous (fun x => s.mixedFourthDerivativeF x j k l m) := by
  simp_rw [s.mixedFourthDerivativeF_eq]
  unfold FaceWeights.fourthFactor
  fun_prop

theorem variance_le_one (x : Fin p → ℝ) : s.F x * (1 - s.F x) ≤ 1 := by
  nlinarith [s.F_le_one x, sq_nonneg (s.F x)]

theorem norm_F_le_one (x : Fin p → ℝ) : ‖s.F x‖ ≤ 1 := by
  simpa only [Real.norm_eq_abs, abs_of_pos (s.F_pos x)] using s.F_le_one x

theorem norm_firstDerivative_le (x : Fin p → ℝ) (j : Fin p) :
    ‖s.coordinateDerivativeF x j‖ ≤ 1 / s.bandwidth := by
  have he : |s.coordinateDerivativeF x j| ≤ ∑ k, |s.coordinateDerivativeF x k| :=
    Finset.single_le_sum (f := fun k => |s.coordinateDerivativeF x k|)
      (fun k _ => abs_nonneg _) (Finset.mem_univ j)
  have hs := s.sum_abs_deriv_F_coordinate_le_variance x
  have hb := div_le_div_of_nonneg_right (s.variance_le_one x) s.bandwidth_pos.le
  exact he.trans (hs.trans hb)

theorem norm_secondDerivative_le (x : Fin p → ℝ) (j k : Fin p) :
    ‖s.mixedSecondDerivativeF x j k‖ ≤ 3 / s.bandwidth ^ 2 := by
  have h1 : |s.mixedSecondDerivativeF x j k| ≤ ∑ l, |s.mixedSecondDerivativeF x j l| :=
    Finset.single_le_sum (f := fun l => |s.mixedSecondDerivativeF x j l|)
      (fun l _ => abs_nonneg _) (Finset.mem_univ k)
  have h2 : (∑ l, |s.mixedSecondDerivativeF x j l|) ≤
      ∑ i, ∑ l, |s.mixedSecondDerivativeF x i l| :=
    Finset.single_le_sum (f := fun i => ∑ l, |s.mixedSecondDerivativeF x i l|)
      (fun i _ => Finset.sum_nonneg (fun l _ => abs_nonneg _))
      (Finset.mem_univ j)
  have hn : 3 * s.F x * (1 - s.F x) ≤ 3 := by nlinarith [s.variance_le_one x]
  exact (h1.trans h2).trans ((s.sum_abs_mixedSecondDerivativeF_le_variance x).trans
    (div_le_div_of_nonneg_right hn (sq_nonneg _)))

theorem norm_thirdDerivative_le (x : Fin p → ℝ) (j k l : Fin p) :
    ‖s.mixedThirdDerivativeF x j k l‖ ≤ 13 / s.bandwidth ^ 3 := by
  have he := abs_entry_le_total3 (s.mixedThirdDerivativeF x) j k l
  have hn : 13 * s.F x * (1 - s.F x) ≤ 13 := by nlinarith [s.variance_le_one x]
  exact he.trans ((s.sum_abs_mixedThirdDerivativeF_le_variance x).trans
    (div_le_div_of_nonneg_right hn (pow_nonneg s.bandwidth_pos.le 3)))

theorem norm_fourthDerivative_le (x : Fin p → ℝ) (j k l m : Fin p) :
    ‖s.mixedFourthDerivativeF x j k l m‖ ≤ 75 / s.bandwidth ^ 4 := by
  have he := abs_entry_le_total4 (s.mixedFourthDerivativeF x) j k l m
  have hn : 75 * s.F x * (1 - s.F x) ≤ 75 := by nlinarith [s.variance_le_one x]
  exact he.trans ((s.sum_abs_mixedFourthDerivativeF_le_variance x).trans
    (div_le_div_of_nonneg_right hn (pow_nonneg s.bandwidth_pos.le 4)))

theorem hasDerivAt_F_coordinate_normalized (x : Fin p → ℝ) (j : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.F (line x (coordinateDirection j) r))
      (s.coordinateDerivativeF (line x (coordinateDirection j) t) j) t := by
  simpa only [s.coordinateDerivativeF_eq, directionalMean_coordinate] using
    s.hasDerivAt_F_line x (coordinateDirection j) t

theorem hasDerivAt_firstDerivative_coordinate (x : Fin p → ℝ) (j k : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.coordinateDerivativeF (line x (coordinateDirection k) r) j)
      (s.mixedSecondDerivativeF (line x (coordinateDirection k) t) j k) t := by
  have h := s.hasDerivAt_coordinateDerivativeF_line x (coordinateDirection k) j t
  by_cases hjk : j = k <;>
    simpa only [s.mixedSecondDerivativeF_eq, directionalMean_coordinate, coordinateDirection,
      FaceWeights.diagonalMass, hjk, ↓reduceIte, mul_one, mul_zero] using h

theorem hasDerivAt_secondDerivative_coordinate (x : Fin p → ℝ) (j k l : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.mixedSecondDerivativeF (line x (coordinateDirection l) r) j k)
      (s.mixedThirdDerivativeF (line x (coordinateDirection l) t) j k l) t := by
  simpa only [s.mixedThirdDerivativeF_eq] using
    s.hasDerivAt_mixedSecondDerivativeF_coordinate x j k l t

theorem hasDerivAt_thirdDerivative_coordinate (x : Fin p → ℝ)
    (j k l m : Fin p) (t : ℝ) :
    HasDerivAt (fun r => s.mixedThirdDerivativeF (line x (coordinateDirection m) r) j k l)
      (s.mixedFourthDerivativeF (line x (coordinateDirection m) t) j k l m) t := by
  simpa only [s.mixedFourthDerivativeF_eq] using
    s.hasDerivAt_mixedThirdDerivativeF_coordinate x j k l m t

theorem line_add_shift (x y z : Fin p → ℝ) (t : ℝ) :
    line x y t + z = line (x + z) y t := by
  funext j
  simp only [line, Pi.add_apply]
  ring

end FaceSmoother

/-- Bounded continuous kernels can be integrated against every probability law. -/
theorem integrable_shift_of_continuous_bounded {p : ℕ}
    (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν]
    (G : (Fin p → ℝ) → ℝ) (C : ℝ) (hG : Continuous G)
    (hbound : ∀ x, ‖G x‖ ≤ C) (x : Fin p → ℝ) :
    Integrable (fun z => G (x + z)) ν :=
  (integrable_const C).mono'
    (hG.comp (continuous_const.add continuous_id)).aestronglyMeasurable
    (ae_of_all ν (fun z => hbound (x + z)))

/-- Dominated differentiation under a probability-shift integral. All the
regularity and uniform dominating bounds are explicit hypotheses on concrete
kernels; later theorems discharge them for the actual smoother derivatives. -/
theorem hasDerivAt_shiftIntegral_coordinate {p : ℕ}
    (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν]
    (G D : (Fin p → ℝ) → ℝ) (C₀ C₁ : ℝ) (j : Fin p)
    (hG : Continuous G) (hD : Continuous D)
    (hGbound : ∀ x, ‖G x‖ ≤ C₀) (hDbound : ∀ x, ‖D x‖ ≤ C₁)
    (hderiv : ∀ x t, HasDerivAt
      (fun r => G (FaceSmoother.line x (FaceSmoother.coordinateDirection j) r))
      (D (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t)) t)
    (x : Fin p → ℝ) :
    HasDerivAt (fun t => shiftIntegral ν G
      (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t))
      (shiftIntegral ν D x) 0 := by
  have hi := integrable_shift_of_continuous_bounded ν G C₀ hG hGbound x
  have h := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := ν) (bound := fun _ => C₁) (ε := 1)
    (F := fun t z => G (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t + z))
    (F' := fun t z => D (FaceSmoother.line x (FaceSmoother.coordinateDirection j) t + z))
    (x₀ := (0 : ℝ)) (by norm_num)
    (Filter.Eventually.of_forall (fun t =>
      (hG.comp (continuous_const.add continuous_id)).aestronglyMeasurable))
    (by simpa only [FaceSmoother.line_zero] using hi)
    ((hD.comp (continuous_const.add continuous_id)).aestronglyMeasurable)
    (ae_of_all ν (fun z t _ => hDbound _)) (integrable_const C₁)
    (ae_of_all ν (fun z t _ => by
      simpa only [FaceSmoother.line_add_shift] using hderiv (x + z) t))
  simpa only [FaceSmoother.line_zero, shiftIntegral] using h.2

theorem norm_shiftIntegral_le {p : ℕ}
    (ν : Measure (Fin p → ℝ)) [IsProbabilityMeasure ν]
    (G : (Fin p → ℝ) → ℝ) (C : ℝ) (hbound : ∀ x, ‖G x‖ ≤ C) (x : Fin p → ℝ) :
    ‖shiftIntegral ν G x‖ ≤ C := by
  simpa only [shiftIntegral, measureReal_univ_eq_one, mul_one] using
    (norm_integral_le_of_norm_le_const (μ := ν) (ae_of_all ν (fun z => hbound (x + z))))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p) (ν : Measure (Fin p → ℝ))

/-- Convolution of the actual smoother with a shift law. -/
noncomputable def convolution (x : Fin p → ℝ) : ℝ := shiftIntegral ν s.F x

noncomputable def convolutionFirstDerivative (x : Fin p → ℝ) (j : Fin p) : ℝ :=
  coordinatePartial (s.convolution ν) j x

noncomputable def convolutionSecondDerivative (x : Fin p → ℝ) (j k : Fin p) : ℝ :=
  coordinatePartial (fun y => s.convolutionFirstDerivative ν y j) k x

noncomputable def convolutionThirdDerivative (x : Fin p → ℝ) (j k l : Fin p) : ℝ :=
  coordinatePartial (fun y => s.convolutionSecondDerivative ν y j k) l x

noncomputable def convolutionFourthDerivative (x : Fin p → ℝ) (j k l m : Fin p) : ℝ :=
  coordinatePartial (fun y => s.convolutionThirdDerivative ν y j k l) m x

variable [IsProbabilityMeasure ν]

theorem integrable_F_shift (x : Fin p → ℝ) : Integrable (fun z => s.F (x + z)) ν :=
  integrable_shift_of_continuous_bounded ν s.F 1 s.continuous_F s.norm_F_le_one x

theorem integrable_firstDerivative_shift (x : Fin p → ℝ) (j : Fin p) :
    Integrable (fun z => s.coordinateDerivativeF (x + z) j) ν :=
  integrable_shift_of_continuous_bounded ν (fun y => s.coordinateDerivativeF y j)
    (1 / s.bandwidth) (s.continuous_firstDerivative j) (fun y => s.norm_firstDerivative_le y j) x

theorem integrable_secondDerivative_shift (x : Fin p → ℝ) (j k : Fin p) :
    Integrable (fun z => s.mixedSecondDerivativeF (x + z) j k) ν :=
  integrable_shift_of_continuous_bounded ν (fun y => s.mixedSecondDerivativeF y j k)
    (3 / s.bandwidth ^ 2) (s.continuous_secondDerivative j k)
    (fun y => s.norm_secondDerivative_le y j k) x

theorem integrable_thirdDerivative_shift (x : Fin p → ℝ) (j k l : Fin p) :
    Integrable (fun z => s.mixedThirdDerivativeF (x + z) j k l) ν :=
  integrable_shift_of_continuous_bounded ν (fun y => s.mixedThirdDerivativeF y j k l)
    (13 / s.bandwidth ^ 3) (s.continuous_thirdDerivative j k l)
    (fun y => s.norm_thirdDerivative_le y j k l) x

theorem integrable_fourthDerivative_shift (x : Fin p → ℝ) (j k l m : Fin p) :
    Integrable (fun z => s.mixedFourthDerivativeF (x + z) j k l m) ν :=
  integrable_shift_of_continuous_bounded ν (fun y => s.mixedFourthDerivativeF y j k l m)
    (75 / s.bandwidth ^ 4) (s.continuous_fourthDerivative j k l m)
    (fun y => s.norm_fourthDerivative_le y j k l m) x

/-- First actual coordinate derivatives commute with the probability convolution. -/
theorem convolutionFirstDerivative_eq_integral (x : Fin p → ℝ) (j : Fin p) :
    s.convolutionFirstDerivative ν x j = ∫ z, s.coordinateDerivativeF (x + z) j ∂ν :=
  (hasDerivAt_shiftIntegral_coordinate ν s.F (fun y => s.coordinateDerivativeF y j)
    1 (1 / s.bandwidth) j s.continuous_F (s.continuous_firstDerivative j)
    s.norm_F_le_one (fun y => s.norm_firstDerivative_le y j)
    (fun y t => s.hasDerivAt_F_coordinate_normalized y j t) x).deriv

/-- Second actual mixed coordinate derivatives commute with convolution. -/
theorem convolutionSecondDerivative_eq_integral (x : Fin p → ℝ) (j k : Fin p) :
    s.convolutionSecondDerivative ν x j k = ∫ z, s.mixedSecondDerivativeF (x + z) j k ∂ν := by
  change deriv (fun t => s.convolutionFirstDerivative ν
    (line x (coordinateDirection k) t) j) 0 = _
  simp_rw [s.convolutionFirstDerivative_eq_integral]
  exact (hasDerivAt_shiftIntegral_coordinate ν (fun y => s.coordinateDerivativeF y j)
    (fun y => s.mixedSecondDerivativeF y j k) (1 / s.bandwidth) (3 / s.bandwidth ^ 2) k
    (s.continuous_firstDerivative j) (s.continuous_secondDerivative j k)
    (fun y => s.norm_firstDerivative_le y j) (fun y => s.norm_secondDerivative_le y j k)
    (fun y t => s.hasDerivAt_firstDerivative_coordinate y j k t) x).deriv

/-- Third actual mixed coordinate derivatives commute with convolution. -/
theorem convolutionThirdDerivative_eq_integral (x : Fin p → ℝ) (j k l : Fin p) :
    s.convolutionThirdDerivative ν x j k l = ∫ z, s.mixedThirdDerivativeF (x + z) j k l ∂ν := by
  change deriv (fun t => s.convolutionSecondDerivative ν
    (line x (coordinateDirection l) t) j k) 0 = _
  simp_rw [s.convolutionSecondDerivative_eq_integral]
  exact (hasDerivAt_shiftIntegral_coordinate ν (fun y => s.mixedSecondDerivativeF y j k)
    (fun y => s.mixedThirdDerivativeF y j k l) (3 / s.bandwidth ^ 2) (13 / s.bandwidth ^ 3) l
    (s.continuous_secondDerivative j k) (s.continuous_thirdDerivative j k l)
    (fun y => s.norm_secondDerivative_le y j k) (fun y => s.norm_thirdDerivative_le y j k l)
    (fun y t => s.hasDerivAt_secondDerivative_coordinate y j k l t) x).deriv

/-- Fourth actual mixed coordinate derivatives commute with convolution. -/
theorem convolutionFourthDerivative_eq_integral (x : Fin p → ℝ) (j k l m : Fin p) :
    s.convolutionFourthDerivative ν x j k l m =
      ∫ z, s.mixedFourthDerivativeF (x + z) j k l m ∂ν := by
  change deriv (fun t => s.convolutionThirdDerivative ν
    (line x (coordinateDirection m) t) j k l) 0 = _
  simp_rw [s.convolutionThirdDerivative_eq_integral]
  exact (hasDerivAt_shiftIntegral_coordinate ν (fun y => s.mixedThirdDerivativeF y j k l)
    (fun y => s.mixedFourthDerivativeF y j k l m) (13 / s.bandwidth ^ 3) (75 / s.bandwidth ^ 4) m
    (s.continuous_thirdDerivative j k l) (s.continuous_fourthDerivative j k l m)
    (fun y => s.norm_thirdDerivative_le y j k l) (fun y => s.norm_fourthDerivative_le y j k l m)
    (fun y t => s.hasDerivAt_thirdDerivative_coordinate y j k l m t) x).deriv

theorem norm_convolutionFirstDerivative_le (x : Fin p → ℝ) (j : Fin p) :
    ‖s.convolutionFirstDerivative ν x j‖ ≤ 1 / s.bandwidth := by
  rw [s.convolutionFirstDerivative_eq_integral]
  exact norm_shiftIntegral_le ν (fun y => s.coordinateDerivativeF y j) _
    (fun y => s.norm_firstDerivative_le y j) x

theorem norm_convolutionSecondDerivative_le (x : Fin p → ℝ) (j k : Fin p) :
    ‖s.convolutionSecondDerivative ν x j k‖ ≤ 3 / s.bandwidth ^ 2 := by
  rw [s.convolutionSecondDerivative_eq_integral]
  exact norm_shiftIntegral_le ν (fun y => s.mixedSecondDerivativeF y j k) _
    (fun y => s.norm_secondDerivative_le y j k) x

theorem norm_convolutionThirdDerivative_le (x : Fin p → ℝ) (j k l : Fin p) :
    ‖s.convolutionThirdDerivative ν x j k l‖ ≤ 13 / s.bandwidth ^ 3 := by
  rw [s.convolutionThirdDerivative_eq_integral]
  exact norm_shiftIntegral_le ν (fun y => s.mixedThirdDerivativeF y j k l) _
    (fun y => s.norm_thirdDerivative_le y j k l) x

theorem norm_convolutionFourthDerivative_le (x : Fin p → ℝ) (j k l m : Fin p) :
    ‖s.convolutionFourthDerivative ν x j k l m‖ ≤ 75 / s.bandwidth ^ 4 := by
  rw [s.convolutionFourthDerivative_eq_integral]
  exact norm_shiftIntegral_le ν (fun y => s.mixedFourthDerivativeF y j k l m) _
    (fun y => s.norm_fourthDerivative_le y j k l m) x

end FaceSmoother

end RectangleCLT
