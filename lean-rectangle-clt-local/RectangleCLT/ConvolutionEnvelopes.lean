import RectangleCLT.BernoulliCommonPoint
import RectangleCLT.BoundedEnvelopeShift

/-! Concrete local convolution envelopes obtained by integrating the checked
positive smoother majorants. These give the short-scale input without any
Gaussian face estimate. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

theorem continuous_fourthLocalMajorant (j k l m : Fin p) :
    Continuous (fun x => s.fourthLocalMajorant x j k l m) := by
  have hM (a : Fin p) : Continuous (fun x => (s.weights x).coordinateMass a) :=
    (s.contDiff_coordinateMass_translation a).continuous
  have hD (a b : Fin p) : Continuous (fun x => (s.weights x).diagonalMass a b) :=
    (s.contDiff_diagonalMass_translation a b).continuous
  have hE (a b c : Fin p) : Continuous (fun x => (s.weights x).thirdAbsDiagonalMass a b c) := by
    unfold FaceWeights.thirdAbsDiagonalMass
    split_ifs
    · exact hM a
    · exact continuous_const
  have hK (a b c d : Fin p) : Continuous (fun x => (s.weights x).fourthDiagonalMass a b c d) := by
    unfold FaceWeights.fourthDiagonalMass
    split_ifs
    · exact hM a
    · exact continuous_const
  unfold fourthLocalMajorant FaceWeights.fourthMajorant
  fun_prop

theorem fourthLocalMajorant_le_sum (x : Vector p) (j k l m : Fin p) :
    s.fourthLocalMajorant x j k l m ≤
      ∑ a, ∑ b, ∑ c, ∑ d, s.fourthLocalMajorant x a b c d := by
  have h₁ := Finset.single_le_sum (fun d _ => s.fourthLocalMajorant_nonneg x j k l d)
    (Finset.mem_univ m)
  have h₂ : (∑ d, s.fourthLocalMajorant x j k l d) ≤
      ∑ c, ∑ d, s.fourthLocalMajorant x j k c d := Finset.single_le_sum (fun c _ => Finset.sum_nonneg
    (fun d _ => s.fourthLocalMajorant_nonneg x j k c d)) (Finset.mem_univ l)
  have h₃ : (∑ c, ∑ d, s.fourthLocalMajorant x j k c d) ≤
      ∑ b, ∑ c, ∑ d, s.fourthLocalMajorant x j b c d := Finset.single_le_sum (fun b _ => Finset.sum_nonneg
    (fun c _ => Finset.sum_nonneg (fun d _ => s.fourthLocalMajorant_nonneg x j b c d)))
    (Finset.mem_univ k)
  have h₄ : (∑ b, ∑ c, ∑ d, s.fourthLocalMajorant x j b c d) ≤
      ∑ a, ∑ b, ∑ c, ∑ d, s.fourthLocalMajorant x a b c d := Finset.single_le_sum (fun a _ => Finset.sum_nonneg
    (fun b _ => Finset.sum_nonneg (fun c _ => Finset.sum_nonneg
      (fun d _ => s.fourthLocalMajorant_nonneg x a b c d)))) (Finset.mem_univ j)
  exact h₁.trans (h₂.trans (h₃.trans h₄))

theorem fourthLocalMajorant_le_const (x : Vector p) (j k l m : Fin p) :
    s.fourthLocalMajorant x j k l m ≤ (75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4 := by
  apply (s.fourthLocalMajorant_le_sum x j k l m).trans
  apply (s.sum_fourthLocalMajorant_le_variance x).trans
  have hF : s.F x * (1 - s.F x) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (s.F_le_one x)
        (by linarith [s.F_pos x]) (sub_nonneg.mpr (s.F_le_one x)) (by norm_num)
      _ = _ := one_mul _
  apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (75 * (Real.exp 2) ^ 5) * (s.F x * (1 - s.F x)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hF

theorem integrable_fourthLocalMajorant_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (j k l m : Fin p) :
    Integrable (fun ω => s.fourthLocalMajorant (W ω) j k l m) μ := by
  apply (integrable_const ((75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4)).mono'
    (((s.continuous_fourthLocalMajorant j k l m).measurable.comp hW).aestronglyMeasurable)
  exact ae_of_all _ (fun ω => by
    change ‖s.fourthLocalMajorant (W ω) j k l m‖ ≤ _
    rw [Real.norm_eq_abs, abs_of_nonneg (s.fourthLocalMajorant_nonneg _ j k l m)]
    exact s.fourthLocalMajorant_le_const _ j k l m)

noncomputable def convolutionFourthLocalMajorant (ν : Measure (Vector p))
    (x : Vector p) (j k l m : Fin p) : ℝ :=
  ∫ z, s.fourthLocalMajorant (x + z) j k l m ∂ν

theorem abs_convolutionFourthDerivative_shift_le
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x : Vector p)
    {u : Vector p} (hu : ‖u‖ ≤ s.bandwidth) (j k l m : Fin p) :
    |s.convolutionFourthDerivative ν (x + u) j k l m| ≤
      s.convolutionFourthLocalMajorant ν x j k l m := by
  rw [s.convolutionFourthDerivative_eq_integral]
  have hi := s.integrable_fourthLocalMajorant_comp ν (fun z : Vector p => x + z)
    (measurable_const.add measurable_id) j k l m
  have hb : ∀ᵐ z : Vector p ∂ν,
      ‖s.mixedFourthDerivativeF ((x + u) + z) j k l m‖ ≤
        s.fourthLocalMajorant (x + z) j k l m :=
    ae_of_all _ (fun z => by
      rw [Real.norm_eq_abs]
      have h := s.abs_mixedFourthDerivativeF_shift_le (x + z) hu j k l m
      simpa only [add_right_comm x u z] using h)
  have hn := norm_integral_le_of_norm_le
    (f := fun z : Vector p => s.mixedFourthDerivativeF ((x + u) + z) j k l m)
    (g := fun z : Vector p => s.fourthLocalMajorant (x + z) j k l m) hi hb
  simpa only [Real.norm_eq_abs, convolutionFourthLocalMajorant] using hn


/-- Every entry of the actual integrated positive majorant is nonnegative. -/
theorem convolutionFourthLocalMajorant_nonneg
    (ν : Measure (Vector p)) (x : Vector p) (j k l m : Fin p) :
    0 ≤ s.convolutionFourthLocalMajorant ν x j k l m :=
  integral_nonneg (fun z => s.fourthLocalMajorant_nonneg (x + z) j k l m)

theorem norm_fourthLocalMajorant_le_const (x : Vector p) (j k l m : Fin p) :
    ‖s.fourthLocalMajorant x j k l m‖ ≤ (75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (s.fourthLocalMajorant_nonneg x j k l m)]
  exact s.fourthLocalMajorant_le_const x j k l m

/-- The actual convolution majorant is uniformly bounded under every
probability convolution law, including singular Gaussian laws. -/
theorem norm_convolutionFourthLocalMajorant_le_const
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x : Vector p) (j k l m : Fin p) :
    ‖s.convolutionFourthLocalMajorant ν x j k l m‖ ≤
      (75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4 := by
  have hh := norm_integral_le_of_norm_le_const
    (μ := ν) (f := fun z : Vector p => s.fourthLocalMajorant (x + z) j k l m)
    (ae_of_all _ (fun z => s.norm_fourthLocalMajorant_le_const (x + z) j k l m))
  simpa only [convolutionFourthLocalMajorant, measureReal_univ_eq_one, mul_one] using hh

theorem convolutionFourthLocalMajorant_le_const
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x : Vector p) (j k l m : Fin p) :
    s.convolutionFourthLocalMajorant ν x j k l m ≤
      (75 * (Real.exp 2) ^ 5) / s.bandwidth ^ 4 :=
  (le_abs_self _).trans (by simpa only [Real.norm_eq_abs] using
    s.norm_convolutionFourthLocalMajorant_le_const ν x j k l m)

/-- The concrete convolution majorant is continuous in its base point. -/
theorem continuous_convolutionFourthLocalMajorant
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (j k l m : Fin p) :
    Continuous (fun x => s.convolutionFourthLocalMajorant ν x j k l m) := by
  exact continuous_shiftIntegral_of_bounded ν (fun x => s.fourthLocalMajorant x j k l m)
    (s.continuous_fourthLocalMajorant j k l m) _
    (fun x => s.norm_fourthLocalMajorant_le_const x j k l m)

/-- Actual local-envelope entries may be composed with an arbitrary
measurable random base point without further integrability assumptions. -/
theorem integrable_convolutionFourthLocalMajorant_comp
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (j k l m : Fin p) :
    Integrable (fun ω => s.convolutionFourthLocalMajorant ν (W ω) j k l m) μ :=
  integrable_bounded_test_comp μ W hW _
    (s.continuous_convolutionFourthLocalMajorant ν j k l m) _
    (fun x => s.norm_convolutionFourthLocalMajorant_le_const ν x j k l m)

/-- The finite ordered four-coordinate sum commutes with the actual
convolution-law integral. -/
theorem sum_convolutionFourthLocalMajorant_eq_integral
    (ν : Measure (Vector p)) [IsFiniteMeasure ν] (x : Vector p) :
    (∑ j, ∑ k, ∑ l, ∑ m, s.convolutionFourthLocalMajorant ν x j k l m) =
      ∫ z, ∑ j, ∑ k, ∑ l, ∑ m, s.fourthLocalMajorant (x + z) j k l m ∂ν := by
  have hi (j k l m : Fin p) := s.integrable_fourthLocalMajorant_comp ν
    (fun z : Vector p => x + z) (measurable_const.add measurable_id) j k l m
  symm
  rw [integral_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ => hi j k l m))))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ =>
    integrable_finset_sum Finset.univ (fun l _ =>
      integrable_finset_sum Finset.univ (fun m _ => hi _ k l m))),
    integral_finset_sum Finset.univ (fun l _ =>
      integrable_finset_sum Finset.univ (fun m _ => hi _ _ l m)),
    integral_finset_sum Finset.univ (fun m _ => hi _ _ _ m)]
  rfl


/-- Third-order positive local majorants are continuous as well. -/
theorem continuous_thirdLocalMajorant (j k l : Fin p) :
    Continuous (fun x => s.thirdLocalMajorant x j k l) := by
  have hM (a : Fin p) : Continuous (fun x => (s.weights x).coordinateMass a) :=
    (s.contDiff_coordinateMass_translation a).continuous
  have hD (a b : Fin p) : Continuous (fun x => (s.weights x).diagonalMass a b) :=
    (s.contDiff_diagonalMass_translation a b).continuous
  have hE (a b c : Fin p) : Continuous (fun x => (s.weights x).thirdAbsDiagonalMass a b c) := by
    unfold FaceWeights.thirdAbsDiagonalMass
    split_ifs
    · exact hM a
    · exact continuous_const
  unfold thirdLocalMajorant FaceWeights.thirdMajorant
  fun_prop

theorem thirdLocalMajorant_le_sum (x : Vector p) (j k l : Fin p) :
    s.thirdLocalMajorant x j k l ≤ ∑ a, ∑ b, ∑ c, s.thirdLocalMajorant x a b c := by
  have h₁ := Finset.single_le_sum (fun c _ => s.thirdLocalMajorant_nonneg x j k c)
    (Finset.mem_univ l)
  have h₂ : (∑ c, s.thirdLocalMajorant x j k c) ≤
      ∑ b, ∑ c, s.thirdLocalMajorant x j b c := Finset.single_le_sum
        (fun b _ => Finset.sum_nonneg (fun c _ => s.thirdLocalMajorant_nonneg x j b c))
        (Finset.mem_univ k)
  have h₃ : (∑ b, ∑ c, s.thirdLocalMajorant x j b c) ≤
      ∑ a, ∑ b, ∑ c, s.thirdLocalMajorant x a b c := Finset.single_le_sum
        (fun a _ => Finset.sum_nonneg (fun b _ => Finset.sum_nonneg
          (fun c _ => s.thirdLocalMajorant_nonneg x a b c))) (Finset.mem_univ j)
  exact h₁.trans (h₂.trans h₃)

theorem thirdLocalMajorant_le_const (x : Vector p) (j k l : Fin p) :
    s.thirdLocalMajorant x j k l ≤ (13 * (Real.exp 2) ^ 4) / s.bandwidth ^ 3 := by
  apply (s.thirdLocalMajorant_le_sum x j k l).trans
  apply (s.sum_thirdLocalMajorant_le_variance x).trans
  have hF : s.F x * (1 - s.F x) ≤ 1 := by
    calc
      _ ≤ 1 * 1 := mul_le_mul (s.F_le_one x)
        (by linarith [s.F_pos x]) (sub_nonneg.mpr (s.F_le_one x)) (by norm_num)
      _ = _ := one_mul _
  apply div_le_div_of_nonneg_right _ (pow_nonneg s.bandwidth_pos.le _)
  calc
    _ = (13 * (Real.exp 2) ^ 4) * (s.F x * (1 - s.F x)) := by ring
    _ ≤ _ := mul_le_of_le_one_right (by positivity) hF

theorem norm_thirdLocalMajorant_le_const (x : Vector p) (j k l : Fin p) :
    ‖s.thirdLocalMajorant x j k l‖ ≤ (13 * (Real.exp 2) ^ 4) / s.bandwidth ^ 3 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (s.thirdLocalMajorant_nonneg x j k l)]
  exact s.thirdLocalMajorant_le_const x j k l

theorem integrable_thirdLocalMajorant_comp
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W : Ω → Vector p) (hW : Measurable W) (j k l : Fin p) :
    Integrable (fun ω => s.thirdLocalMajorant (W ω) j k l) μ :=
  integrable_bounded_test_comp μ W hW _ (s.continuous_thirdLocalMajorant j k l) _
    (fun x => s.norm_thirdLocalMajorant_le_const x j k l)

/-- Absolute actual third derivatives are bounded by integrating the positive
majorants; all cancellations inside the convolution are retained until here. -/
theorem sum_abs_convolutionThirdDerivative_le_integral_majorant
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x : Vector p) :
    (∑ j, ∑ k, ∑ l, |s.convolutionThirdDerivative ν x j k l|) ≤
      ∫ z, ∑ j, ∑ k, ∑ l, s.thirdLocalMajorant (x + z) j k l ∂ν := by
  have hi (j k l : Fin p) := s.integrable_thirdLocalMajorant_comp ν
    (fun z : Vector p => x + z) (measurable_const.add measurable_id) j k l
  have hb (j k l : Fin p) : |s.convolutionThirdDerivative ν x j k l| ≤
      ∫ z, s.thirdLocalMajorant (x + z) j k l ∂ν := by
    rw [s.convolutionThirdDerivative_eq_integral]
    have hpoint : ∀ᵐ z : Vector p ∂ν,
        ‖s.mixedThirdDerivativeF (x + z) j k l‖ ≤ s.thirdLocalMajorant (x + z) j k l :=
      ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs]
        have hh := s.abs_mixedThirdDerivativeF_shift_le (x + z)
          (show ‖(0 : Vector p)‖ ≤ s.bandwidth by simpa only [norm_zero] using s.bandwidth_pos.le) j k l
        simpa only [add_zero] using hh)
    have hh := norm_integral_le_of_norm_le
      (f := fun z : Vector p => s.mixedThirdDerivativeF (x + z) j k l)
      (g := fun z : Vector p => s.thirdLocalMajorant (x + z) j k l) (hi j k l) hpoint
    simpa only [Real.norm_eq_abs] using hh
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∫ z, s.thirdLocalMajorant (x + z) j k l ∂ν :=
      Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ => Finset.sum_le_sum fun l _ => hb j k l
    _ = _ := by
      symm
      rw [integral_finset_sum Finset.univ (fun j _ =>
        integrable_finset_sum Finset.univ (fun k _ =>
          integrable_finset_sum Finset.univ (fun l _ => hi j k l)))]
      simp_rw [integral_finset_sum Finset.univ (fun k _ =>
        integrable_finset_sum Finset.univ (fun l _ => hi _ k l)),
        integral_finset_sum Finset.univ (fun l _ => hi _ _ l)]

end RectangleCLT.FaceSmoother
