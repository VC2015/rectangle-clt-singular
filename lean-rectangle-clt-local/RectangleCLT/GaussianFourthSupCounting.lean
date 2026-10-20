import RectangleCLT.SharpMasterAssembly
import RectangleCLT.GaussianFourthAssembly
import RectangleCLT.GaussianFourthSelectorBounds

/-! Canonical equality-pattern counting for separate local suprema of the
actual Gaussian-convolved fourth derivatives. No supremum is interchanged
with a tensor sum or a probability expectation. -/

open MeasureTheory Set
open scoped BigOperators

universe u

namespace RectangleCLT.FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

/-- An explicit bound uniform throughout the actual local cube bounds its
canonical coordinate supremum. Nonnegative radius ensures a nonempty cube. -/
theorem localConvolutionFourthSup_le_of_uniform
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r)
    (x : Vector p) (t : ℝ) (j k l m : Fin p) (H : ℝ)
    (hH : ∀ u : Vector p, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m| ≤ H) :
    s.localConvolutionFourthSup A r x t j k l m ≤ H := by
  apply csSup_le
  · exact ⟨_, 0, by simpa only [Metric.mem_closedBall, dist_self] using hr, rfl⟩
  · rintro y ⟨v, hv, rfl⟩
    exact hH v (by simpa only [Metric.mem_closedBall, dist_zero_right] using hv)

theorem localConvolutionFourthSup_swap_first_two
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m = s.localConvolutionFourthSup A r x t k j l m := by
  have hf : (fun u : Vector p =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m|) =
      (fun u : Vector p =>
        |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) k j l m|) :=
    funext (fun u => congrArg abs (s.convolutionFourthDerivative_swap_first_two
      (Real.sqrt t • A) (x + u) j k l m))
  exact congrArg (fun f : Vector p → ℝ => sSup (f '' Metric.closedBall 0 r)) hf

theorem localConvolutionFourthSup_swap_middle_two
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m = s.localConvolutionFourthSup A r x t j l k m := by
  have hf : (fun u : Vector p =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m|) =
      (fun u : Vector p =>
        |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j l k m|) :=
    funext (fun u => congrArg abs (s.convolutionFourthDerivative_swap_middle_two
      (Real.sqrt t • A) (x + u) j k l m))
  exact congrArg (fun f : Vector p → ℝ => sSup (f '' Metric.closedBall 0 r)) hf

theorem localConvolutionFourthSup_swap_last_two
    (A : Matrix (Fin p) (Fin p) ℝ) (r : ℝ) (x : Vector p) (t : ℝ) (j k l m : Fin p) :
    s.localConvolutionFourthSup A r x t j k l m = s.localConvolutionFourthSup A r x t j k m l := by
  have hf : (fun u : Vector p =>
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m|) =
      (fun u : Vector p =>
        |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k m l|) :=
    funext (fun u => congrArg abs (s.convolutionFourthDerivative_swap_last_two
      (Real.sqrt t • A) (x + u) j k l m))
  exact congrArg (fun f : Vector p → ℝ => sSup (f '' Metric.closedBall 0 r)) hf

/-- Uniform canonical coordinate caps control the sum of the separate actual
local suprema with the universal position counts `1,4,3,6,1`. -/
theorem sum_localConvolutionFourthSup_le_of_uniform_canonical_bounds
    (A : Matrix (Fin p) (Fin p) ℝ) {r : ℝ} (hr : 0 ≤ r) (x : Vector p) (t : ℝ)
    (M4 : Fin p → ℝ) (M31 M22 : Fin p → Fin p → ℝ)
    (M211 : Fin p → Fin p → Fin p → ℝ)
    (M1111 : Fin p → Fin p → Fin p → Fin p → ℝ)
    (h4 : ∀ a, 0 ≤ M4 a) (h31 : ∀ a b, 0 ≤ M31 a b)
    (h22 : ∀ a b, 0 ≤ M22 a b) (h211 : ∀ a b c, 0 ≤ M211 a b c)
    (h1111 : ∀ a b c d, 0 ≤ M1111 a b c d)
    (hf4 : ∀ a u, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) a a a a| ≤ M4 a)
    (hf31 : ∀ a b, a ≠ b → ∀ u, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) a a a b| ≤ M31 a b)
    (hf22 : ∀ a b, a ≠ b → ∀ u, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) a a b b| ≤ M22 a b)
    (hf211 : ∀ a b c, a ≠ b → a ≠ c → b ≠ c → ∀ u, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) a a b c| ≤ M211 a b c)
    (hf1111 : ∀ a b c d, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d →
      ∀ u, ‖u‖ ≤ r →
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) a b c d| ≤ M1111 a b c d) :
    (∑ a, ∑ b, ∑ c, ∑ d, s.localConvolutionFourthSup A r x t a b c d) ≤
      (∑ a, M4 a) + 4 * (∑ a, ∑ b, M31 a b) + 3 * (∑ a, ∑ b, M22 a b) +
        6 * (∑ a, ∑ b, ∑ c, M211 a b c) + ∑ a, ∑ b, ∑ c, ∑ d, M1111 a b c d := by
  exact sum_symmetric_fourth_le
    (s.localConvolutionFourthSup A r x t)
    (s.localConvolutionFourthSup_swap_first_two A r x t)
    (s.localConvolutionFourthSup_swap_middle_two A r x t)
    (s.localConvolutionFourthSup_swap_last_two A r x t)
    M4 M31 M22 M211 M1111 h4 h31 h22 h211 h1111
    (fun a => s.localConvolutionFourthSup_le_of_uniform A hr x t a a a a (M4 a) (hf4 a))
    (fun a b hab => s.localConvolutionFourthSup_le_of_uniform A hr x t a a a b (M31 a b) (hf31 a b hab))
    (fun a b hab => s.localConvolutionFourthSup_le_of_uniform A hr x t a a b b (M22 a b) (hf22 a b hab))
    (fun a b c hab hac hbc => s.localConvolutionFourthSup_le_of_uniform A hr x t a a b c (M211 a b c)
      (hf211 a b c hab hac hbc))
    (fun a b c d hab hac had hbc hbd hcd =>
      s.localConvolutionFourthSup_le_of_uniform A hr x t a b c d (M1111 a b c d)
        (hf1111 a b c d hab hac had hbc hbd hcd))

/-- Uniform entrywise bounds by an explicit integrable envelope transfer to
the actual selector-weighted expectation of the separate local suprema. -/
theorem sharpFourthAverage_le_selectorEnvelope_of_uniform
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ x u : Vector p, ‖u‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m| ≤ H x j k l m)
    (hHi : ∀ mask : Kane.Cube n, Integrable (fun ω => ∑ j, ∑ k, ∑ l, ∑ m,
      H (0 + thinningScale t • maskObservationSum ξ mask ω) j k l m) μ) :
    s.sharpFourthAverage μ ξ A δ t ≤ selectorFourthEnvelopeAverage μ ξ 0 t H := by
  rw [s.sharpFourthAverage_eq_selectorEnvelope μ ξ hξ A hδ t]
  unfold selectorFourthEnvelopeAverage
  apply Finset.sum_le_sum
  intro mask _
  apply mul_le_mul_of_nonneg_left _
    (Kane.maskWeight_nonneg (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) mask)
  let W : Ω → Vector p := fun ω => 0 + thinningScale t • maskObservationSum ξ mask ω
  have hW : Measurable W := measurable_const.add
    (measurable_const.smul (measurable_maskObservationSum ξ hξ mask))
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ by positivity) t μ W hW j k l m))))
  apply integral_mono hi (hHi mask)
  intro ω
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
    Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
      s.localConvolutionFourthSup_le_of_uniform A (show 0 ≤ 4 * δ by positivity)
        (W ω) t j k l m (H (W ω) j k l m) (fun u hu => hH (W ω) u hu j k l m)


/-- The same transfer directly under the actual retained-array probability
law. Only the explicit comparison envelope needs an integrability premise. -/
theorem sharpFourthAverage_le_integral_envelope_of_uniform
    {Ω : Type u} [MeasurableSpace Ω] {n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) {δ t : ℝ} (hδ : 0 ≤ δ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (H : Vector p → Fin p → Fin p → Fin p → Fin p → ℝ)
    (hH : ∀ x u : Vector p, ‖u‖ ≤ 4 * δ → ∀ j k l m,
      |s.convolutionFourthDerivative (gaussianLaw (Real.sqrt t • A)) (x + u) j k l m| ≤ H x j k l m)
    (hHi : Integrable (fun b : Fin n → Vector p => ∑ j, ∑ k, ∑ l, ∑ m,
      H (arraySum b) j k l m) (bernoulliArrayLaw μ ξ t)) :
    s.sharpFourthAverage μ ξ A δ t ≤
      ∫ b, ∑ j, ∑ k, ∑ l, ∑ m, H (arraySum b) j k l m ∂bernoulliArrayLaw μ ξ t := by
  letI : IsProbabilityMeasure (bernoulliArrayLaw μ ξ t) :=
    bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  rw [s.sharpFourthAverage_eq_integral_bernoulliArrayLaw μ ξ hξ A hδ ht ht1]
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      integrable_finset_sum Finset.univ (fun l _ =>
        integrable_finset_sum Finset.univ (fun m _ =>
          s.integrable_localConvolutionFourthSup_comp A (show 0 ≤ 4 * δ by positivity) t
            (bernoulliArrayLaw μ ξ t) arraySum (measurable_arraySum p n) j k l m))))
  apply integral_mono hi hHi
  intro b
  exact Finset.sum_le_sum fun j _ => Finset.sum_le_sum fun k _ =>
    Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
      s.localConvolutionFourthSup_le_of_uniform A (show 0 ≤ 4 * δ by positivity)
        (arraySum b) t j k l m (H (arraySum b) j k l m)
        (fun u hu => hH (arraySum b) u hu j k l m)

end RectangleCLT.FaceSmoother
