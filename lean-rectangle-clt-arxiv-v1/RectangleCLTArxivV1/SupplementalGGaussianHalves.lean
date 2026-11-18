import RectangleCLTArxivV1.SupplementalGSeededBase
import RectangleCLTCompanion.SubexponentialGaussian

/-! The two independent Gaussian halves can be collapsed before applying
the unconditional whole-point small-box estimate, with rectangular factors. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_gaussian_halves_map_rectangular {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    ((standardGaussian r).prod (standardGaussian r)).map (fun z =>
      (seededSplitGaussianScale ε t • A).mulVec z.1+
      (seededSplitGaussianScale ε t • A).mulVec z.2) =
      RectangleCLT.Companion.rectangularGaussianLaw (Real.sqrt (t+ε) • A) := by
  let σ := seededSplitGaussianScale ε t
  let I : Matrix (Fin r) (Fin r) ℝ := 1
  have hV : Measurable (σ • I).mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hl := map_sum_standardGaussian_factor (standardGaussian r) (σ • I).mulVec hV (σ • I)
  change ((standardGaussian r).prod (standardGaussian r)).map
      (fun z => (σ • I).mulVec z.1+(σ • I).mulVec z.2) =
      Measure.conv (gaussianLaw (σ • I)) (gaussianLaw (σ • I)) at hl
  rw [seededGaussianHalves_conv I hε ht] at hl
  have hA : Measurable A.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  have hmap := congrArg (fun ν : Measure (Vector r) => ν.map A.mulVec) hl
  dsimp only at hmap
  have hf : Measurable (fun z : Vector r × Vector r => (σ • I).mulVec z.1+(σ • I).mulVec z.2) :=
    (hV.comp measurable_fst).add (hV.comp measurable_snd)
  rw [Measure.map_map hA hf] at hmap
  have hrhs : (gaussianLaw (Real.sqrt (t+ε) • I)).map A.mulVec =
      RectangleCLT.Companion.rectangularGaussianLaw (Real.sqrt (t+ε) • A) := by
    unfold gaussianLaw RectangleCLT.Companion.rectangularGaussianLaw
    rw [Measure.map_map hA (by fun_prop)]
    congr 1
    funext g
    simp only [Function.comp_apply,I,Matrix.smul_mulVec_assoc,Matrix.one_mulVec,Matrix.mulVec_smul]
  rw [hrhs] at hmap
  convert hmap using 1
  congr 1
  funext z
  simp only [Function.comp_apply,Matrix.mulVec_add,Matrix.smul_mulVec_assoc,
    Matrix.mulVec_smul,I,σ,Matrix.one_mulVec]

/-- Actual bounded tests have equal iterated expectations under the two
Gaussian halves and the whole Gaussian. -/
theorem cap_gaussian_halves_integral_rectangular {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t)
    (F : Vector p → ℝ) (hF : Measurable F) (hFb : ∃ C : ℝ, ∀ y, |F y| ≤ C) :
    (∫ g₁, ∫ g₀, F ((seededSplitGaussianScale ε t • A).mulVec g₁+
      (seededSplitGaussianScale ε t • A).mulVec g₀) ∂standardGaussian r ∂standardGaussian r) =
      ∫ g, F ((Real.sqrt (t+ε) • A).mulVec g) ∂standardGaussian r := by
  let P : Vector r × Vector r → Vector p := fun z =>
    (seededSplitGaussianScale ε t • A).mulVec z.1+(seededSplitGaussianScale ε t • A).mulVec z.2
  have hP : Measurable P :=
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst).add
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)
  obtain ⟨C,hC⟩ := hFb
  have hi : Integrable (fun z => F (P z)) ((standardGaussian r).prod (standardGaussian r)) :=
    (integrable_const C).mono' (hF.comp hP).aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact hC _))
  calc
    _ = ∫ z, F (P z) ∂(standardGaussian r).prod (standardGaussian r) := (integral_prod _ hi).symm
    _ = ∫ y, F y ∂(((standardGaussian r).prod (standardGaussian r)).map P) :=
      (integral_map hP.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ y, F y ∂RectangleCLT.Companion.rectangularGaussianLaw (Real.sqrt (t+ε) • A) := by
      rw [cap_gaussian_halves_map_rectangular A hε ht]
    _ = _ := by
      unfold RectangleCLT.Companion.rectangularGaussianLaw
      rw [integral_map (by fun_prop) hF.aestronglyMeasurable]

end
end RectangleCLTArxivV1
