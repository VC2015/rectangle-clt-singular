import RectangleCLTCompanion.SelectorMatrixReduction
import Mathlib.MeasureTheory.Integral.Prod

/-! Measurability and actual integrability of Gaussian weighted means.
Dimension-dependent domination is used only to justify integration, not as
the final quantitative CLT estimate. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion

noncomputable section

/-- Weighted Cauchy--Schwarz gives a finite domination independent of the
base point and of the weight mass, including mass zero. -/
theorem gaussian_weighted_mean_energy_le_dimension {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hwb : ∀ z, 0 ≤ w z ∧ w z ≤ 1) :
    weightMass (standardGaussian r) w *
      vectorNormSq (weightMean (standardGaussian r) id w) ≤ r := by
  have hb (z : Vector r) : |w z| ≤ 1 := by
    rw [abs_of_nonneg (hwb z).1]
    exact (hwb z).2
  have hwi := standardGaussian_integrable_bounded_weight w hw hb
  have hp : 0 ≤ weightMass (standardGaussian r) w := integral_nonneg (fun z => (hwb z).1)
  by_cases hz : weightMass (standardGaussian r) w = 0
  · rw [hz, zero_mul]
    positivity
  have hp0 : 0 < weightMass (standardGaussian r) w := lt_of_le_of_ne hp (Ne.symm hz)
  have hcoord (j : Fin r) :
      weightMass (standardGaussian r) w * (weightMean (standardGaussian r) id w j) ^ 2 ≤ 1 := by
    have h1 : Integrable (fun z => w z * z j) (standardGaussian r) := by
      simpa only [mul_comm] using standardGaussian_integrable_weighted_coordinate w hw hb j
    have h2 : Integrable (fun z => w z * (z j) ^ 2) (standardGaussian r) := by
      simpa only [pow_two, mul_assoc, mul_comm, mul_left_comm] using
        standardGaussian_integrable_weighted_product w hw hb j j
    have hh := weighted_mean_sq_le_second (standardGaussian r) w (fun z => z j)
      (fun z => (hwb z).1) hwi h1 h2 hp0
    have hmoment : (∫ z, w z * (z j) ^ 2 ∂standardGaussian r) ≤ 1 := by
      calc
        _ ≤ ∫ z, (z j) ^ 2 ∂standardGaussian r :=
          integral_mono h2 (by simpa only [pow_two] using standardGaussian_integrable_coordinate_product r j j)
            (fun z => mul_le_of_le_one_left (sq_nonneg _) (hwb z).2)
        _ = 1 := standardGaussian_integral_coordinate_sq r j
    convert hh.trans hmoment using 1
    simp only [weightMass, weightMean, id_eq, mul_comm]
  unfold vectorNormSq
  rw [Finset.mul_sum]
  calc
    _ ≤ ∑ _j : Fin r, (1 : ℝ) := Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by simp

/-- Actual weighted mean energy depends measurably on a measurable base. -/
theorem measurable_gaussian_weighted_mean_energy {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (w : Ω → Vector r → ℝ)
    (hw : Measurable (fun z : Ω × Vector r => w z.1 z.2)) :
    Measurable (fun ω => weightMass (standardGaussian r) (w ω) *
      vectorNormSq (weightMean (standardGaussian r) id (w ω))) := by
  have hp : Measurable (fun ω => weightMass (standardGaussian r) (w ω)) :=
    hw.stronglyMeasurable.integral_prod_right'.measurable
  have hn (j : Fin r) : Measurable (fun ω => ∫ g, g j * w ω g ∂standardGaussian r) := by
    have hm : Measurable (fun z : Ω × Vector r => z.2 j * w z.1 z.2) :=
      ((measurable_pi_apply j).comp measurable_snd).mul hw
    exact hm.stronglyMeasurable.integral_prod_right'.measurable
  apply hp.mul
  unfold vectorNormSq weightMean
  exact Finset.measurable_sum _ (fun j _ => ((hn j).div hp).pow_const 2)

/-- The finite domination proves genuine integrability over every
probability law of the base point. -/
theorem integrable_gaussian_weighted_mean_energy {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (ν : Measure Ω) [IsProbabilityMeasure ν] (w : Ω → Vector r → ℝ)
    (hw : Measurable (fun z : Ω × Vector r => w z.1 z.2))
    (hwb : ∀ ω z, 0 ≤ w ω z ∧ w ω z ≤ 1) :
    Integrable (fun ω => weightMass (standardGaussian r) (w ω) *
      vectorNormSq (weightMean (standardGaussian r) id (w ω))) ν := by
  apply (integrable_const (r : ℝ)).mono'
    (measurable_gaussian_weighted_mean_energy w hw).aestronglyMeasurable
  exact ae_of_all _ fun ω => by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
      (integral_nonneg (fun z => (hwb ω z).1)) (Finset.sum_nonneg (fun j _ => sq_nonneg _)))]
    exact gaussian_weighted_mean_energy_le_dimension (w ω)
      (hw.comp (measurable_const.prodMk measurable_id)) (hwb ω)

end
end RectangleCLT.Companion
