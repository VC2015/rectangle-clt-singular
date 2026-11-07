import RectangleCLTCompanion.SplitV4.RestorationRelativeSeries
import RectangleCLTCompanion.RestorationSmootherIBP
import RectangleCLTCompanion.RestorationFourth
import RectangleCLTCompanion.SplitV4.RestorationDerivativeIdentification

/-! Two actual Gaussian Stein identities for the paired third/fourth
derivatives in B.2, with rectangular factors and translated bases. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem integrable_fixed_gaussian_repeated_score {r : ℕ} (z : Vector r) :
    Integrable (fun g => repeatedDirectionScore g z) (standardGaussian r) := by
  simpa only [mul_one] using integrable_repeatedDirectionScore_weight
    (standardGaussian r) id (fun _ => (1 : ℝ)) (integrable_const 1)
    (fun j k => by simpa only [mul_one] using standardGaussian_integrable_coordinate_product r j k) z

theorem integrable_score_firstDerivative {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r) (j : Fin p) :
    Integrable (fun g => repeatedDirectionScore g z * s.coordinateDerivativeF (A.mulVec g + x) j)
      (standardGaussian r) := by
  have hm : Measurable (fun g : Vector r => s.coordinateDerivativeF (A.mulVec g + x) j) :=
    (s.continuous_firstDerivative j).measurable.comp
      ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)
  have hi := (integrable_fixed_gaussian_repeated_score z).bdd_mul' hm.aestronglyMeasurable
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using s.norm_firstDerivative_le (A.mulVec g + x) j))
  simpa only [mul_comm] using hi

theorem integrable_score_secondDerivative {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (z : Vector r) (j k : Fin p) :
    Integrable (fun g => repeatedDirectionScore g z * s.mixedSecondDerivativeF (A.mulVec g + x) j k)
      (standardGaussian r) := by
  have hm : Measurable (fun g : Vector r => s.mixedSecondDerivativeF (A.mulVec g + x) j k) :=
    (s.continuous_secondDerivative j k).measurable.comp
      ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)
  have hi := (integrable_fixed_gaussian_repeated_score z).bdd_mul' hm.aestronglyMeasurable
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using s.norm_secondDerivative_le (A.mulVec g + x) j k))
  simpa only [mul_comm] using hi

theorem integrable_paired_third_coordinate {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x a : Vector p) (j : Fin p) :
    Integrable (fun g => matrixQuadratic (fun l m => s.mixedThirdDerivativeF (A.mulVec g + x) j l m) a)
      (standardGaussian r) := by
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have hi : Integrable (fun g : Vector r => s.mixedThirdDerivativeF (A.mulVec g + x) j l m)
      (standardGaussian r) := by
    apply (integrable_const (13 / s.bandwidth ^ 3)).mono'
      ((s.continuous_thirdDerivative j l m).measurable.comp
        ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)).aestronglyMeasurable
    exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using s.norm_thirdDerivative_le (A.mulVec g + x) j l m)
  exact (hi.const_mul (a l)).mul_const (a m)

theorem integrable_paired_fourth_coordinate {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x a : Vector p) (j k : Fin p) :
    Integrable (fun g => matrixQuadratic (fun l m => s.mixedFourthDerivativeF (A.mulVec g + x) j k l m) a)
      (standardGaussian r) := by
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have hi : Integrable (fun g : Vector r => s.mixedFourthDerivativeF (A.mulVec g + x) j k l m)
      (standardGaussian r) := by
    apply (integrable_const (75 / s.bandwidth ^ 4)).mono'
      ((s.continuous_fourthDerivative j k l m).measurable.comp
        ((continuous_const.matrix_mulVec continuous_id).measurable.add_const x)).aestronglyMeasurable
    exact ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using s.norm_fourthDerivative_le (A.mulVec g + x) j k l m)
  exact (hi.const_mul (a l)).mul_const (a m)

theorem gaussian_paired_third_coordinate_stein {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x y : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, ∑ j, y j * matrixQuadratic
      (fun l m => s.mixedThirdDerivativeF ((σ • A).mulVec g + x) j l m) (A.mulVec z)
        ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z * s.translationD1 ((σ • A).mulVec g + x) y
        ∂standardGaussian r) / σ ^ 2 := by
  have hi (j : Fin p) := integrable_paired_third_coordinate s (σ • A) x (A.mulVec z) j
  have hs (j : Fin p) := integrable_score_firstDerivative s (σ • A) x z j
  have hpoint (g : Vector r) : repeatedDirectionScore g z * s.translationD1 ((σ • A).mulVec g + x) y =
      ∑ j, (repeatedDirectionScore g z * s.coordinateDerivativeF ((σ • A).mulVec g + x) j) * y j := by
    simp only [FaceSmoother.translationD1, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [integral_finset_sum Finset.univ (fun j _ => (hi j).const_mul (y j))]
  simp_rw [integral_const_mul]
  simp_rw [smoother_third_repeated_score_scaled s A x z hσ]
  simp_rw [hpoint]
  rw [integral_finset_sum Finset.univ (fun j _ => (hs j).mul_const (y j)), Finset.sum_div]
  simp_rw [integral_mul_const]
  exact Finset.sum_congr rfl (fun j _ => by ring)

theorem gaussian_paired_fourth_coordinate_stein {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x y w : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, ∑ j, ∑ k, (w j * y k) * matrixQuadratic
      (fun l m => s.mixedFourthDerivativeF ((σ • A).mulVec g + x) j k l m) (A.mulVec z)
        ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z * restorationHessian s ((σ • A).mulVec g + x) w y
        ∂standardGaussian r) / σ ^ 2 := by
  have hi (j k : Fin p) := integrable_paired_fourth_coordinate s (σ • A) x (A.mulVec z) j k
  have hs (j k : Fin p) := integrable_score_secondDerivative s (σ • A) x z j k
  have hpoint (g : Vector r) : repeatedDirectionScore g z * restorationHessian s ((σ • A).mulVec g + x) w y =
      ∑ j, ∑ k, ((repeatedDirectionScore g z * s.mixedSecondDerivativeF ((σ • A).mulVec g + x) j k) * w j) * y k := by
    simp only [restorationHessian, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => (hi j k).const_mul (w j * y k)))]
  simp_rw [integral_finset_sum Finset.univ (fun k _ => (hi _ k).const_mul (w _ * y k)), integral_const_mul]
  simp_rw [smoother_fourth_repeated_score_scaled s A x z hσ]
  simp_rw [hpoint]
  rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
    (fun k _ => ((hs j k).mul_const (w j)).mul_const (y k))), Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  rw [integral_finset_sum Finset.univ (fun k _ => ((hs j k).mul_const (w j)).mul_const (y k)), Finset.sum_div]
  simp_rw [integral_mul_const]
  exact Finset.sum_congr rfl (fun k _ => by ring)

theorem gaussian_restorationThirdDerivative_stein {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x y : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, restorationThirdDerivative s ((σ • A).mulVec g + x) (A.mulVec z) y ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z * s.translationD1 ((σ • A).mulVec g + x) y
        ∂standardGaussian r) / σ ^ 2 := by
  simp_rw [restorationThirdDerivative_eq_coordinate]
  exact gaussian_paired_third_coordinate_stein s A x y z hσ

theorem gaussian_restorationFourthDerivative_stein {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x y w : Vector p) (z : Vector r)
    {σ : ℝ} (hσ : σ ≠ 0) :
    (∫ g, restorationFourthDerivative s ((σ • A).mulVec g + x) (A.mulVec z) y w ∂standardGaussian r) =
      (∫ g, repeatedDirectionScore g z * restorationHessian s ((σ • A).mulVec g + x) w y
        ∂standardGaussian r) / σ ^ 2 := by
  simp_rw [restorationFourthDerivative_eq_coordinate]
  exact gaussian_paired_fourth_coordinate_stein s A x y w z hσ

theorem integrable_projected_coordinate_product {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (μ : Measure Ω) (A : Matrix (Fin p) (Fin r) ℝ) (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ) (j k : Fin p) :
    Integrable (fun ω => A.mulVec (Z ω) j * A.mulVec (Z ω) k) μ := by
  have hi := integrable_finset_sum Finset.univ (fun a _ => integrable_finset_sum Finset.univ
    (fun b _ => ((hZ a b).const_mul (A j a)).mul_const (A k b)))
  convert hi using 1
  funext ω
  simp only [Matrix.mulVec, dotProduct, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a _
  exact Finset.sum_congr rfl (fun b _ => by ring)

theorem restoration_ae_abs_fst_le {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (a : Ω → ℝ) (ha : Measurable a) {B : ℝ} (hab : ∀ᵐ ω ∂μ, |a ω| ≤ B) :
    ∀ᵐ z : Ω × Γ ∂μ.prod ν, |a z.1| ≤ B := by
  apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (ha.comp measurable_fst).abs measurable_const)).mpr
  exact hab.mono (fun _ hω => ae_of_all _ (fun _ => hω))

theorem integrable_restoration_bounded_product
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (P a : Ω → ℝ) (f : Ω × Γ → ℝ) (hP : Integrable P μ)
    (ha : Measurable a) (hf : Measurable f) {B C : ℝ} (hB : 0 ≤ B)
    (hab : ∀ᵐ ω ∂μ, |a ω| ≤ B) (hfb : ∀ z, |f z| ≤ C) :
    Integrable (fun z : Ω × Γ => (a z.1 * f z) * P z.1) (μ.prod ν) := by
  have hPi : Integrable (fun z : Ω × Γ => P z.1) (μ.prod ν) := by
    simpa only [mul_one] using hP.mul_prod (integrable_const (μ := ν) (1 : ℝ))
  apply hPi.bdd_mul' ((ha.comp measurable_fst).mul hf).aestronglyMeasurable
  filter_upwards [restoration_ae_abs_fst_le μ ν a ha hab] with z hz
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul hz (hfb z) (abs_nonneg _) hB

theorem integrable_random_restorationThirdDerivative
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Ω → Vector r)
    (_hZm : Measurable Z) (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y : Ω → Vector p) (hY : Measurable Y) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (X : Ω × Vector r → Vector p) (hX : Measurable X) :
    Integrable (fun z : Ω × Vector r => restorationThirdDerivative s (X z) (A.mulVec (Z z.1)) (Y z.1))
      (μ.prod (standardGaussian r)) := by
  simp_rw [restorationThirdDerivative_eq_coordinate, matrixQuadratic, Finset.mul_sum]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have ha : Measurable (fun ω => Y ω j) := (measurable_pi_apply j).comp hY
  have hab : ∀ᵐ ω ∂μ, |Y ω j| ≤ δ := hYb.mono (fun ω hω => (norm_le_pi_norm (Y ω) j).trans hω)
  have hi := integrable_restoration_bounded_product μ (standardGaussian r)
    (fun ω => A.mulVec (Z ω) l * A.mulVec (Z ω) m) (fun ω => Y ω j)
    (fun z => s.mixedThirdDerivativeF (X z) j l m)
    (integrable_projected_coordinate_product μ A Z hZ l m) ha
    ((s.continuous_thirdDerivative j l m).measurable.comp hX) hδ hab
    (fun z => s.norm_thirdDerivative_le (X z) j l m)
  convert hi using 1
  funext z
  ring

theorem integrable_random_restorationFourthDerivative
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (Z : Ω → Vector r)
    (_hZm : Measurable Z) (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y W : Ω → Vector p) (hY : Measurable Y) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ δ)
    (X : Ω × Vector r → Vector p) (hX : Measurable X) :
    Integrable (fun z : Ω × Vector r => restorationFourthDerivative s (X z) (A.mulVec (Z z.1)) (Y z.1) (W z.1))
      (μ.prod (standardGaussian r)) := by
  simp_rw [restorationFourthDerivative_eq_coordinate, matrixQuadratic, Finset.mul_sum]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have ha : Measurable (fun ω => W ω j * Y ω k) :=
    ((measurable_pi_apply j).comp hW).mul ((measurable_pi_apply k).comp hY)
  have hab : ∀ᵐ ω ∂μ, |W ω j * Y ω k| ≤ δ ^ 2 := by
    filter_upwards [hYb, hWb] with ω hy hw
    rw [abs_mul, pow_two]
    exact mul_le_mul ((norm_le_pi_norm (W ω) j).trans hw) ((norm_le_pi_norm (Y ω) k).trans hy)
      (abs_nonneg _) hδ
  have hi := integrable_restoration_bounded_product μ (standardGaussian r)
    (fun ω => A.mulVec (Z ω) l * A.mulVec (Z ω) m) (fun ω => W ω j * Y ω k)
    (fun z => s.mixedFourthDerivativeF (X z) j k l m)
    (integrable_projected_coordinate_product μ A Z hZ l m) ha
    ((s.continuous_fourthDerivative j k l m).measurable.comp hX) (sq_nonneg δ) hab
    (fun z => s.norm_fourthDerivative_le (X z) j k l m)
  convert hi using 1
  funext z
  ring

theorem integrable_random_score_translationD1
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y : Ω → Vector p) (hY : Measurable Y) {δ : ℝ} (_hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (X : Ω × Vector r → Vector p) (hX : Measurable X) :
    Integrable (fun z : Ω × Vector r => repeatedDirectionScore z.2 (Z z.1) * s.translationD1 (X z) (Y z.1))
      (μ.prod (standardGaussian r)) := by
  have hm : Measurable (fun z : Ω × Vector r => s.translationD1 (X z) (Y z.1)) :=
    Finset.measurable_sum _ (fun j _ => ((s.continuous_firstDerivative j).measurable.comp hX).mul
      ((measurable_pi_apply j).comp (hY.comp measurable_fst)))
  have hYprod : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ‖Y z.1‖ ≤ δ := by
    simpa only [abs_norm] using restoration_ae_abs_fst_le μ (standardGaussian r) (fun ω => ‖Y ω‖) hY.norm
      (by simpa only [abs_norm] using hYb)
  have hb : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r),
      ‖s.translationD1 (X z) (Y z.1)‖ ≤ (p : ℝ) * (1 / s.bandwidth) * δ := by
    filter_upwards [hYprod] with z hz
    apply (s.norm_translationD1_le_constant _ _).trans
    calc
      _ ≤ ∑ _j : Fin p, (1 / s.bandwidth) * δ := Finset.sum_le_sum (fun j _ => by
        simp only [pow_one]
        exact mul_le_mul_of_nonneg_left ((norm_le_pi_norm (Y z.1) j).trans hz)
          (div_nonneg (by norm_num) s.bandwidth_pos.le))
      _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have hi := (integrable_random_repeatedDirectionScore μ Z hZ).bdd_mul' hm.aestronglyMeasurable hb
  simpa only [mul_comm] using hi

theorem integrable_random_score_restorationHessian
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ] (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y W : Ω → Vector p) (hY : Measurable Y) (hW : Measurable W) {δ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ δ)
    (X : Ω × Vector r → Vector p) (hX : Measurable X) :
    Integrable (fun z : Ω × Vector r => repeatedDirectionScore z.2 (Z z.1) * restorationHessian s (X z) (W z.1) (Y z.1))
      (μ.prod (standardGaussian r)) := by
  have hm : Measurable (fun z : Ω × Vector r => restorationHessian s (X z) (W z.1) (Y z.1)) := by
    apply Finset.measurable_sum
    intro j _
    exact Finset.measurable_sum _ (fun k _ =>
      (((s.continuous_secondDerivative j k).measurable.comp hX).mul
        ((measurable_pi_apply j).comp (hW.comp measurable_fst))).mul
        ((measurable_pi_apply k).comp (hY.comp measurable_fst)))
  have hYprod : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ‖Y z.1‖ ≤ δ := by
    simpa only [abs_norm] using restoration_ae_abs_fst_le μ (standardGaussian r) (fun ω => ‖Y ω‖) hY.norm
      (by simpa only [abs_norm] using hYb)
  have hWprod : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r), ‖W z.1‖ ≤ δ := by
    simpa only [abs_norm] using restoration_ae_abs_fst_le μ (standardGaussian r) (fun ω => ‖W ω‖) hW.norm
      (by simpa only [abs_norm] using hWb)
  have hb : ∀ᵐ z : Ω × Vector r ∂μ.prod (standardGaussian r),
      ‖restorationHessian s (X z) (W z.1) (Y z.1)‖ ≤ 3 * δ ^ 2 / s.bandwidth ^ 2 := by
    filter_upwards [hYprod, hWprod] with z hy hw
    exact abs_restorationHessian_le s _ _ _ hδ hw hy
  have hi := (integrable_random_repeatedDirectionScore μ Z hZ).bdd_mul' hm.aestronglyMeasurable hb
  simpa only [mul_comm] using hi

theorem random_restorationThirdDerivative_stein
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V v : Ω → Vector p) (hV : Measurable V) (hv : Measurable v)
    (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y : Ω → Vector p) (hY : Measurable Y) {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (hσ : σ ≠ 0) :
    Integrable (fun z : Ω × Vector r => restorationThirdDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v z.1) (A.mulVec (Z z.1)) (Y z.1)) (μ.prod (standardGaussian r)) ∧
    Integrable (fun z : Ω × Vector r => repeatedDirectionScore z.2 (Z z.1) *
      s.translationD1 ((σ • A).mulVec z.2 + V z.1 + v z.1) (Y z.1)) (μ.prod (standardGaussian r)) ∧
    (∫ z : Ω × Vector r, restorationThirdDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v z.1) (A.mulVec (Z z.1)) (Y z.1) ∂μ.prod (standardGaussian r)) =
      (∫ z : Ω × Vector r, repeatedDirectionScore z.2 (Z z.1) *
        s.translationD1 ((σ • A).mulVec z.2 + V z.1 + v z.1) (Y z.1) ∂μ.prod (standardGaussian r)) / σ ^ 2 := by
  let X : Ω × Vector r → Vector p := fun z => (σ • A).mulVec z.2 + V z.1 + v z.1
  have hX : Measurable X :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)).add (hv.comp measurable_fst)
  have hiD := integrable_random_restorationThirdDerivative s μ A Z hZm hZ Y hY hδ hYb X hX
  have hiS := integrable_random_score_translationD1 s μ Z hZ Y hY hδ hYb X hX
  refine ⟨hiD, hiS, ?_⟩
  rw [integral_prod _ hiD, integral_prod _ hiS, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    simpa only [X, add_assoc] using gaussian_restorationThirdDerivative_stein s A (V ω + v ω) (Y ω) (Z ω) hσ)

theorem random_restorationFourthDerivative_stein
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V v : Ω → Vector p) (hV : Measurable V) (hv : Measurable v)
    (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j * Z ω k) μ)
    (Y W : Ω → Vector p) (hY : Measurable Y) (hW : Measurable W) {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ᵐ ω ∂μ, ‖Y ω‖ ≤ δ) (hWb : ∀ᵐ ω ∂μ, ‖W ω‖ ≤ δ) (hσ : σ ≠ 0) :
    Integrable (fun z : Ω × Vector r => restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v z.1) (A.mulVec (Z z.1)) (Y z.1) (W z.1)) (μ.prod (standardGaussian r)) ∧
    Integrable (fun z : Ω × Vector r => repeatedDirectionScore z.2 (Z z.1) *
      restorationHessian s ((σ • A).mulVec z.2 + V z.1 + v z.1) (W z.1) (Y z.1)) (μ.prod (standardGaussian r)) ∧
    (∫ z : Ω × Vector r, restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v z.1) (A.mulVec (Z z.1)) (Y z.1) (W z.1) ∂μ.prod (standardGaussian r)) =
      (∫ z : Ω × Vector r, repeatedDirectionScore z.2 (Z z.1) *
        restorationHessian s ((σ • A).mulVec z.2 + V z.1 + v z.1) (W z.1) (Y z.1) ∂μ.prod (standardGaussian r)) / σ ^ 2 := by
  let X : Ω × Vector r → Vector p := fun z => (σ • A).mulVec z.2 + V z.1 + v z.1
  have hX : Measurable X :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)).add (hv.comp measurable_fst)
  have hiD := integrable_random_restorationFourthDerivative s μ A Z hZm hZ Y W hY hW hδ hYb hWb X hX
  have hiS := integrable_random_score_restorationHessian s μ Z hZ Y W hY hW hδ hYb hWb X hX
  refine ⟨hiD, hiS, ?_⟩
  rw [integral_prod _ hiD, integral_prod _ hiS, ← integral_div]
  apply integral_congr_ae
  exact ae_of_all _ (fun ω => by
    simpa only [X, add_assoc] using gaussian_restorationFourthDerivative_stein s A (V ω + v ω) (Y ω) (W ω) (Z ω) hσ)

theorem array_restorationThirdDerivative_stein
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hσ : σ ≠ 0) :
    Integrable (fun z : Ω × Vector r => ∑ i, restorationThirdDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1)) (μ.prod (standardGaussian r)) ∧
    Integrable (fun z : Ω × Vector r => ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
      s.translationD1 ((σ • A).mulVec z.2 + V z.1 + v i z.1) (Y i z.1)) (μ.prod (standardGaussian r)) ∧
    (∫ z : Ω × Vector r, ∑ i, restorationThirdDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) ∂μ.prod (standardGaussian r)) =
      (∫ z : Ω × Vector r, ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
        s.translationD1 ((σ • A).mulVec z.2 + V z.1 + v i z.1) (Y i z.1) ∂μ.prod (standardGaussian r)) / σ ^ 2 := by
  have hi (i : Fin n) := random_restorationThirdDerivative_stein s μ A V (v i) hV (hv i)
    (Z i) (hZm i) (hZ i) (Y i) (hY i) hδ (hYb i) hσ
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),
    integrable_finset_sum _ (fun i _ => (hi i).2.1), ?_⟩
  rw [integral_finset_sum Finset.univ (fun i _ => (hi i).1),
    integral_finset_sum Finset.univ (fun i _ => (hi i).2.1), Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => (hi i).2.2)

theorem array_restorationFourthDerivative_stein
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y W : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i)) (hW : ∀ i, Measurable (W i))
    {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) (hσ : σ ≠ 0) :
    Integrable (fun z : Ω × Vector r => ∑ i, restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1)) (μ.prod (standardGaussian r)) ∧
    Integrable (fun z : Ω × Vector r => ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
      restorationHessian s ((σ • A).mulVec z.2 + V z.1 + v i z.1) (W i z.1) (Y i z.1)) (μ.prod (standardGaussian r)) ∧
    (∫ z : Ω × Vector r, ∑ i, restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1) ∂μ.prod (standardGaussian r)) =
      (∫ z : Ω × Vector r, ∑ i, repeatedDirectionScore z.2 (Z i z.1) *
        restorationHessian s ((σ • A).mulVec z.2 + V z.1 + v i z.1) (W i z.1) (Y i z.1) ∂μ.prod (standardGaussian r)) / σ ^ 2 := by
  have hi (i : Fin n) := random_restorationFourthDerivative_stein s μ A V (v i) hV (hv i)
    (Z i) (hZm i) (hZ i) (Y i) (W i) (hY i) (hW i) hδ (hYb i) (hWb i) hσ
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),
    integrable_finset_sum _ (fun i _ => (hi i).2.1), ?_⟩
  rw [integral_finset_sum Finset.univ (fun i _ => (hi i).1),
    integral_finset_sum Finset.univ (fun i _ => (hi i).2.1), Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => (hi i).2.2)

end

end RectangleCLT.Companion.SplitV4
