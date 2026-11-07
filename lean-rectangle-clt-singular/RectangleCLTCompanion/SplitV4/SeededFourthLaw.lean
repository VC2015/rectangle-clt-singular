import RectangleCLTCompanion.SplitV4.SeededRelativeCopyBudgets
import RectangleCLTCompanion.SplitV4.SeededGaussianSplit
import RectangleCLTCompanion.SplitV4.SeededRestorationBounds
import RectangleCLTCompanion.SplitV4.VariableAmplitudeFourthIdentity
import RectangleCLTCompanion.SharpGaussianConvolution

/-! Actual retained-array and Gaussian-half law transport for the seeded
fourth-order kernels. Bounds used for Fubini are auxiliary finite bounds;
the identities have no derivative estimate as a premise. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem seeded_arraySum_update_zero {p n : ℕ} (b : Fin n → Vector p) (i : Fin n) :
    arraySum (Function.update b i 0) = arraySum b - b i := by
  classical
  unfold arraySum
  rw [Finset.sum_update_of_mem (Finset.mem_univ i), zero_add]
  apply (eq_sub_iff_add_eq).mpr
  simpa only [Finset.sum_singleton] using Finset.sum_sdiff
    (f := b) (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))

theorem seeded_retainedArray_remove {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (t : ℝ) (mask : Kane.Cube n) (ω : Ω) (i : Fin n) :
    arraySum (retainedArray ξ t mask ω) - retainedArray ξ t mask ω i =
      thinningScale t • maskObservationSum ξ (Function.update mask i false) ω := by
  have heq : retainedArray ξ t (Function.update mask i false) ω =
      Function.update (retainedArray ξ t mask ω) i 0 := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [retainedArray]
    · simp [retainedArray, Function.update_of_ne hj]
  rw [← seeded_arraySum_update_zero, ← heq, arraySum_retainedArray_eq_maskObservationSum]

theorem integral_bernoulliArrayLaw_bounded_kernel
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (G : (Fin n → Vector p) → ℝ) (hG : Measurable G)
    {D : ℝ} (hGb : ∀ b, ‖G b‖ ≤ D) :
    (∫ b, G b ∂bernoulliArrayLaw μ ξ t) =
      ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ ω, G (retainedArray ξ t mask ω) ∂μ := by
  have hi (mask : Kane.Cube n) : Integrable G (μ.map (retainedArray ξ t mask)) := by
    letI : IsProbabilityMeasure (μ.map (retainedArray ξ t mask)) :=
      isProbabilityMeasure_map (μ := μ) (measurable_retainedArray ξ hξ t mask).aemeasurable
    exact (integrable_const D).mono' hG.aestronglyMeasurable (Filter.Eventually.of_forall hGb)
  rw [bernoulliArrayLaw, integral_bernoulliMixtureLaw μ (retainedArray ξ t)
    (thinningProbability t) (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) G hi]
  apply Finset.sum_congr rfl
  intro mask _
  rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable hG.aestronglyMeasurable]

/-- Removing one retained coordinate uses the full array law. The kernel
may have only an a.e. envelope in the independent-copy variables. -/
theorem seeded_retained_leaveRow_kernel
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ρ : Measure Ξ) [IsProbabilityMeasure ρ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (K : Fin n → Vector p → Ξ → ℝ)
    (hKm : ∀ i, Measurable (fun ya : Vector p × Ξ => K i ya.1 ya.2))
    {D : ℝ} (hKb : ∀ i, ∀ᵐ a ∂ρ, ∀ y, ‖K i y a‖ ≤ D)
    (x : Vector p) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ b, ∑ i, ∫ a, K i (x + arraySum b - b i) a ∂ρ ∂bernoulliArrayLaw μ ξ t) =
      ∑ i, ∑ mask, Kane.maskWeight (thinningProbability t) mask *
        ∫ z : Ω × Ξ, K i (x + thinningScale t •
          maskObservationSum ξ (Function.update mask i false) z.1) z.2 ∂μ.prod ρ := by
  letI := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  let G : Fin n → (Fin n → Vector p) → ℝ :=
    fun i b => ∫ a, K i (x + arraySum b - b i) a ∂ρ
  have hGm (i : Fin n) : Measurable (G i) := by
    exact (((hKm i).comp
      (((measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).sub
        ((measurable_pi_apply i).comp measurable_fst)).prodMk measurable_snd)).stronglyMeasurable.integral_prod_right').measurable
  have hGb (i : Fin n) (b : Fin n → Vector p) : ‖G i b‖ ≤ D := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ρ) ((hKb i).mono (fun _ h => h _))
  have hGi (i : Fin n) : Integrable (G i) (bernoulliArrayLaw μ ξ t) :=
    (integrable_const D).mono' (hGm i).aestronglyMeasurable (Filter.Eventually.of_forall (hGb i))
  rw [integral_finset_sum Finset.univ (fun i _ => hGi i)]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_bernoulliArrayLaw_bounded_kernel μ ξ hξ ht ht1 (G i) (hGm i) (hGb i)]
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  have hbase : Measurable (fun ω => x + thinningScale t •
      maskObservationSum ξ (Function.update mask i false) ω) :=
    measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ hξ _))
  have hm : Measurable (fun z : Ω × Ξ => K i
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) z.2) :=
    (hKm i).comp ((hbase.comp measurable_fst).prodMk measurable_snd)
  have hi : Integrable (fun z : Ω × Ξ => K i
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1) z.2) (μ.prod ρ) :=
    (integrable_const D).mono' hm.aestronglyMeasurable
      ((Measure.quasiMeasurePreserving_snd.ae (hKb i)).mono (fun _ h => h _))
  rw [integral_prod _ hi]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun ω => by
    dsimp only [G]
    rw [show x + arraySum (retainedArray ξ t mask ω) - retainedArray ξ t mask ω i =
      x + thinningScale t • maskObservationSum ξ (Function.update mask i false) ω by
        rw [add_sub_assoc, seeded_retainedArray_remove]])

theorem restorationHessian_swap {p : ℕ} (s : FaceSmoother p) (x y w : Vector p) :
    restorationHessian s x y w = restorationHessian s x w y := by
  unfold restorationHessian
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  rw [s.mixedSecondDerivativeF_symm x k j]
  ring

theorem convolutionFourthTensor_eq_gaussian_restoration
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x y w z : Vector p) {σ : ℝ} (hσ : σ ≠ 0) :
    s.convolutionFourthTensor (gaussianLaw (σ • A)) x (A.mulVec z) (A.mulVec z) y w =
      ∫ g, restorationFourthDerivative s ((σ • A).mulVec g + x) (A.mulVec z) y w ∂standardGaussian p := by
  rw [convolutionFourthTensor_repeated_score_scaled s A x z y w hσ,
    gaussian_restorationFourthDerivative_stein s A x y w z hσ]
  simp_rw [restorationHessian_swap s _ w y]

def seededFourthTensorEnvelope {p : ℕ} (s : FaceSmoother p) (δ : ℝ) : ℝ :=
  (p : ℝ) ^ 4 * (75 / s.bandwidth ^ 4) * δ ^ 4

theorem seeded_fourthTensor_norm_le {p : ℕ} (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν] (x u v w z : Vector p)
    {δ : ℝ} (hδ : 0 ≤ δ) (hu : ‖u‖ ≤ δ) (hv : ‖v‖ ≤ δ)
    (hw : ‖w‖ ≤ δ) (hz : ‖z‖ ≤ δ) :
    ‖s.convolutionFourthTensor ν x u v w z‖ ≤ seededFourthTensorEnvelope s δ := by
  have hj (j k l m : Fin p) :
      ‖s.convolutionFourthDerivative ν x j k l m * u j * v k * w l * z m‖ ≤
        (75 / s.bandwidth ^ 4) * δ * δ * δ * δ := by
    have hD : 0 ≤ 75 / s.bandwidth ^ 4 := by positivity
    have h1 := mul_le_mul (s.norm_convolutionFourthDerivative_le ν x j k l m)
      ((norm_le_pi_norm u j).trans hu) (norm_nonneg _) hD
    have h2 := mul_le_mul h1 ((norm_le_pi_norm v k).trans hv) (norm_nonneg _) (mul_nonneg hD hδ)
    have h3 := mul_le_mul h2 ((norm_le_pi_norm w l).trans hw) (norm_nonneg _)
      (mul_nonneg (mul_nonneg hD hδ) hδ)
    have h4 := mul_le_mul h3 ((norm_le_pi_norm z m).trans hz) (norm_nonneg _)
      (mul_nonneg (mul_nonneg (mul_nonneg hD hδ) hδ) hδ)
    simpa only [norm_mul] using h4
  unfold FaceSmoother.convolutionFourthTensor
  calc
    _ ≤ ∑ j, ∑ k, ∑ l, ∑ m, (75 / s.bandwidth ^ 4) * δ * δ * δ * δ := by
      apply norm_sum_le_of_le
      intro j _
      apply norm_sum_le_of_le
      intro k _
      apply norm_sum_le_of_le
      intro l _
      apply norm_sum_le_of_le
      intro m _
      exact hj j k l m
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, seededFourthTensorEnvelope]
      ring

theorem measurable_seeded_convolutionFourthTensor
    {X : Type*} [MeasurableSpace X] {p : ℕ} (s : FaceSmoother p)
    (ν : Measure (Vector p)) [IsProbabilityMeasure ν]
    (B U V W Z : X → Vector p) (hB : Measurable B) (hU : Measurable U)
    (hV : Measurable V) (hW : Measurable W) (hZ : Measurable Z) :
    Measurable (fun a => s.convolutionFourthTensor ν (B a) (U a) (V a) (W a) (Z a)) := by
  unfold FaceSmoother.convolutionFourthTensor
  apply Finset.measurable_sum
  intro j _
  apply Finset.measurable_sum
  intro k _
  apply Finset.measurable_sum
  intro l _
  exact Finset.measurable_sum _ (fun m _ =>
    (((((s.continuous_convolutionFourthDerivative_commonPoint ν j k l m).measurable.comp hB).mul
      ((measurable_pi_apply j).comp hU)).mul ((measurable_pi_apply k).comp hV)).mul
        ((measurable_pi_apply l).comp hW)).mul ((measurable_pi_apply m).comp hZ))

theorem seeded_integral_fourthTensor_gaussian_split
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {p n : ℕ}
    (s : FaceSmoother p) (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (A : Matrix (Fin p) (Fin p) ℝ) (t : ℝ)
    (B : Fin n → X × Y → Vector p) (U V W Z : Fin n → Y → Vector p)
    (hB : ∀ i, Measurable (B i)) (hU : ∀ i, Measurable (U i))
    (hV : ∀ i, Measurable (V i)) (hW : ∀ i, Measurable (W i))
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hUb : ∀ i, ∀ᵐ a ∂ρ, ‖U i a‖ ≤ δ) (hVb : ∀ i, ∀ᵐ a ∂ρ, ‖V i a‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ a ∂ρ, ‖W i a‖ ≤ δ) (hZb : ∀ i, ∀ᵐ a ∂ρ, ‖Z i a‖ ≤ δ) :
    (∫ x, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • A))
      (B i (x, a)) (U i a) (V i a) (W i a) (Z i a) ∂ρ ∂ν) =
    ∫ xg, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • A))
      (B i (xg.1, a) + (splitGaussianScale t • A).mulVec xg.2)
      (U i a) (V i a) (W i a) (Z i a) ∂ρ ∂ν.prod (standardGaussian p) := by
  let H (i : Fin n) (ba : (X × Vector p) × Y) :=
    s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • A))
      (B i (ba.1.1, ba.2) + (splitGaussianScale t • A).mulVec ba.1.2)
      (U i ba.2) (V i ba.2) (W i ba.2) (Z i ba.2)
  have hproj : Measurable (fun ba : (X × Vector p) × Y => (ba.1.1, ba.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hHm (i : Fin n) : Measurable (H i) := measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
    (((hB i).comp hproj).add ((measurable_mulVec _).comp (measurable_snd.comp measurable_fst)))
    ((hU i).comp measurable_snd) ((hV i).comp measurable_snd)
    ((hW i).comp measurable_snd) ((hZ i).comp measurable_snd)
  have hHb (i : Fin n) : ∀ᵐ a ∂ρ, ∀ xg, ‖H i (xg, a)‖ ≤ seededFourthTensorEnvelope s δ := by
    filter_upwards [hUb i, hVb i, hWb i, hZb i] with a hu hv hw hz
    exact fun _ => seeded_fourthTensor_norm_le s _ _ _ _ _ _ hδ hu hv hw hz
  have hGm (i : Fin n) : Measurable (fun xg => ∫ a, H i (xg, a) ∂ρ) :=
    (hHm i).stronglyMeasurable.integral_prod_right'.measurable
  have hGb (i : Fin n) (xg : X × Vector p) : ‖∫ a, H i (xg, a) ∂ρ‖ ≤ seededFourthTensorEnvelope s δ := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ρ) ((hHb i).mono (fun _ h => h xg))
  have hsum : Integrable (fun xg => ∑ i, ∫ a, H i (xg, a) ∂ρ) (ν.prod (standardGaussian p)) :=
    integrable_finset_sum _ (fun i _ => (integrable_const _).mono'
      (hGm i).aestronglyMeasurable (Filter.Eventually.of_forall (hGb i)))
  change _ = ∫ xg, ∑ i, ∫ a, H i (xg, a) ∂ρ ∂ν.prod (standardGaussian p)
  rw [integral_prod _ hsum]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hsection (i : Fin n) : Integrable (fun g => ∫ a, H i ((x, g), a) ∂ρ) (standardGaussian p) :=
    (integrable_const _).mono'
      ((hGm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun g => hGb i (x, g)))
  dsimp only
  rw [integral_finset_sum _ (fun i _ => hsection i)]
  apply Finset.sum_congr rfl
  intro i _
  have hjoint : Measurable (fun ag : Y × Vector p => H i ((x, ag.2), ag.1)) :=
    (hHm i).comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hi : Integrable (fun ag : Y × Vector p => H i ((x, ag.2), ag.1)) (ρ.prod (standardGaussian p)) :=
    (integrable_const _).mono' hjoint.aestronglyMeasurable
      ((Measure.quasiMeasurePreserving_fst.ae (hHb i)).mono (fun _ h => h _))
  calc
    _ = ∫ a, ∫ g, H i ((x, g), a) ∂standardGaussian p ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => s.convolutionFourthTensor_gaussian_split A t
        (B i (x, a)) (U i a) (V i a) (W i a) (Z i a))
    _ = _ := integral_integral_swap hi

theorem integrable_gaussian_restorationFourthDerivative
    {p : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x z y w : Vector p) (σ : ℝ) :
    Integrable (fun g => restorationFourthDerivative s ((σ • A).mulVec g + x) z y w)
      (standardGaussian p) := by
  simp_rw [restorationFourthDerivative_eq_coordinate, matrixQuadratic, Finset.mul_sum]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have hi := integrable_bounded_test_comp (standardGaussian p) (fun g => (σ • A).mulVec g + x)
    ((measurable_mulVec _).add measurable_const) _ (s.continuous_fourthDerivative j k l m) _
    (fun a => s.norm_fourthDerivative_le a j k l m)
  convert ((hi.const_mul (w j * y k)).mul_const (z l)).mul_const (z m) using 1
  funext g
  ring

theorem seeded_convolutionFourthExpectation_eq_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector p) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) (hσ : σ ≠ 0) :
    (∫ ω, ∑ i, s.convolutionFourthTensor (gaussianLaw (σ • A)) (V ω + v i ω)
      (A.mulVec (Z i ω)) (A.mulVec (Z i ω)) (Y i ω) (W i ω) ∂μ) =
      restorationFourthExpectation s μ A V Z Y W v σ := by
  have hX (i : Fin n) : Measurable (fun z : Ω × Vector p => (σ • A).mulVec z.2 + V z.1 + v i z.1) :=
    (((measurable_mulVec _).comp measurable_snd).add (hV.comp measurable_fst)).add ((hv i).comp measurable_fst)
  have hi : Integrable (fun z : Ω × Vector p => ∑ i, restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1))
      (μ.prod (standardGaussian p)) :=
    integrable_finset_sum _ (fun i _ => integrable_random_restorationFourthDerivative s μ A
      (Z i) (hZm i) (hZ i) (Y i) (W i) (hY i) (hW i) hδ (hYb i) (hWb i) _ (hX i))
  unfold restorationFourthExpectation
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hfixed (i : Fin n) : Integrable (fun g => restorationFourthDerivative s
      ((σ • A).mulVec g + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)) (standardGaussian p) := by
    simpa only [add_assoc] using integrable_gaussian_restorationFourthDerivative s A
      (V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω) σ
  dsimp only
  rw [integral_finset_sum _ (fun i _ => hfixed i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_assoc] using convolutionFourthTensor_eq_gaussian_restoration s A
    (V ω + v i ω) (Y i ω) (W i ω) (Z i ω) hσ

def seededFourthCopy {Ω : Type*} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (fresh : Bool) (i : Fin n) (a : Ω × Ω) : Vector p :=
  if fresh then ξ i a.2 else ξ i a.1

theorem seededFourthCopy_measurable {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i)) (fresh : Bool) (i : Fin n) :
    Measurable (seededFourthCopy ξ fresh i) := by
  cases fresh
  · exact (hξ i).comp measurable_fst
  · exact (hξ i).comp measurable_snd

theorem seededFourthCopy_bounded {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ) (fresh : Bool) (i : Fin n) :
    ∀ᵐ a ∂μ.prod μ, ‖seededFourthCopy ξ fresh i a‖ ≤ δ := by
  cases fresh
  · exact Measure.quasiMeasurePreserving_fst.ae (h.bounded i)
  · exact Measure.quasiMeasurePreserving_snd.ae (h.bounded i)

theorem seeded_integral_sum_inner_to_prod
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {n : ℕ}
    (ν : Measure X) [IsProbabilityMeasure ν] (ρ : Measure Y) [IsProbabilityMeasure ρ]
    (K : Fin n → X × Y → ℝ) (hKm : ∀ i, Measurable (K i))
    {D : ℝ} (hKb : ∀ i, ∀ᵐ a ∂ρ, ∀ x, ‖K i (x, a)‖ ≤ D) :
    (∫ x, ∑ i, ∫ a, K i (x, a) ∂ρ ∂ν) = ∫ z, ∑ i, K i z ∂ν.prod ρ := by
  have hi (i : Fin n) : Integrable (K i) (ν.prod ρ) :=
    (integrable_const D).mono' (hKm i).aestronglyMeasurable
      ((Measure.quasiMeasurePreserving_snd.ae (hKb i)).mono (fun _ h => h _))
  rw [integral_prod _ (integrable_finset_sum _ (fun i _ => hi i))]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  dsimp only
  have hsection (i : Fin n) : Integrable (fun a => K i (x, a)) ρ :=
    (integrable_const D).mono'
      ((hKm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      ((hKb i).mono (fun _ h => h x))
  rw [integral_finset_sum _ (fun i _ => hsection i)]

def seededFourthArrayKernel {Ω : Type*} {p n : ℕ} (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (ε t r : ℝ) (freshY freshW freshShift : Bool)
    (i : Fin n) (ba : (Fin n → Vector p) × (Ω × Ω)) : ℝ :=
  s.convolutionFourthTensor (gaussianLaw (Real.sqrt (t + ε) • A))
    (x + arraySum ba.1 + ((r * (1 + t)) • seededFourthCopy ξ freshShift i ba.2 - ba.1 i))
    (seededFourthCopy ξ false i ba.2) (seededFourthCopy ξ false i ba.2)
    (seededFourthCopy ξ freshY i ba.2) (seededFourthCopy ξ freshW i ba.2)

def seededFourthArrayExperiment {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (ε t r : ℝ) (freshY freshW freshShift : Bool) : ℝ :=
  ∫ b, ∑ i, ∫ a, seededFourthArrayKernel s ξ A x ε t r freshY freshW freshShift i (b, a)
    ∂μ.prod μ ∂bernoulliArrayLaw μ ξ t

theorem seededFourthArrayExperiment_eq_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (htε : 0 < t + ε)
    (freshY freshW freshShift : Bool) :
    seededFourthArrayExperiment s μ ξ A x ε t r freshY freshW freshShift =
      restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
        (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale ε t) := by
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht ht1
  letI := splitBaseLaw_isProbability μ ξ h.measurable ht ht1
  let B : Fin n → (Fin n → Vector p) × (Ω × Ω) → Vector p := fun i ba =>
    x + arraySum ba.1 + ((r * (1 + t)) • seededFourthCopy ξ freshShift i ba.2 - ba.1 i)
  let O := seededFourthCopy ξ
  have hB (i : Fin n) : Measurable (B i) :=
    (measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      ((measurable_const.smul ((seededFourthCopy_measurable ξ h.measurable freshShift i).comp measurable_snd)).sub
        ((measurable_pi_apply i).comp measurable_fst))
  have hO (b : Bool) (i : Fin n) : Measurable (O b i) := seededFourthCopy_measurable ξ h.measurable b i
  have hb (b : Bool) (i : Fin n) : ∀ᵐ a ∂μ.prod μ, ‖O b i a‖ ≤ δ := seededFourthCopy_bounded μ ξ h b i
  have hs := seeded_integral_fourthTensor_gaussian_split s (bernoulliArrayLaw μ ξ t) (μ.prod μ) A (t + ε)
    B (O false) (O false) (O freshY) (O freshW) hB (hO false) (hO false) (hO freshY) (hO freshW)
    h.delta_nonneg (hb false) (hb false) (hb freshY) (hb freshW)
  change seededFourthArrayExperiment s μ ξ A x ε t r freshY freshW freshShift = _ at hs
  rw [hs]
  let K : Fin n → (((Fin n → Vector p) × Vector p) × (Ω × Ω)) → ℝ := fun i z =>
    s.convolutionFourthTensor (gaussianLaw (seededSplitGaussianScale ε t • A))
      (seededSplitBaseValue A x ε t z.1 + seededCopyShift ξ freshShift t r i z)
      (seededCopyOriginal ξ i z) (seededCopyOriginal ξ i z)
      (seededCopyDirection ξ freshY i z) (seededCopyDirection ξ freshW i z)
  have hshift (i : Fin n) : Measurable (seededCopyShift ξ freshShift t r i) := by
    unfold seededCopyShift
    exact (measurable_const.smul (seededCopyDirection_measurable ξ h.measurable freshShift i)).sub
      ((measurable_pi_apply i).comp (measurable_fst.comp measurable_fst))
  have hKm (i : Fin n) : Measurable (K i) := measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
    (((measurable_seededSplitBaseValue A x ε t).comp measurable_fst).add (hshift i))
    (seededCopyOriginal_measurable ξ h.measurable i) (seededCopyOriginal_measurable ξ h.measurable i)
    (seededCopyDirection_measurable ξ h.measurable freshY i) (seededCopyDirection_measurable ξ h.measurable freshW i)
  have hKb (i : Fin n) : ∀ᵐ a ∂μ.prod μ, ∀ bg, ‖K i (bg, a)‖ ≤ seededFourthTensorEnvelope s δ := by
    filter_upwards [hb false i, hb freshY i, hb freshW i] with a hf hy hw
    intro bg
    have he (b : Bool) : seededCopyDirection ξ b i (bg, a) = O b i a := by cases b <;> rfl
    dsimp only [K]
    rw [he freshY, he freshW]
    exact seeded_fourthTensor_norm_le s _ _ _ _ _ _ h.delta_nonneg hf hf hy hw
  have he : (∫ bg, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale (t + ε) • A))
      (B i (bg.1, a) + (splitGaussianScale (t + ε) • A).mulVec bg.2)
      (O false i a) (O false i a) (O freshY i a) (O freshW i a) ∂μ.prod μ
        ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian p)) =
      ∫ bg, ∑ i, ∫ a, K i (bg, a) ∂μ.prod μ ∂splitBaseLaw μ ξ t := by
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro bg
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro a
    have hpoint : B i (bg.1, a) + (splitGaussianScale (t + ε) • A).mulVec bg.2 =
        seededSplitBaseValue A x ε t bg + seededCopyShift ξ freshShift t r i (bg, a) := by
      dsimp only [B, seededSplitBaseValue, seededCopyShift, splitGaussianScale, seededSplitGaussianScale]
      have he (b : Bool) : seededCopyDirection ξ b i (bg, a) = O b i a := by cases b <;> rfl
      rw [he freshShift]
      abel
    dsimp only
    rw [hpoint]
    cases freshY <;> cases freshW <;> rfl
  rw [he, seeded_integral_sum_inner_to_prod (splitBaseLaw μ ξ t) (μ.prod μ) K hKm hKb]
  have hre := seededCopyWhitened_reconstruct (splitBaseLaw μ ξ t) μ ξ h A hA
  have hraw : (∫ z, ∑ i, K i z ∂(splitBaseLaw μ ξ t).prod (μ.prod μ)) =
      ∫ z, ∑ i, s.convolutionFourthTensor (gaussianLaw (seededSplitGaussianScale ε t • A))
        (seededSplitBaseValue A x ε t z.1 + seededCopyShift ξ freshShift t r i z)
        (A.mulVec (seededCopyWhitened A ξ i z)) (A.mulVec (seededCopyWhitened A ξ i z))
        (seededCopyDirection ξ freshY i z) (seededCopyDirection ξ freshW i z)
        ∂(splitBaseLaw μ ξ t).prod (μ.prod μ) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hre] with z hz
    apply Finset.sum_congr rfl
    intro i _
    dsimp only [K]
    rw [hz i]
  rw [hraw]
  exact seeded_convolutionFourthExpectation_eq_product s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
    _ ((measurable_seededSplitBaseValue A x ε t).comp measurable_fst)
    (seededCopyWhitened A ξ) (seededCopyWhitened_measurable μ ξ h A)
    (seededCopyWhitened_integrable_coordinate_pair (splitBaseLaw μ ξ t) μ ξ h A)
    _ _ _ (seededCopyDirection_measurable ξ h.measurable freshY)
    (seededCopyDirection_measurable ξ h.measurable freshW) hshift h.delta_nonneg
    (seededCopyDirection_bounded (splitBaseLaw μ ξ t) μ ξ h freshY)
    (seededCopyDirection_bounded (splitBaseLaw μ ξ t) μ ξ h freshW)
    (seededSplitGaussianScale_pos htε).ne'

def seededFourthMaskExperiment {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (s : FaceSmoother p)
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (A : Matrix (Fin p) (Fin p) ℝ)
    (x : Vector p) (ε t r : ℝ) (freshY freshW freshShift : Bool) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask *
    ∫ z : Ω × (Ω × Ω), s.convolutionFourthTensor (gaussianLaw (Real.sqrt (t + ε) • A))
      (x + thinningScale t • maskObservationSum ξ (Function.update mask i false) z.1 +
        (r * (1 + t)) • seededFourthCopy ξ freshShift i z.2)
      (seededFourthCopy ξ false i z.2) (seededFourthCopy ξ false i z.2)
      (seededFourthCopy ξ freshY i z.2) (seededFourthCopy ξ freshW i z.2) ∂μ.prod (μ.prod μ)

theorem seededFourthMaskExperiment_eq_array
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε : ℝ)
    {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (r : ℝ) (freshY freshW freshShift : Bool) :
    seededFourthMaskExperiment s μ ξ A x ε t r freshY freshW freshShift =
      seededFourthArrayExperiment s μ ξ A x ε t r freshY freshW freshShift := by
  let K : Fin n → Vector p → Ω × Ω → ℝ := fun i y a =>
    s.convolutionFourthTensor (gaussianLaw (Real.sqrt (t + ε) • A))
      (y + (r * (1 + t)) • seededFourthCopy ξ freshShift i a)
      (seededFourthCopy ξ false i a) (seededFourthCopy ξ false i a)
      (seededFourthCopy ξ freshY i a) (seededFourthCopy ξ freshW i a)
  have hKm (i : Fin n) : Measurable (fun ya : Vector p × (Ω × Ω) => K i ya.1 ya.2) :=
    measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
      (measurable_fst.add (measurable_const.smul
        ((seededFourthCopy_measurable ξ h.measurable freshShift i).comp measurable_snd)))
      ((seededFourthCopy_measurable ξ h.measurable false i).comp measurable_snd)
      ((seededFourthCopy_measurable ξ h.measurable false i).comp measurable_snd)
      ((seededFourthCopy_measurable ξ h.measurable freshY i).comp measurable_snd)
      ((seededFourthCopy_measurable ξ h.measurable freshW i).comp measurable_snd)
  have hKb (i : Fin n) : ∀ᵐ a ∂μ.prod μ, ∀ y, ‖K i y a‖ ≤ seededFourthTensorEnvelope s δ := by
    filter_upwards [seededFourthCopy_bounded μ ξ h false i, seededFourthCopy_bounded μ ξ h freshY i,
      seededFourthCopy_bounded μ ξ h freshW i] with a hf hy hw
    exact fun _ => seeded_fourthTensor_norm_le s _ _ _ _ _ _ h.delta_nonneg hf hf hy hw
  have he := seeded_retained_leaveRow_kernel μ (μ.prod μ) ξ h.measurable K hKm hKb x ht ht1
  change _ = seededFourthMaskExperiment s μ ξ A x ε t r freshY freshW freshShift at he
  rw [← he]
  unfold seededFourthArrayExperiment
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro b
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro a
  dsimp only [K, seededFourthArrayKernel]
  congr 1
  abel

theorem seededFourthMaskExperiment_eq_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (htε : 0 < t + ε)
    (freshY freshW freshShift : Bool) :
    seededFourthMaskExperiment s μ ξ A x ε t r freshY freshW freshShift =
      restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyDirection ξ freshY) (seededCopyDirection ξ freshW)
        (seededCopyShift ξ freshShift t r) (seededSplitGaussianScale ε t) := by
  rw [seededFourthMaskExperiment_eq_array s μ ξ h A x ε ht ht1 r freshY freshW freshShift]
  exact seededFourthArrayExperiment_eq_product s μ ξ h A hA x ht ht1 htε freshY freshW freshShift

theorem variableFourthPathIntegrandB_eq_seeded_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (htε : 0 < t + ε) :
    s.variableFourthPathIntegrandB (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r =
      restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyDirection ξ true) (seededCopyDirection ξ true)
        (seededCopyShift ξ true t r) (seededSplitGaussianScale ε t) := by
  have he := seededFourthMaskExperiment_eq_product s μ ξ h A hA x (r := r) ht ht1 htε true true true
  simpa only [seededFourthMaskExperiment, FaceSmoother.variableFourthPathIntegrandB,
    seededFourthCopy, if_true, if_false, thinningScale, FaceSmoother.line, mul_comm r (1 + t)] using he

theorem variableFourthPathIntegrandC_eq_seeded_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (htε : 0 < t + ε) :
    s.variableFourthPathIntegrandC (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r =
      restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyDirection ξ false) (seededCopyDirection ξ true)
        (seededCopyShift ξ true t r) (seededSplitGaussianScale ε t) := by
  have he := seededFourthMaskExperiment_eq_product s μ ξ h A hA x (r := r) ht ht1 htε false true true
  simpa only [seededFourthMaskExperiment, FaceSmoother.variableFourthPathIntegrandC,
    seededFourthCopy, if_true, if_false, thinningScale, FaceSmoother.line, mul_comm r (1 + t)] using he

theorem variableFourthPathIntegrandA_eq_seeded_mask
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t r : ℝ) :
    s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r = seededFourthMaskExperiment s μ ξ A x ε t r false false false := by
  have hfst : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
  have hmp : MeasurePreserving (fun z : Ω × (Ω × Ω) => (z.1, z.2.1))
      (μ.prod (μ.prod μ)) (μ.prod μ) := (MeasurePreserving.id μ).prod hfst
  unfold FaceSmoother.variableFourthPathIntegrandA seededFourthMaskExperiment
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro mask _
  congr 1
  let F : Ω × Ω → ℝ := fun z => s.convolutionFourthTensor (gaussianLaw (Real.sqrt (t + ε) • A))
    (FaceSmoother.line (x + (1 + t) • maskObservationSum ξ (Function.update mask i false) z.1) (ξ i z.2) ((1 + t) * r))
    (ξ i z.2) (ξ i z.2) (ξ i z.2) (ξ i z.2)
  have hpoint : Measurable (fun z : Ω × Ω =>
      FaceSmoother.line (x + (1 + t) • maskObservationSum ξ (Function.update mask i false) z.1)
        (ξ i z.2) ((1 + t) * r)) := by
    change Measurable (fun z : Ω × Ω =>
      (x + (1 + t) • maskObservationSum ξ (Function.update mask i false) z.1) +
        (((1 + t) * r) • ξ i z.2))
    exact (measurable_const.add (measurable_const.smul
      ((measurable_maskObservationSum ξ hξ _).comp measurable_fst))).add
      (measurable_const.smul ((hξ i).comp measurable_snd))
  have hF : Measurable F := measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
    hpoint
    ((hξ i).comp measurable_snd) ((hξ i).comp measurable_snd)
    ((hξ i).comp measurable_snd) ((hξ i).comp measurable_snd)
  have he : (∫ z : Ω × (Ω × Ω), F (z.1, z.2.1) ∂μ.prod (μ.prod μ)) = ∫ z, F z ∂μ.prod μ := by
    calc
      _ = ∫ z, F z ∂(μ.prod (μ.prod μ)).map (fun z : Ω × (Ω × Ω) => (z.1, z.2.1)) :=
        (integral_map hmp.measurable.aemeasurable hF.aestronglyMeasurable).symm
      _ = _ := by rw [hmp.map_eq]
  simpa only [F, seededFourthCopy, if_false, thinningScale, FaceSmoother.line, mul_comm r (1 + t)] using he.symm

theorem variableFourthPathIntegrandA_eq_seeded_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t r : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1) (htε : 0 < t + ε) :
    s.variableFourthPathIntegrandA (gaussianLaw (Real.sqrt (t + ε) • A)) μ ξ x
      (thinningProbability t) (1 + t) r =
      restorationFourthExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyDirection ξ false) (seededCopyDirection ξ false)
        (seededCopyShift ξ false t r) (seededSplitGaussianScale ε t) := by
  rw [variableFourthPathIntegrandA_eq_seeded_mask s μ ξ h.measurable A x ε t r]
  exact seededFourthMaskExperiment_eq_product s μ ξ h A hA x ht ht1 htε false false false

end

end RectangleCLT.Companion.SplitV4
