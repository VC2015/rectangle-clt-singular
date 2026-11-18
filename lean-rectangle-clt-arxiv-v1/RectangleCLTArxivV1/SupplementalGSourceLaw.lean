import RectangleCLTArxivV1.SupplementalGSeededContributions
import RectangleCLTArxivV1.SupplementalGPhysicalFourth

/-! Exact source-law transport of the calibrated fourth tensor between
square and rectangular covariance factors. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_gaussian_factor_integral_eq {p r : ℕ}
    (B : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : B*B.transpose = C*C.transpose) (F : Vector p → ℝ) (hF : Measurable F) :
    (∫ g, F (B.mulVec g) ∂standardGaussian r) = ∫ g, F (C.mulVec g) ∂standardGaussian p := by
  have hB : Measurable B.mulVec := (continuous_const.matrix_mulVec continuous_id).measurable
  calc
    _ = ∫ y, F y ∂RectangleCLT.Companion.rectangularGaussianLaw B :=
      (integral_map hB.aemeasurable hF.aestronglyMeasurable).symm
    _ = ∫ y, F y ∂gaussianLaw C := by rw [RectangleCLT.Companion.rectangularGaussianLaw_eq_gaussianLaw B C hgram]
    _ = _ := integral_map (measurable_mulVec C).aemeasurable hF.aestronglyMeasurable

theorem cap_convolutionFourthTensor_gaussian_split_rectangular {p r : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : A*A.transpose = C*C.transpose) (t : ℝ) (x u v w z : Vector p) :
    s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • C)) x u v w z =
      ∫ g, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • C))
        (x+(splitGaussianScale t • A).mulVec g) u v w z ∂standardGaussian r := by
  rw [s.convolutionFourthTensor_gaussian_split C t]
  have hscaled : (splitGaussianScale t • A)*(splitGaussianScale t • A).transpose =
      (splitGaussianScale t • C)*(splitGaussianScale t • C).transpose := by
    simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,hgram]
  have hF : Measurable (fun q : Vector p => s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • C))
      (x+q) u v w z) :=
    measurable_seeded_convolutionFourthTensor s _ (fun q => x+q)
      (fun _ => u) (fun _ => v) (fun _ => w) (fun _ => z)
      (measurable_const.add measurable_id) measurable_const measurable_const measurable_const measurable_const
  exact (cap_gaussian_factor_integral_eq (splitGaussianScale t • A) (splitGaussianScale t • C) hscaled
    (fun q => s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • C)) (x+q) u v w z) hF).symm


theorem cap_seeded_integral_fourthTensor_gaussian_split_rectangular
    {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y] {p r n : ℕ}
    (s : FaceSmoother p) (ν : Measure X) [IsProbabilityMeasure ν]
    (ρ : Measure Y) [IsProbabilityMeasure ρ] (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : A*A.transpose=C*C.transpose) (t : ℝ)
    (B : Fin n → X × Y → Vector p) (U V W Z : Fin n → Y → Vector p)
    (hB : ∀ i, Measurable (B i)) (hU : ∀ i, Measurable (U i))
    (hV : ∀ i, Measurable (V i)) (hW : ∀ i, Measurable (W i))
    (hZ : ∀ i, Measurable (Z i)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hUb : ∀ i, ∀ᵐ a ∂ρ, ‖U i a‖ ≤ δ) (hVb : ∀ i, ∀ᵐ a ∂ρ, ‖V i a‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ a ∂ρ, ‖W i a‖ ≤ δ) (hZb : ∀ i, ∀ᵐ a ∂ρ, ‖Z i a‖ ≤ δ) :
    (∫ x, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (Real.sqrt t • C))
      (B i (x, a)) (U i a) (V i a) (W i a) (Z i a) ∂ρ ∂ν) =
    ∫ xg, ∑ i, ∫ a, s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • C))
      (B i (xg.1, a) + (splitGaussianScale t • A).mulVec xg.2)
      (U i a) (V i a) (W i a) (Z i a) ∂ρ ∂ν.prod (standardGaussian r) := by
  let H (i : Fin n) (ba : (X × Vector r) × Y) :=
    s.convolutionFourthTensor (gaussianLaw (splitGaussianScale t • C))
      (B i (ba.1.1, ba.2) + (splitGaussianScale t • A).mulVec ba.1.2)
      (U i ba.2) (V i ba.2) (W i ba.2) (Z i ba.2)
  have hproj : Measurable (fun ba : (X × Vector r) × Y => (ba.1.1, ba.2)) :=
    (measurable_fst.comp measurable_fst).prodMk measurable_snd
  have hHm (i : Fin n) : Measurable (H i) := measurable_seeded_convolutionFourthTensor s _ _ _ _ _ _
    (((hB i).comp hproj).add (((continuous_const.matrix_mulVec continuous_id).measurable).comp (measurable_snd.comp measurable_fst)))
    ((hU i).comp measurable_snd) ((hV i).comp measurable_snd)
    ((hW i).comp measurable_snd) ((hZ i).comp measurable_snd)
  have hHb (i : Fin n) : ∀ᵐ a ∂ρ, ∀ xg, ‖H i (xg, a)‖ ≤ seededFourthTensorEnvelope s δ := by
    filter_upwards [hUb i, hVb i, hWb i, hZb i] with a hu hv hw hz
    exact fun _ => seeded_fourthTensor_norm_le s _ _ _ _ _ _ hδ hu hv hw hz
  have hGm (i : Fin n) : Measurable (fun xg => ∫ a, H i (xg, a) ∂ρ) :=
    (hHm i).stronglyMeasurable.integral_prod_right'.measurable
  have hGb (i : Fin n) (xg : X × Vector r) : ‖∫ a, H i (xg, a) ∂ρ‖ ≤ seededFourthTensorEnvelope s δ := by
    simpa only [measureReal_univ_eq_one, mul_one] using
      norm_integral_le_of_norm_le_const (μ := ρ) ((hHb i).mono (fun _ h => h xg))
  have hsum : Integrable (fun xg => ∑ i, ∫ a, H i (xg, a) ∂ρ) (ν.prod (standardGaussian r)) :=
    integrable_finset_sum _ (fun i _ => (integrable_const _).mono'
      (hGm i).aestronglyMeasurable (Filter.Eventually.of_forall (hGb i)))
  change _ = ∫ xg, ∑ i, ∫ a, H i (xg, a) ∂ρ ∂ν.prod (standardGaussian r)
  rw [integral_prod _ hsum]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  have hsection (i : Fin n) : Integrable (fun g => ∫ a, H i ((x, g), a) ∂ρ) (standardGaussian r) :=
    (integrable_const _).mono'
      ((hGm i).comp (measurable_const.prodMk measurable_id)).aestronglyMeasurable
      (Filter.Eventually.of_forall (fun g => hGb i (x, g)))
  dsimp only
  rw [integral_finset_sum _ (fun i _ => hsection i)]
  apply Finset.sum_congr rfl
  intro i _
  have hjoint : Measurable (fun ag : Y × Vector r => H i ((x, ag.2), ag.1)) :=
    (hHm i).comp ((measurable_const.prodMk measurable_snd).prodMk measurable_fst)
  have hi : Integrable (fun ag : Y × Vector r => H i ((x, ag.2), ag.1)) (ρ.prod (standardGaussian r)) :=
    (integrable_const _).mono' hjoint.aestronglyMeasurable
      ((Measure.quasiMeasurePreserving_fst.ae (hHb i)).mono (fun _ h => h _))
  calc
    _ = ∫ a, ∫ g, H i ((x, g), a) ∂standardGaussian r ∂ρ := by
      apply integral_congr_ae
      exact Filter.Eventually.of_forall (fun a => cap_convolutionFourthTensor_gaussian_split_rectangular s A C hgram t
        (B i (x, a)) (U i a) (V i a) (W i a) (Z i a))
    _ = _ := integral_integral_swap hi


theorem cap_integrable_gaussian_restorationFourthDerivative_rectangular
    {p r : ℕ} (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (x z y w : Vector p) (σ : ℝ) :
    Integrable (fun g => restorationFourthDerivative s ((σ • A).mulVec g + x) z y w)
      (standardGaussian r) := by
  simp_rw [restorationFourthDerivative_eq_coordinate, matrixQuadratic, Finset.mul_sum]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  apply integrable_finset_sum
  intro l _
  apply integrable_finset_sum
  intro m _
  have hi := integrable_bounded_test_comp (standardGaussian r) (fun g => (σ • A).mulVec g + x)
    (((continuous_const.matrix_mulVec continuous_id).measurable).add measurable_const) _ (s.continuous_fourthDerivative j k l m) _
    (fun a => s.norm_fourthDerivative_le a j k l m)
  convert ((hi.const_mul (w j * y k)).mul_const (z l)).mul_const (z m) using 1
  funext g
  ring

theorem cap_convolutionFourthExpectation_eq_product_rectangular
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (C : Matrix (Fin p) (Fin p) ℝ)
    (hgram : A*A.transpose=C*C.transpose) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (Y W v : Fin n → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) (_hσ : σ ≠ 0) :
    (∫ ω, ∑ i, s.convolutionFourthTensor (gaussianLaw (σ • C)) (V ω + v i ω)
      (A.mulVec (Z i ω)) (A.mulVec (Z i ω)) (Y i ω) (W i ω) ∂μ) =
      restorationFourthExpectation s μ A V Z Y W v σ := by
  have hscaled : (σ • A)*(σ • A).transpose = (σ • C)*(σ • C).transpose := by
    simp only [Matrix.transpose_smul,Matrix.smul_mul,Matrix.mul_smul,hgram]
  have hX (i : Fin n) : Measurable (fun z : Ω × Vector r => (σ • A).mulVec z.2 + V z.1 + v i z.1) :=
    ((((continuous_const.matrix_mulVec continuous_id).measurable).comp measurable_snd).add (hV.comp measurable_fst)).add ((hv i).comp measurable_fst)
  have hi : Integrable (fun z : Ω × Vector r => ∑ i, restorationFourthDerivative s
      ((σ • A).mulVec z.2 + V z.1 + v i z.1) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1))
      (μ.prod (standardGaussian r)) :=
    integrable_finset_sum _ (fun i _ => integrable_random_restorationFourthDerivative s μ A
      (Z i) (hZm i) (hZ i) (Y i) (W i) (hY i) (hW i) hδ (hYb i) (hWb i) _ (hX i))
  unfold restorationFourthExpectation
  rw [integral_prod _ hi]
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro ω
  have hfixed (i : Fin n) : Integrable (fun g => restorationFourthDerivative s
      ((σ • A).mulVec g + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)) (standardGaussian r) := by
    simpa only [add_assoc] using cap_integrable_gaussian_restorationFourthDerivative_rectangular s A
      (V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω) σ
  dsimp only
  rw [integral_finset_sum _ (fun i _ => hfixed i)]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [add_assoc] using cap_convolutionFourthTensor_rectangular s (σ • A) (σ • C) hscaled
    (V ω+v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)

end
end RectangleCLTArxivV1
