import RectangleCLTCompanion.SplitV4.ConditionalGaussianTransport

/-! The original-space B.2 derivative expectations equal the proved
fresh-Gaussian product expectations under exactly conditional joint-array
independence given H and Gaussian independence from H. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

abbrev RestorationAuxiliaryData (p r n : ℕ) :=
  (Fin n → Vector r) × (Fin n → Vector p) × (Fin n → Vector p) × (Fin n → Vector p)

def restorationAuxiliaryData {Ω : Type*} {p r n : ℕ}
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p) (ω : Ω) :
    RestorationAuxiliaryData p r n :=
  (fun i => Z i ω, fun i => Y i ω, fun i => W i ω, fun i => v i ω)

theorem measurable_restorationAuxiliaryData
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p)
    (hZ : ∀ i, Measurable (Z i)) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i)) :
    Measurable (restorationAuxiliaryData Z Y W v) :=
  (measurable_pi_lambda _ hZ).prodMk ((measurable_pi_lambda _ hY).prodMk
    ((measurable_pi_lambda _ hW).prodMk (measurable_pi_lambda _ hv)))

def restorationThirdDataTest {p r n : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    (z : (Vector p × RestorationAuxiliaryData p r n) × Vector r) : ℝ :=
  ∑ i, restorationThirdDerivative s
    ((σ • A).mulVec z.2 + z.1.1 + z.1.2.2.2.2 i)
    (A.mulVec (z.1.2.1 i)) (z.1.2.2.1 i)

def restorationFourthDataTest {p r n : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ)
    (z : (Vector p × RestorationAuxiliaryData p r n) × Vector r) : ℝ :=
  ∑ i, restorationFourthDerivative s
    ((σ • A).mulVec z.2 + z.1.1 + z.1.2.2.2.2 i)
    (A.mulVec (z.1.2.1 i)) (z.1.2.2.1 i) (z.1.2.2.2.1 i)

theorem measurable_restorationThirdDataTest {p r n : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    Measurable (restorationThirdDataTest (n := n) s A σ) := by
  have h3 (j l m : Fin p) := (s.continuous_thirdDerivative j l m).measurable
  unfold restorationThirdDataTest
  simp_rw [restorationThirdDerivative_eq_coordinate, matrixQuadratic]
  fun_prop

theorem measurable_restorationFourthDataTest {p r n : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) :
    Measurable (restorationFourthDataTest (n := n) s A σ) := by
  have h4 (j k l m : Fin p) := (s.continuous_fourthDerivative j k l m).measurable
  unfold restorationFourthDataTest
  simp_rw [restorationFourthDerivative_eq_coordinate, matrixQuadratic]
  fun_prop

theorem restoration_data_gaussian_identDistrib
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (V : Ω → Vector p) (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p)
    (hZ : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ = standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance)
      (MeasurableSpace.comap G inferInstance)) :
    @IdentDistrib Ω (Ω × Vector r) ((Vector p × RestorationAuxiliaryData p r n) × Vector r)
      mΩ (@Prod.instMeasurableSpace Ω (Vector r) mΩ inferInstance) inferInstance
      (fun ω => ((V ω, restorationAuxiliaryData Z Y W v ω), G ω))
      (fun z : Ω × Vector r => ((V z.1, restorationAuxiliaryData Z Y W v z.1), z.2))
      μ (@Measure.prod Ω (Vector r) mΩ inferInstance μ (standardGaussian r)) := by
  let K := MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance
  letI : MeasurableSpace Ω := mΩ
  have haux := @measurable_restorationAuxiliaryData Ω mΩ p r n Z Y W v hZ hY hW hv
  have hauxK : @Measurable Ω (RestorationAuxiliaryData p r n) K inferInstance
      (restorationAuxiliaryData Z Y W v) := Measurable.of_comap_le le_rfl
  have hD : @Measurable Ω (Vector p × RestorationAuxiliaryData p r n) (H ⊔ K) inferInstance
      (fun ω => (V ω, restorationAuxiliaryData Z Y W v ω)) :=
    (hV.mono le_sup_left le_rfl).prodMk (hauxK.mono le_sup_right le_rfl)
  have hi := indepFun_of_conditionalEventIndependence (mΩ := mΩ) μ H K hH haux.comap_le
    (fun ω => (V ω, restorationAuxiliaryData Z Y W v ω)) G hD hG hCI hHG
  exact independent_data_gaussian_identDistrib μ _ G ((hV.mono hH le_rfl).prodMk haux) hG hi hGlaw

theorem restorationThirdExpectation_conditional_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ = standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) :
    (∀ i, Integrable (fun ω => restorationThirdDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω)) μ) ∧
    (∑ i, ∫ ω, restorationThirdDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) ∂μ) =
      restorationThirdExpectation (mΩ := mΩ) s μ A V Z Y v σ := by
  letI : MeasurableSpace Ω := mΩ
  have hd := restoration_data_gaussian_identDistrib (mΩ := mΩ) μ H hH V hV Z Y W v hZm hY hW hv
    G hG hGlaw hHG hCI
  have hX (i : Fin n) : Measurable (fun z : Ω × Vector r =>
      (σ • A).mulVec z.2 + V z.1 + v i z.1) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      ((hV.mono hH le_rfl).comp measurable_fst)).add ((hv i).comp measurable_fst)
  let F (i : Fin n) (z : (Vector p × RestorationAuxiliaryData p r n) × Vector r) : ℝ :=
    restorationThirdDerivative s ((σ • A).mulVec z.2 + z.1.1 + z.1.2.2.2.2 i)
      (A.mulVec (z.1.2.1 i)) (z.1.2.2.1 i)
  have hF (i : Fin n) : Measurable (F i) := by
    have h3 (j l m : Fin p) := (s.continuous_thirdDerivative j l m).measurable
    dsimp only [F]
    simp_rw [restorationThirdDerivative_eq_coordinate, matrixQuadratic]
    fun_prop
  have hi (i : Fin n) : Integrable (fun ω => restorationThirdDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω)) μ := by
    have hip := integrable_random_restorationThirdDerivative s μ A (Z i) (hZm i) (hZ i)
      (Y i) (hY i) hδ (hYb i) _ (hX i)
    exact (hd.comp (hF i)).integrable_iff.mpr hip
  refine ⟨hi, ?_⟩
  rw [← integral_finset_sum _ (fun i _ => hi i)]
  simpa only [restorationThirdDataTest, restorationAuxiliaryData, restorationThirdExpectation] using
    (hd.comp (measurable_restorationThirdDataTest (n := n) s A σ)).integral_eq

theorem restorationFourthExpectation_conditional_transport
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {p r n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (H : MeasurableSpace Ω) (hH : H ≤ mΩ)
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p)
    (hV : @Measurable Ω (Vector p) H inferInstance V)
    (Z : Fin n → Ω → Vector r) (Y W v : Fin n → Ω → Vector p)
    (hZm : ∀ i, @Measurable Ω (Vector r) mΩ inferInstance (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j * Z i ω k) μ)
    (hY : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (Y i))
    (hW : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (W i))
    (hv : ∀ i, @Measurable Ω (Vector p) mΩ inferInstance (v i))
    (G : Ω → Vector r) (hG : @Measurable Ω (Vector r) mΩ inferInstance G)
    (hGlaw : @Measure.map Ω (Vector r) mΩ inferInstance G μ = standardGaussian r)
    (hHG : @Indep Ω H (MeasurableSpace.comap G inferInstance) mΩ μ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H
      (MeasurableSpace.comap (restorationAuxiliaryData Z Y W v) inferInstance)
      (MeasurableSpace.comap G inferInstance))
    {δ σ : ℝ} (hδ : 0 ≤ δ) (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ)
    (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ) :
    (∀ i, Integrable (fun ω => restorationFourthDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)) μ) ∧
    (∑ i, ∫ ω, restorationFourthDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω) ∂μ) =
      restorationFourthExpectation (mΩ := mΩ) s μ A V Z Y W v σ := by
  letI : MeasurableSpace Ω := mΩ
  have hd := restoration_data_gaussian_identDistrib (mΩ := mΩ) μ H hH V hV Z Y W v hZm hY hW hv
    G hG hGlaw hHG hCI
  have hX (i : Fin n) : Measurable (fun z : Ω × Vector r =>
      (σ • A).mulVec z.2 + V z.1 + v i z.1) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      ((hV.mono hH le_rfl).comp measurable_fst)).add ((hv i).comp measurable_fst)
  let F (i : Fin n) (z : (Vector p × RestorationAuxiliaryData p r n) × Vector r) : ℝ :=
    restorationFourthDerivative s ((σ • A).mulVec z.2 + z.1.1 + z.1.2.2.2.2 i)
      (A.mulVec (z.1.2.1 i)) (z.1.2.2.1 i) (z.1.2.2.2.1 i)
  have hF (i : Fin n) : Measurable (F i) := by
    have h4 (j k l m : Fin p) := (s.continuous_fourthDerivative j k l m).measurable
    dsimp only [F]
    simp_rw [restorationFourthDerivative_eq_coordinate, matrixQuadratic]
    fun_prop
  have hi (i : Fin n) : Integrable (fun ω => restorationFourthDerivative s
      ((σ • A).mulVec (G ω) + V ω + v i ω) (A.mulVec (Z i ω)) (Y i ω) (W i ω)) μ := by
    have hip := integrable_random_restorationFourthDerivative s μ A (Z i) (hZm i) (hZ i)
      (Y i) (W i) (hY i) (hW i) hδ (hYb i) (hWb i) _ (hX i)
    exact (hd.comp (hF i)).integrable_iff.mpr hip
  refine ⟨hi, ?_⟩
  rw [← integral_finset_sum _ (fun i _ => hi i)]
  simpa only [restorationFourthDataTest, restorationAuxiliaryData, restorationFourthExpectation] using
    (hd.comp (measurable_restorationFourthDataTest (n := n) s A σ)).integral_eq

end

end RectangleCLT.Companion.SplitV4
