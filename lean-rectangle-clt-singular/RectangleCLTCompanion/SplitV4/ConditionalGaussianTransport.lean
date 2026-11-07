import Mathlib.Probability.Independence.Conditional
import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.IdentDistrib
import RectangleCLTCompanion.SplitV4.RestorationProductBounds

/-! Conditional independence used in B.2 implies actual independence
after averaging, because the Gaussian law given H is constant. The
event formulation works on arbitrary probability spaces. -/

open MeasureTheory ProbabilityTheory

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- Conditional independence written with genuine conditional expectations
of bounded indicators. This formulation needs no regular conditional law
or standard-Borel assumption on the underlying probability space. -/
def ConditionalEventIndependence {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) (H K L : MeasurableSpace Ω) : Prop :=
  ∀ S T, MeasurableSet[K] S → MeasurableSet[L] T →
    μ[(S ∩ T).indicator (fun _ => (1 : ℝ)) | H] =ᵐ[μ]
      fun ω => μ[S.indicator (fun _ => (1 : ℝ)) | H] ω *
        μ[T.indicator (fun _ => (1 : ℝ)) | H] ω

theorem conditionalEventIndependence_of_condIndep
    {Ω : Type*} [mΩ : MeasurableSpace Ω] [StandardBorelSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K L : MeasurableSpace Ω)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (hL : L ≤ mΩ)
    (h : @CondIndep Ω H K L mΩ inferInstance hH μ inferInstance) :
    ConditionalEventIndependence (mΩ := mΩ) μ H K L :=
  (condIndep_iff H K L hH hK hL μ).mp h

theorem indep_of_conditionalEventIndependence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K L : MeasurableSpace Ω)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (hL : L ≤ mΩ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H K L)
    (hHL : @Indep Ω H L mΩ μ) : @Indep Ω K L mΩ μ := by
  rw [Indep_iff]
  intro S T hS hT
  have hS₀ : MeasurableSet[mΩ] S := hK _ hS
  have hT₀ : MeasurableSet[mΩ] T := hL _ hT
  have hconst : μ[T.indicator (fun _ => (1 : ℝ)) | H] =ᵐ[μ] fun _ => μ.real T := by
    have hm : StronglyMeasurable[L] (T.indicator (fun _ : Ω => (1 : ℝ))) :=
      stronglyMeasurable_const.indicator hT
    have he := condExp_indep_eq hL hH hm hHL.symm
    simpa only [integral_indicator hT₀, setIntegral_const, smul_eq_mul, mul_one] using he
  have heq : μ.real (S ∩ T) = μ.real S * μ.real T := by
    calc
      _ = ∫ ω, μ[(S ∩ T).indicator (fun _ => (1 : ℝ)) | H] ω ∂μ := by
        rw [integral_condExp hH, integral_indicator (hS₀.inter hT₀), setIntegral_const]
        simp
      _ = ∫ ω, μ[S.indicator (fun _ => (1 : ℝ)) | H] ω * μ.real T ∂μ := by
        apply integral_congr_ae
        filter_upwards [hCI S T hS hT, hconst] with ω hc ht
        rw [hc, ht]
      _ = (∫ ω, μ[S.indicator (fun _ => (1 : ℝ)) | H] ω ∂μ) * μ.real T := integral_mul_const _ _
      _ = μ.real S * μ.real T := by
        rw [integral_condExp hH, integral_indicator hS₀, setIntegral_const]
        simp
  apply ENNReal.toReal_eq_toReal (measure_ne_top _ _) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) |>.mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using heq

theorem conditional_intersections_measure
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K L : MeasurableSpace Ω)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (hL : L ≤ mΩ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H K L)
    (hHL : @Indep Ω H L mΩ μ)
    {P S T : Set Ω} (hP : MeasurableSet[H] P) (hS : MeasurableSet[K] S) (hT : MeasurableSet[L] T) :
    μ ((P ∩ S) ∩ T) = μ (P ∩ S) * μ T := by
  letI : MeasurableSpace Ω := mΩ
  have hS₀ : MeasurableSet[mΩ] S := hK _ hS
  have hT₀ : MeasurableSet[mΩ] T := hL _ hT
  have hconst : μ[T.indicator (fun _ => (1 : ℝ)) | H] =ᵐ[μ] fun _ => μ.real T := by
    have hm : StronglyMeasurable[L] (T.indicator (fun _ : Ω => (1 : ℝ))) :=
      stronglyMeasurable_const.indicator hT
    have he := condExp_indep_eq hL hH hm hHL.symm
    simpa only [integral_indicator hT₀, setIntegral_const, smul_eq_mul, mul_one] using he
  have heq : μ.real ((P ∩ S) ∩ T) = μ.real (P ∩ S) * μ.real T := by
    calc
      _ = ∫ ω in P, μ[(S ∩ T).indicator (fun _ => (1 : ℝ)) | H] ω ∂μ := by
        rw [setIntegral_condExp hH ((integrable_const (μ := μ) (1 : ℝ)).indicator (hS₀.inter hT₀)) hP,
          setIntegral_indicator (hS₀.inter hT₀), setIntegral_const]
        simp only [smul_eq_mul, mul_one, Set.inter_assoc]
      _ = ∫ ω in P, μ[S.indicator (fun _ => (1 : ℝ)) | H] ω * μ.real T ∂μ := by
        apply setIntegral_congr_ae (hH _ hP)
        filter_upwards [hCI S T hS hT, hconst] with ω hc ht _
        rw [hc, ht]
      _ = (∫ ω in P, μ[S.indicator (fun _ => (1 : ℝ)) | H] ω ∂μ) * μ.real T := integral_mul_const _ _
      _ = μ.real (P ∩ S) * μ.real T := by
        rw [setIntegral_condExp hH ((integrable_const (μ := μ) (1 : ℝ)).indicator hS₀) hP,
          setIntegral_indicator hS₀, setIntegral_const]
        simp
  apply ENNReal.toReal_eq_toReal (measure_ne_top _ _) (ENNReal.mul_ne_top (measure_ne_top _ _) (measure_ne_top _ _)) |>.mp
  simpa only [measureReal_def, ENNReal.toReal_mul] using heq

def sigmaFieldIntersections {Ω : Type*} (H K : MeasurableSpace Ω) : Set (Set Ω) :=
  {S | ∃ P Q, MeasurableSet[H] P ∧ MeasurableSet[K] Q ∧ S = P ∩ Q}

theorem isPiSystem_sigmaFieldIntersections {Ω : Type*} (H K : MeasurableSpace Ω) :
    IsPiSystem (sigmaFieldIntersections H K) := by
  rintro S ⟨P, Q, hP, hQ, rfl⟩ T ⟨R, U, hR, hU, rfl⟩ _
  refine ⟨P ∩ R, Q ∩ U, hP.inter hR, hQ.inter hU, ?_⟩
  ext x
  simp only [Set.mem_inter_iff]
  tauto

theorem generateFrom_sigmaFieldIntersections {Ω : Type*} (H K : MeasurableSpace Ω) :
    MeasurableSpace.generateFrom (sigmaFieldIntersections H K) = H ⊔ K := by
  apply le_antisymm
  · apply MeasurableSpace.generateFrom_le
    rintro S ⟨P, Q, hP, hQ, rfl⟩
    exact ((show H ≤ H ⊔ K from le_sup_left) P hP).inter
      ((show K ≤ H ⊔ K from le_sup_right) Q hQ)
  · apply sup_le
    · intro P hP
      have he := MeasurableSpace.GenerateMeasurable.basic (P ∩ Set.univ)
        (show P ∩ Set.univ ∈ sigmaFieldIntersections H K from ⟨P, Set.univ, hP, MeasurableSet.univ, rfl⟩)
      simpa using he
    · intro Q hQ
      have he := MeasurableSpace.GenerateMeasurable.basic (Set.univ ∩ Q)
        (show Set.univ ∩ Q ∈ sigmaFieldIntersections H K from ⟨Set.univ, Q, MeasurableSet.univ, hQ, rfl⟩)
      simpa using he

/-- Adjoining all H-measurable information is valid under the source's
weak conditional-independence assumptions. In particular, one may include
V0 in the joint array data before transporting to a Gaussian product law. -/
theorem indep_sup_of_conditionalEventIndependence
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K L : MeasurableSpace Ω)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (hL : L ≤ mΩ)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H K L)
    (hHL : @Indep Ω H L mΩ μ) : @Indep Ω (H ⊔ K) L mΩ μ := by
  apply IndepSets.indep (sup_le hH hK) hL (isPiSystem_sigmaFieldIntersections H K)
    (@MeasurableSpace.isPiSystem_measurableSet Ω L)
    (generateFrom_sigmaFieldIntersections H K).symm
    (@MeasurableSpace.generateFrom_measurableSet Ω L).symm
  rw [IndepSets_iff]
  rintro S T ⟨P, Q, hP, hQ, rfl⟩ hT
  exact conditional_intersections_measure (mΩ := mΩ) μ H K L hH hK hL hCI hHL hP hQ hT

theorem indepFun_of_conditionalEventIndependence
    {Ω E Γ : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E] [mΓ : MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (H K : MeasurableSpace Ω)
    (hH : H ≤ mΩ) (hK : K ≤ mΩ) (D : Ω → E) (G : Ω → Γ)
    (hD : @Measurable Ω E (H ⊔ K) mE D) (hG : @Measurable Ω Γ mΩ mΓ G)
    (hCI : ConditionalEventIndependence (mΩ := mΩ) μ H K (MeasurableSpace.comap G mΓ))
    (hHG : @Indep Ω H (MeasurableSpace.comap G mΓ) mΩ μ) :
    @IndepFun Ω E Γ mΩ mE mΓ D G μ := by
  have hi := indep_sup_of_conditionalEventIndependence (mΩ := mΩ)
    μ H K (MeasurableSpace.comap G mΓ) hH hK hG.comap_le hCI hHG
  change @Indep Ω (MeasurableSpace.comap D mE) (MeasurableSpace.comap G mΓ) mΩ μ
  exact indep_of_indep_of_le_left hi hD.comap_le

/-- Replacing the original Gaussian by a fresh independent Gaussian has
the same complete joint law with the non-Gaussian data. -/
theorem independent_data_gaussian_identDistrib
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → E) (G : Ω → Vector r)
    (hD : Measurable D) (hG : Measurable G) (hDG : IndepFun D G μ)
    (hGlaw : μ.map G = standardGaussian r) :
    IdentDistrib (fun ω => (D ω, G ω)) (fun z : Ω × Vector r => (D z.1, z.2))
      μ (μ.prod (standardGaussian r)) := by
  refine ⟨(hD.prodMk hG).aemeasurable,
    ((hD.comp measurable_fst).prodMk measurable_snd).aemeasurable, ?_⟩
  calc
    _ = (μ.map D).prod (μ.map G) :=
      (indepFun_iff_map_prod_eq_prod_map_map hD.aemeasurable hG.aemeasurable).mp hDG
    _ = (μ.map D).prod (standardGaussian r) := by rw [hGlaw]
    _ = _ := by
      simpa only [Measure.map_id, Prod.map_apply, id_eq] using
        Measure.map_prod_map μ (standardGaussian r) hD measurable_id

theorem independent_data_gaussian_test_transport
    {Ω E B : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    [NormedAddCommGroup B] [NormedSpace ℝ B] [CompleteSpace B] [MeasurableSpace B]
    [BorelSpace B] {r : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (D : Ω → E) (G : Ω → Vector r)
    (hD : Measurable D) (hG : Measurable G) (hDG : IndepFun D G μ)
    (hGlaw : μ.map G = standardGaussian r) (F : E × Vector r → B) (hF : Measurable F)
    (hFi : Integrable (fun z : Ω × Vector r => F (D z.1, z.2)) (μ.prod (standardGaussian r))) :
    Integrable (fun ω => F (D ω, G ω)) μ ∧
      (∫ ω, F (D ω, G ω) ∂μ) = ∫ z : Ω × Vector r, F (D z.1, z.2) ∂μ.prod (standardGaussian r) := by
  have hd := (independent_data_gaussian_identDistrib μ D G hD hG hDG hGlaw).comp hF
  exact ⟨hd.integrable_iff.mpr hFi, hd.integral_eq⟩

end

end RectangleCLT.Companion.SplitV4
