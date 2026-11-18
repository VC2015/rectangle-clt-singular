import RectangleCLTArxivV1.SupplementalGRectangularTensor
import RectangleCLTArxivV1.SupplementalGScoreRestoration

/-! Exact finite-array decomposition and actual Fubini transport of the
signed fourth derivative into Gaussian-outer H3 and H2 expectations. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_sum_integral_prod_swap
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ] {N : ℕ}
    (μ : Measure Ω) [SFinite μ] (ν : Measure Γ) [SFinite ν]
    (F : Fin N → Ω × Γ → ℝ) (hF : ∀ i, Integrable (F i) (μ.prod ν)) :
    (∑ i, ∫ ω, ∫ g, F i (ω,g) ∂ν ∂μ) =
      ∫ g, ∫ ω, ∑ i, F i (ω,g) ∂μ ∂ν := by
  calc
    _ = ∑ i, ∫ z, F i z ∂μ.prod ν := Finset.sum_congr rfl (fun i _ => (integral_prod _ (hF i)).symm)
    _ = ∫ z, ∑ i, F i z ∂μ.prod ν := (integral_finset_sum _ (fun i _ => hF i)).symm
    _ = _ := integral_prod_symm _ (integrable_finset_sum _ (fun i _ => hF i))

theorem cap_integrable_bounded_coefficient_score
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Γ) [IsProbabilityMeasure ν]
    (K w : Ω × Γ → ℝ) (hK : Integrable K (μ.prod ν)) (hw : Measurable w)
    (hw1 : ∀ z, |w z| ≤ 1) (c : Ω → ℝ) (hc : Measurable c) {b : ℝ}
    (hcb : ∀ᵐ ω ∂μ, |c ω| ≤ b) :
    Integrable (fun z => c z.1*(K z*w z)) (μ.prod ν) := by
  have hm := (hc.comp measurable_fst).mul hw
  have hb : ∀ᵐ z ∂μ.prod ν, ‖c z.1*w z‖ ≤ b := by
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcb] with z hz
    rw [Real.norm_eq_abs,abs_mul]
    exact (mul_le_mul_of_nonneg_left (hw1 z) (abs_nonneg _)).trans (by simpa using hz)
  convert hK.bdd_mul' hm.aestronglyMeasurable hb using 1
  funext z
  dsimp only [Function.comp_apply]
  ring

theorem cap_original_pair_coefficient_abs_le {p r : ℕ}
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (f g : Face p) (Y W : Vector p) {δ : ℝ} (hδ : 0 ≤ δ) (hY : ‖Y‖ ≤ δ) (hW : ‖W‖ ≤ δ) :
    |capRectangularPairCoefficient A f g Y W| ≤ 4*δ^2 := by
  have hρ : |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| ≤ 1 :=
    abs_dotProduct_unit_le_one _ _ (capRectangularFactorNormal_unit A hdiag f) (capRectangularFactorNormal_unit A hdiag g)
  have hp (a b : Face p) : |normalDot a Y*normalDot b W| ≤ δ^2 := by
    rw [abs_mul]
    exact (mul_le_mul (abs_normalDot_le_of_norm_le a hY) (abs_normalDot_le_of_norm_le b hW)
      (abs_nonneg _) hδ).trans_eq (by ring)
  unfold capRectangularPairCoefficient
  calc
    _ ≤ |normalDot f Y*normalDot g W+normalDot g Y*normalDot f W|+
        |faceDot (capRectangularFactorNormal A f) (capRectangularFactorNormal A g)| *
          |normalDot f Y*normalDot f W+normalDot g Y*normalDot g W| := by rw [← abs_mul]; exact abs_sub _ _
    _ ≤ (δ^2+δ^2)+1*(δ^2+δ^2) := by
      apply add_le_add ((abs_add _ _).trans (add_le_add (hp f g) (hp g f)))
      exact mul_le_mul hρ ((abs_add _ _).trans (add_le_add (hp f f) (hp g g))) (abs_nonneg _) zero_le_one
    _ = _ := by ring

/-- Exact signed decomposition on any genuine probability space. All
Gaussian exchanges are justified by actual second moments and bounded
coefficient slots; no concentration or remainder estimate is assumed. -/
theorem cap_array_fourth_expectation_single_pair
    {Ω : Type*} [MeasurableSpace Ω] {p r N : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin N → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (Y W v : Fin N → Ω → Vector p) (hY : ∀ i, Measurable (Y i))
    (hW : ∀ i, Measurable (W i)) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ω ∂μ, ‖Y i ω‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ω ∂μ, ‖W i ω‖ ≤ δ)
    (hσ : σ ≠ 0) :
    restorationFourthExpectation s μ A V Z Y W v σ =
      -(1/(s.bandwidth*σ^3))*(∑ f, ∫ g, ∫ ω, ∑ i,
        ((normalDot f (Y i ω)*normalDot f (W i ω))*
          capThirdHermiteScore (capRectangularFactorNormal A f) (Z i ω) g)*
        selectorTupleWeight s ![f] ((σ • A).mulVec g+V ω+v i ω) ∂μ ∂standardGaussian r)+
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ f', ∫ g, ∫ ω, ∑ i,
        (capRectangularPairCoefficient A f f' (Y i ω) (W i ω)*repeatedDirectionScore g (Z i ω))*
        selectorTupleWeight s ![f,f'] ((σ • A).mulVec g+V ω+v i ω) ∂μ ∂standardGaussian r) := by
  let C := fun f i ω => normalDot f (Y i ω)*normalDot f (W i ω)
  let B := fun f g i ω => capRectangularPairCoefficient A f g (Y i ω) (W i ω)
  let X := fun i (z : Ω × Vector r) => (σ • A).mulVec z.2+V z.1+v i z.1
  let P := fun f i (z : Ω × Vector r) => C f i z.1*
    (capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1) z.2*selectorTupleWeight s ![f] (X i z))
  let Q := fun f g i (z : Ω × Vector r) => B f g i z.1*
    (repeatedDirectionScore z.2 (Z i z.1)*selectorTupleWeight s ![f,g] (X i z))
  let D := fun i (z : Ω × Vector r) => restorationFourthDerivative s (X i z) (A.mulVec (Z i z.1)) (Y i z.1) (W i z.1)
  have hXm (i : Fin N) : Measurable (X i) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)).add ((hv i).comp measurable_fst)
  have hCm (f : Face p) (i : Fin N) : Measurable (C f i) := by unfold C normalDot; split <;> fun_prop
  have hBm (f g : Face p) (i : Fin N) : Measurable (B f g i) := by unfold B capRectangularPairCoefficient normalDot; split <;> split <;> fun_prop
  have hCb (f : Face p) (i : Fin N) : ∀ᵐ ω ∂μ, |C f i ω| ≤ δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    rw [abs_mul]
    exact (mul_le_mul (abs_normalDot_le_of_norm_le f hy) (abs_normalDot_le_of_norm_le f hw)
      (abs_nonneg _) hδ).trans_eq (by ring)
  have hBb (f g : Face p) (i : Fin N) : ∀ᵐ ω ∂μ, |B f g i ω| ≤ 4*δ^2 := by
    filter_upwards [hYb i,hWb i] with ω hy hw
    exact cap_original_pair_coefficient_abs_le A hdiag f g (Y i ω) (W i ω) hδ hy hw
  have hPi (f : Face p) (i : Fin N) : Integrable (P f i) (μ.prod (standardGaussian r)) := by
    apply cap_integrable_bounded_coefficient_score μ (standardGaussian r) _ _
      (integrable_random_capThirdHermiteScore μ _ (Z i) (hZ i))
      (measurable_selectorTupleWeight_comp s ![f] _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hCm f i) (hCb f i)
  have hQi (f g : Face p) (i : Fin N) : Integrable (Q f g i) (μ.prod (standardGaussian r)) := by
    apply cap_integrable_bounded_coefficient_score μ (standardGaussian r) _ _
      (integrable_random_repeatedDirectionScore μ (Z i) (hZ i))
      (measurable_selectorTupleWeight_comp s ![f,g] _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hBm f g i) (hBb f g i)
  have hDi (i : Fin N) : Integrable (D i) (μ.prod (standardGaussian r)) :=
    integrable_random_restorationFourthDerivative s μ A (Z i) (hZm i) (hZ i) (Y i) (W i)
      (hY i) (hW i) hδ (hYb i) (hWb i) (X i) (hXm i)
  have hstart : restorationFourthExpectation s μ A V Z Y W v σ = ∑ i, ∫ ω, ∫ g, D i (ω,g) ∂standardGaussian r ∂μ := by
    unfold restorationFourthExpectation
    rw [integral_finset_sum _ (fun i _ => hDi i)]
    exact Finset.sum_congr rfl (fun i _ => integral_prod _ (hDi i))
  have hpoint (i : Fin N) (ω : Ω) : (∫ g, D i (ω,g) ∂standardGaussian r) =
      -(1/(s.bandwidth*σ^3))*(∑ f, ∫ g, P f i (ω,g) ∂standardGaussian r)+
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ f', ∫ g, Q f f' i (ω,g) ∂standardGaussian r) := by
    have ht := cap_rectangular_fourth_derivative_single_pair s A hdiag (V ω+v i ω) (Z i ω) (Y i ω) (W i ω) hσ
    simpa only [D,P,Q,C,B,X,add_assoc,integral_const_mul] using ht
  have houter (i : Fin N) : (∫ ω, ∫ g, D i (ω,g) ∂standardGaussian r ∂μ) =
      -(1/(s.bandwidth*σ^3))*(∑ f, ∫ ω, ∫ g, P f i (ω,g) ∂standardGaussian r ∂μ)+
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ f', ∫ ω, ∫ g, Q f f' i (ω,g) ∂standardGaussian r ∂μ) := by
    simp_rw [hpoint]
    rw [integral_add
      ((integrable_finset_sum _ (fun f _ => (hPi f i).integral_prod_left)).const_mul _)
      ((integrable_finset_sum _ (fun f _ => integrable_finset_sum _ (fun g _ => (hQi f g i).integral_prod_left))).const_mul _),
      integral_const_mul,integral_const_mul,
      integral_finset_sum _ (fun f _ => (hPi f i).integral_prod_left),
      integral_finset_sum _ (fun f _ => integrable_finset_sum _ (fun g _ => (hQi f g i).integral_prod_left))]
    simp_rw [integral_finset_sum _ (fun g _ => (hQi _ g i).integral_prod_left)]
  rw [hstart]
  simp_rw [houter]
  simp only [Finset.sum_add_distrib,← Finset.mul_sum]
  have hp : (∑ i, ∑ f, ∫ ω, ∫ g, P f i (ω,g) ∂standardGaussian r ∂μ) =
      ∑ f, ∫ g, ∫ ω, ∑ i, P f i (ω,g) ∂μ ∂standardGaussian r := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun f _ => cap_sum_integral_prod_swap μ (standardGaussian r) _ (hPi f))
  have hq : (∑ i, ∑ f, ∑ f', ∫ ω, ∫ g, Q f f' i (ω,g) ∂standardGaussian r ∂μ) =
      ∑ f, ∑ f', ∫ g, ∫ ω, ∑ i, Q f f' i (ω,g) ∂μ ∂standardGaussian r := by
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro f _
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun g _ => cap_sum_integral_prod_swap μ (standardGaussian r) _ (hQi f g))
  rw [hp,hq]
  dsimp only [P,Q,C,B,X]
  simp only [mul_assoc]

theorem cap_product_array_marginal
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {N : ℕ}
    (μ : Measure Ω) [SFinite μ] (κ : Measure Ξ) [SFinite κ]
    (F : Fin N → Ω × Ξ → ℝ) (hF : ∀ i, Integrable (F i) (μ.prod κ)) :
    (∫ z, ∑ i, F i z ∂μ.prod κ) = ∫ ω, ∑ i, ∫ ξ, F i (ω,ξ) ∂κ ∂μ := by
  rw [integral_finset_sum _ (fun i _ => hF i),
    integral_finset_sum _ (fun i _ => (hF i).integral_prod_left)]
  exact Finset.sum_congr rfl (fun i _ => integral_prod _ (hF i))

/-- The exact actual base/copy decomposition in the order used by signed
conditional restoration: Gaussian, base, finite observation sum, then copy.
Only ordinary moments and actual measurable bounded slots are inputs. -/
theorem cap_array_fourth_expectation_product_single_pair
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r N : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Measure Ξ) [IsProbabilityMeasure κ]
    (A : Matrix (Fin p) (Fin r) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1)
    (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j k, Integrable (fun ξ => Z i ξ j*Z i ξ k) κ)
    (Y W : Fin N → Ξ → Vector p) (hY : ∀ i, Measurable (Y i)) (hW : ∀ i, Measurable (W i))
    (v : Fin N → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    {δ σ : ℝ} (hδ : 0 ≤ δ)
    (hYb : ∀ i, ∀ᵐ ξ ∂κ, ‖Y i ξ‖ ≤ δ) (hWb : ∀ i, ∀ᵐ ξ ∂κ, ‖W i ξ‖ ≤ δ)
    (hσ : σ ≠ 0) :
    restorationFourthExpectation s (μ.prod κ) A (fun z => V z.1) (fun i z => Z i z.2)
      (fun i z => Y i z.2) (fun i z => W i z.2) v σ =
      -(1/(s.bandwidth*σ^3))*(∑ f, ∫ g, ∫ ω, ∑ i, ∫ ξ,
        ((normalDot f (Y i ξ)*normalDot f (W i ξ))*
          capThirdHermiteScore (capRectangularFactorNormal A f) (Z i ξ) g)*
        selectorTupleWeight s ![f] ((σ • A).mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r)+
      (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ f', ∫ g, ∫ ω, ∑ i, ∫ ξ,
        (capRectangularPairCoefficient A f f' (Y i ξ) (W i ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s ![f,f'] ((σ • A).mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r) := by
  let ν := μ.prod κ
  let C := fun f i (z : Ω × Ξ) => normalDot f (Y i z.2)*normalDot f (W i z.2)
  let B := fun f g i (z : Ω × Ξ) => capRectangularPairCoefficient A f g (Y i z.2) (W i z.2)
  let X := fun i (z : (Ω × Ξ) × Vector r) => (σ • A).mulVec z.2+V z.1.1+v i z.1
  let P := fun f i (z : (Ω × Ξ) × Vector r) =>
    (C f i z.1*capThirdHermiteScore (capRectangularFactorNormal A f) (Z i z.1.2) z.2)*selectorTupleWeight s ![f] (X i z)
  let Q := fun f g i (z : (Ω × Ξ) × Vector r) =>
    (B f g i z.1*repeatedDirectionScore z.2 (Z i z.1.2))*selectorTupleWeight s ![f,g] (X i z)
  have hZl (i : Fin N) (j k : Fin r) : Integrable (fun z : Ω × Ξ => Z i z.2 j*Z i z.2 k) ν := by
    simpa only [one_mul] using (integrable_const (1:ℝ) (μ := μ)).mul_prod (hZ i j k)
  have hYl (i : Fin N) : ∀ᵐ z ∂ν, ‖Y i z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae (hYb i)
  have hWl (i : Fin N) : ∀ᵐ z ∂ν, ‖W i z.2‖ ≤ δ := Measure.quasiMeasurePreserving_snd.ae (hWb i)
  have hXm (i : Fin N) : Measurable (X i) :=
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst.fst)).add ((hv i).comp measurable_fst)
  have hCm (f : Face p) (i : Fin N) : Measurable (C f i) := by unfold C normalDot; split <;> fun_prop
  have hBm (f g : Face p) (i : Fin N) : Measurable (B f g i) := by unfold B capRectangularPairCoefficient normalDot; split <;> split <;> fun_prop
  have hCb (f : Face p) (i : Fin N) : ∀ᵐ z ∂ν, |C f i z| ≤ δ^2 := by
    filter_upwards [hYl i,hWl i] with z hy hw
    rw [abs_mul]
    exact (mul_le_mul (abs_normalDot_le_of_norm_le f hy) (abs_normalDot_le_of_norm_le f hw)
      (abs_nonneg _) hδ).trans_eq (by ring)
  have hBb (f g : Face p) (i : Fin N) : ∀ᵐ z ∂ν, |B f g i z| ≤ 4*δ^2 := by
    filter_upwards [hYl i,hWl i] with z hy hw
    exact cap_original_pair_coefficient_abs_le A hdiag f g (Y i z.2) (W i z.2) hδ hy hw
  have hPi (f : Face p) (i : Fin N) : Integrable (P f i) (ν.prod (standardGaussian r)) := by
    have ht := cap_integrable_bounded_coefficient_score ν (standardGaussian r) _ _
      (integrable_random_capThirdHermiteScore ν (capRectangularFactorNormal A f) (fun z => Z i z.2) (hZl i))
      (measurable_selectorTupleWeight_comp s ![f] _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hCm f i) (hCb f i)
    simpa only [P,mul_assoc] using ht
  have hQi (f g : Face p) (i : Fin N) : Integrable (Q f g i) (ν.prod (standardGaussian r)) := by
    have ht := cap_integrable_bounded_coefficient_score ν (standardGaussian r) _ _
      (integrable_random_repeatedDirectionScore ν (fun z => Z i z.2) (hZl i))
      (measurable_selectorTupleWeight_comp s ![f,g] _ (hXm i))
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      _ (hBm f g i) (hBb f g i)
    simpa only [Q,mul_assoc] using ht
  have hsingle (f : Face p) : (∫ g, ∫ z, ∑ i, P f i (z,g) ∂ν ∂standardGaussian r) =
      ∫ g, ∫ ω, ∑ i, ∫ ξ, P f i ((ω,ξ),g) ∂κ ∂μ ∂standardGaussian r := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hPi f i).prod_left_ae)] with g hg
    exact cap_product_array_marginal μ κ (fun i z => P f i (z,g)) hg
  have hpair (f f' : Face p) : (∫ g, ∫ z, ∑ i, Q f f' i (z,g) ∂ν ∂standardGaussian r) =
      ∫ g, ∫ ω, ∑ i, ∫ ξ, Q f f' i ((ω,ξ),g) ∂κ ∂μ ∂standardGaussian r := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr (fun i => (hQi f f' i).prod_left_ae)] with g hg
    exact cap_product_array_marginal μ κ (fun i z => Q f f' i (z,g)) hg
  have ht := cap_array_fourth_expectation_single_pair s ν A hdiag (fun z => V z.1) (hV.comp measurable_fst)
    (fun i z => Z i z.2) (fun i => (hZm i).comp measurable_snd) hZl
    (fun i z => Y i z.2) (fun i z => W i z.2) v
    (fun i => (hY i).comp measurable_snd) (fun i => (hW i).comp measurable_snd) hv hδ hYl hWl hσ
  change restorationFourthExpectation s (μ.prod κ) A (fun z => V z.1) (fun i z => Z i z.2)
      (fun i z => Y i z.2) (fun i z => W i z.2) v σ =
    -(1/(s.bandwidth*σ^3))*(∑ f, ∫ g, ∫ z, ∑ i, P f i (z,g) ∂ν ∂standardGaussian r)+
    (1/(s.bandwidth^2*σ^2))*(∑ f, ∑ f', ∫ g, ∫ z, ∑ i, Q f f' i (z,g) ∂ν ∂standardGaussian r) at ht
  simp_rw [hsingle,hpair] at ht
  exact ht

end
end RectangleCLTArxivV1
