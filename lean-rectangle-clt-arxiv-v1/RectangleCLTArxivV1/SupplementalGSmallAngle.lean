import RectangleCLTArxivV1.SupplementalGPairDerivative
import RectangleCLTArxivV1.SupplementalGPairMoments
import RectangleCLTArxivV1.SupplementalGFaceMass

/-! The actual positive-weight small-angle branch of Supplemental G.3.
Copy directions and displacements may depend jointly on copies and base;
the angular gain is obtained from genuine copy second moments. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem measurable_capSoftFaceSecond_comp
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (s : FaceSmoother p)
    (S : Finset (Face p)) (Y X : Ω → Vector p) (hY : Measurable Y) (hX : Measurable X) :
    Measurable (fun ω => capSoftFaceSecond s S (Y ω) (X ω)) := by
  have hpi (f : Face p) : Measurable (fun ω => (s.weights (X ω)).pi f) :=
    (s.continuous_pi f).measurable.comp hX
  have hnv (f : Face p) : Measurable (fun ω => FaceWeights.directionalValue f (Y ω)) := by
    unfold FaceWeights.directionalValue
    split <;> fun_prop
  have hnd (f : Face p) : Measurable (fun ω => normalDot f (Y ω)) := by
    unfold normalDot
    split <;> fun_prop
  have hmean : Measurable (fun ω => (s.weights (X ω)).directionalMean (Y ω)) := by
    unfold FaceWeights.directionalMean
    exact Finset.measurable_sum _ (fun f _ => (hpi f).mul (hnv f))
  have hsecond : Measurable (fun ω => (s.weights (X ω)).directionalSecondMoment (Y ω)) := by
    unfold FaceWeights.directionalSecondMoment
    exact Finset.measurable_sum _ (fun f _ => (hpi f).mul ((hnv f).pow_const 2))
  have hsum : Measurable (fun ω => ∑ f ∈ S, normalDot f (Y ω)) :=
    Finset.measurable_sum _ (fun f _ => hnd f)
  have hw := (s.continuous_softFaceWeight S).measurable.comp hX
  change Measurable (fun ω => s.softFaceWeight S (X ω)/s.bandwidth^2*
    (((∑ f ∈ S, normalDot f (Y ω))-((S.card : ℝ)+1)*(s.weights (X ω)).directionalMean (Y ω))^2-
      ((S.card : ℝ)+1)*((s.weights (X ω)).directionalSecondMoment (Y ω)-
        (s.weights (X ω)).directionalMean (Y ω)^2)))
  exact (hw.div_const _).mul
    (((hsum.sub (hmean.const_mul _)).pow_const 2).sub
      ((hsecond.sub (hmean.pow_const 2)).const_mul _))

theorem cap_pair_coefficient_integrable
    {Ξ : Type*} [MeasurableSpace Ξ] {r : ℕ} (κ : Measure Ξ)
    (Z W : Ξ → Vector r) (hZm : Measurable Z) (hWm : Measurable W)
    (hZ : ∀ j k, Integrable (fun ξ => Z ξ j*Z ξ k) κ)
    (hW : ∀ j k, Integrable (fun ξ => W ξ j*W ξ k) κ)
    (u v : Vector r) (hρ : |dotProduct u v| < 1) :
    Integrable (fun ξ => capPairCoefficient u v (Z ξ) (W ξ)) κ := by
  have hi (e : Vector r) : Integrable (fun ξ => dotProduct e (Z ξ)*dotProduct e (W ξ)) κ := by
    have hh := cap_integrable_abs_faceDot_mul κ Z W hZm hWm hZ hW e
    have hm : Measurable (fun ξ => dotProduct e (Z ξ)*dotProduct e (W ξ)) := by unfold dotProduct; fun_prop
    apply hh.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun ξ => by rfl)
  have hh := (((hi u).add (hi v)).sub ((hi (capAngularDirection u v)).const_mul 2)).const_mul
    (capSign (dotProduct u v)*(1-|dotProduct u v|))
  convert hh using 1
  funext ξ
  rw [capPairCoefficient_angular_identity u v (Z ξ) (W ξ) hρ]
  simp only [Pi.sub_apply,Pi.add_apply]
  ring

/-- Actual copy expectation before applying the base concentration theorem.
No independence is required between the two coefficient slots, the third
direction, the scalar kernel, or the bounded displacement. -/
theorem cap_small_angle_copy_bound
    {Ξ : Type*} [MeasurableSpace Ξ] {N p r : ℕ} (κ : Measure Ξ)
    (s : FaceSmoother p) (S : Finset (Face p)) (hcard : S.card ≤ 2) (x : Vector p)
    (Z W : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i)) (hWm : ∀ i, Measurable (W i))
    (hZ : ∀ i j k, Integrable (fun ξ => Z i ξ j*Z i ξ k) κ)
    (hW : ∀ i j k, Integrable (fun ξ => W i ξ j*W i ξ k) κ)
    (u v : Vector r) (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1) (hρ : |dotProduct u v| < 1)
    (c : Fin N → Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (D d : Fin N → Ξ → Vector p) (hD : ∀ i, Measurable (D i)) (hd : ∀ i, Measurable (d i))
    {b K Δ R : ℝ} (hb : 0 ≤ b) (_hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (_hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ ξ ∂κ, |c i ξ| ≤ b)
    (hDb : ∀ i, ∀ᵐ ξ ∂κ, ‖D i ξ‖ ≤ Δ)
    (hdb : ∀ i, ∀ᵐ ξ ∂κ, ‖d i ξ‖ ≤ R)
    (hbZ : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (Z i ξ))^2 ∂κ ≤ K*vectorNormSq e)
    (hbW : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (W i ξ))^2 ∂κ ≤ K*vectorNormSq e) :
    (∀ i, Integrable (fun ξ => (c i ξ*capPairCoefficient u v (Z i ξ) (W i ξ))*
      capSoftFaceSecond s S (D i ξ) (x+d i ξ)) κ) ∧
    (∑ i, ∫ ξ, |(c i ξ*capPairCoefficient u v (Z i ξ) (W i ξ))*
      capSoftFaceSecond s S (D i ξ) (x+d i ξ)| ∂κ) ≤
      (112*b*K*Δ^2/s.bandwidth^2*Real.exp (5*R/s.bandwidth))*(1-|dotProduct u v|)*s.softFaceWeight S x := by
  let L := b*(28*Δ^2/s.bandwidth^2*Real.exp (5*R/s.bandwidth))*s.softFaceWeight S x
  have hL : 0 ≤ L := by dsimp [L]; exact mul_nonneg (mul_nonneg hb (by positivity)) (s.softFaceWeight_nonneg S x)
  have hBi (i : Fin N) := cap_pair_coefficient_integrable κ (Z i) (W i) (hZm i) (hWm i) (hZ i) (hW i) u v hρ
  have hm (i : Fin N) : Measurable (fun ξ => (c i ξ*capPairCoefficient u v (Z i ξ) (W i ξ))*
      capSoftFaceSecond s S (D i ξ) (x+d i ξ)) := by
    have hB : Measurable (fun ξ => capPairCoefficient u v (Z i ξ) (W i ξ)) := by unfold capPairCoefficient dotProduct; fun_prop
    exact ((hc i).mul hB).mul (measurable_capSoftFaceSecond_comp s S (D i) (fun ξ => x+d i ξ)
      (hD i) (measurable_const.add (hd i)))
  have hpoint (i : Fin N) : ∀ᵐ ξ ∂κ,
      |(c i ξ*capPairCoefficient u v (Z i ξ) (W i ξ))*capSoftFaceSecond s S (D i ξ) (x+d i ξ)| ≤
        L*|capPairCoefficient u v (Z i ξ) (W i ξ)| := by
    filter_upwards [hcb i,hDb i,hdb i] with ξ hcξ hDξ hdξ
    rw [abs_mul,abs_mul]
    have ht := capSoftFaceSecond_shift_abs_le s S hcard x (D i ξ) hΔ hDξ hdξ
    have hs := mul_le_mul (mul_le_mul_of_nonneg_right hcξ (abs_nonneg (capPairCoefficient u v (Z i ξ) (W i ξ)))) ht
      (abs_nonneg _) (mul_nonneg hb (abs_nonneg _))
    exact hs.trans_eq (by dsimp only [L]; ring)
  have hFi (i : Fin N) : Integrable (fun ξ => (c i ξ*capPairCoefficient u v (Z i ξ) (W i ξ))*
      capSoftFaceSecond s S (D i ξ) (x+d i ξ)) κ :=
    ((hBi i).abs.const_mul L).mono' (hm i).aestronglyMeasurable
      ((hpoint i).mono (fun ξ hh => by simpa only [Real.norm_eq_abs] using hh))
  refine ⟨hFi, ?_⟩
  have hi (i : Fin N) := integral_mono_ae (hFi i).abs ((hBi i).abs.const_mul L) (hpoint i)
  have hs := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hi i)
  simp only [integral_const_mul,← Finset.mul_sum] at hs
  have hmoment := cap_pair_coefficient_integral_abs_le κ Z W hZm hWm hZ hW hbZ hbW u v hu hv hρ
  exact (hs.trans (mul_le_mul_of_nonneg_left hmoment hL)).trans_eq (by dsimp only [L]; ring)

theorem cap_softFaceWeight_pair_eq {p : ℕ} (s : FaceSmoother p)
    (f g : Face p) (hfg : f ≠ g) (x : Vector p) :
    s.softFaceWeight {f,g} x = selectorTupleWeight s ![f,g] x := by
  classical
  simp [FaceSmoother.softFaceWeight,selectorTupleWeight,FaceSmoother.pi,hfg]

/-- The small-angle pair expectation with its actual G.2 mass supplied by
the bounded-plus-Gaussian model. There is no selector-mass premise. -/
theorem cap_small_angle_actual_expectation
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n q N p r : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (A : Matrix (Fin 2) (Fin q) ℝ)
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f g : Face p) (hfg : f ≠ g)
    (Y : Ω × Vector q → Vector p) (hY : Measurable Y)
    (u v : Vector r) (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1)
    (hρ : |dotProduct u v| < 1) {v₀ : ℝ} (hv₀ : (1/2:ℝ) ≤ v₀)
    (hcov : capMixedCovariance μ X A =
      !![v₀,v₀*dotProduct u v;v₀*dotProduct u v,v₀])
    (a₀ a₁ : ℝ)
    (hproj₀ : ∀ z, normalDot f (Y z) = capMixedValue X A z 0+a₀)
    (hproj₁ : ∀ z, normalDot g (Y z) = capMixedValue X A z 1+a₁)
    (κ : Measure Ξ) [SFinite κ]
    (Z W : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i)) (hWm : ∀ i, Measurable (W i))
    (hZ : ∀ i j k, Integrable (fun ξ => Z i ξ j*Z i ξ k) κ)
    (hW : ∀ i j k, Integrable (fun ξ => W i ξ j*W i ξ k) κ)
    (c : Fin N → (Ω × Vector q) × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (D d : Fin N → (Ω × Vector q) × Ξ → Vector p)
    (hD : ∀ i, Measurable (D i)) (hd : ∀ i, Measurable (d i))
    {b K Δ R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, |c i z| ≤ b)
    (hDb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖D i z‖ ≤ Δ)
    (hdb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖d i z‖ ≤ R)
    (hbZ : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (Z i ξ))^2 ∂κ ≤ K*vectorNormSq e)
    (hbW : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (W i ξ))^2 ∂κ ≤ K*vectorNormSq e) :
    Integrable (fun ω => ∑ i, ∫ ξ,
      (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
        capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ)
          (μ.prod (standardGaussian q)) ∧
    |∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
        capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q)| ≤
      7168*Real.exp (1+5*R/s.bandwidth)*Real.pi^3*b*K*Δ^2*
        Real.sqrt (1-(dotProduct u v)^2) := by
  let ν := μ.prod (standardGaussian q)
  let F := fun ω => ∑ i, ∫ ξ,
    (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
      capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ
  let C := 112*b*K*Δ^2/s.bandwidth^2*Real.exp (5*R/s.bandwidth)
  let w := fun ω => s.softFaceWeight {f,g} (Y ω)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  have hang : 0 ≤ 1-|dotProduct u v| := by linarith
  have hcard : ({f,g} : Finset (Face p)).card ≤ 2 := by
    classical
    simp [hfg]
  have hfm : StronglyMeasurable F := by
    apply Finset.stronglyMeasurable_sum
    intro i _
    have hB : Measurable (fun z : (Ω × Vector q) × Ξ => capPairCoefficient u v (Z i z.2) (W i z.2)) := by
      unfold capPairCoefficient dotProduct
      fun_prop
    have hsec := measurable_capSoftFaceSecond_comp s {f,g} (D i)
      (fun z => Y z.1+d i z) (hD i) ((hY.comp measurable_fst).add (hd i))
    exact (((hc i).mul hB).mul hsec).stronglyMeasurable.integral_prod_right'
  have hwm : Measurable w := (s.continuous_softFaceWeight {f,g}).measurable.comp hY
  have hwi : Integrable w ν :=
    (integrable_const (1:ℝ)).mono' hwm.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (s.softFaceWeight_nonneg _ _)]
        exact s.softFaceWeight_le_one _ _))
  have hca (i : Fin N) : ∀ᵐ ω ∂ν, ∀ᵐ ξ ∂κ, |c i (ω,ξ)| ≤ b := Measure.ae_ae_of_ae_prod (hcb i)
  have hDa (i : Fin N) : ∀ᵐ ω ∂ν, ∀ᵐ ξ ∂κ, ‖D i (ω,ξ)‖ ≤ Δ := Measure.ae_ae_of_ae_prod (hDb i)
  have hda (i : Fin N) : ∀ᵐ ω ∂ν, ∀ᵐ ξ ∂κ, ‖d i (ω,ξ)‖ ≤ R := Measure.ae_ae_of_ae_prod (hdb i)
  have hpoint : ∀ᵐ ω ∂ν, |F ω| ≤ (C*(1-|dotProduct u v|))*w ω := by
    filter_upwards [ae_all_iff.mpr hca,ae_all_iff.mpr hDa,ae_all_iff.mpr hda] with ω hcω hDω hdω
    have ht := cap_small_angle_copy_bound κ s {f,g} hcard (Y ω) Z W hZm hWm hZ hW
      u v hu hv hρ (fun i ξ => c i (ω,ξ)) (fun i => (hc i).comp measurable_prodMk_left)
      (fun i ξ => D i (ω,ξ)) (fun i ξ => d i (ω,ξ))
      (fun i => (hD i).comp measurable_prodMk_left) (fun i => (hd i).comp measurable_prodMk_left)
      hb hK hΔ hR (fun i => hcω i) (fun i => hDω i) (fun i => hdω i) hbZ hbW
    calc
      _ ≤ ∑ i, |∫ ξ, (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
          capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, ∫ ξ, |(c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
          capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ))| ∂κ := by
        apply Finset.sum_le_sum
        intro i _
        simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun ξ => (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
            capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)))
      _ ≤ _ := ht.2
  have hFi : Integrable F ν := (hwi.const_mul (C*(1-|dotProduct u v|))).mono' hfm.aestronglyMeasurable
    (hpoint.mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω))
  refine ⟨hFi, ?_⟩
  have hi := norm_integral_le_of_norm_le (f := F) (hwi.const_mul (C*(1-|dotProduct u v|)))
    (hpoint.mono (fun ω hω => by simpa only [Real.norm_eq_abs] using hω))
  rw [Real.norm_eq_abs,integral_const_mul] at hi
  have hρsq : (dotProduct u v)^2 < 1 := by nlinarith [sq_abs (dotProduct u v),abs_nonneg (dotProduct u v)]
  have hmass := cap_original_pair_face_mass hdata A hv₀ hρsq hcov s hband f g Y hY a₀ a₁ hproj₀ hproj₁
  have heq : (∫ ω, w ω ∂ν) = (∫ ω, selectorTupleWeight s ![f,g] (Y ω) ∂ν) := by
    apply integral_congr_ae
    exact ae_of_all _ (fun ω => cap_softFaceWeight_pair_eq s f g hfg (Y ω))
  rw [heq] at hi
  have hangle := cap_angle_loss_cancels hρ
  have hspos : 0 < Real.sqrt (1-(dotProduct u v)^2) := Real.sqrt_pos.mpr (by linarith)
  have hmono := mul_le_mul_of_nonneg_left hmass (mul_nonneg hC hang)
  have hcanc : (C*(1-|dotProduct u v|))*(64*Real.exp 1*Real.pi^3*s.bandwidth^2/
      Real.sqrt (1-(dotProduct u v)^2)) =
      (7168*Real.exp (1+5*R/s.bandwidth)*Real.pi^3*b*K*Δ^2)*
        ((1-|dotProduct u v|)/Real.sqrt (1-(dotProduct u v)^2)) := by
    dsimp only [C]
    rw [Real.exp_add]
    field_simp [s.bandwidth_pos.ne',hspos.ne']
    ring
  exact (hi.trans (hmono.trans_eq hcanc)).trans
    (mul_le_mul_of_nonneg_left hangle (by positivity))

/-- The normalized small-angle pair remainder, with universal constant and
all concentration and moment inputs discharged by actual model data. -/
theorem cap_small_angle_complementary_remainder
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {n q N p r : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (A : Matrix (Fin 2) (Fin q) ℝ)
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f g : Face p) (hfg : f ≠ g)
    (Y : Ω × Vector q → Vector p) (hY : Measurable Y)
    (u v : Vector r) (hu : vectorNormSq u = 1) (hv : vectorNormSq v = 1)
    (hρ : |dotProduct u v| < 1) {v₀ : ℝ} (hv₀ : (1/2:ℝ) ≤ v₀)
    (hcov : capMixedCovariance μ X A =
      !![v₀,v₀*dotProduct u v;v₀*dotProduct u v,v₀])
    (a₀ a₁ : ℝ)
    (hproj₀ : ∀ z, normalDot f (Y z) = capMixedValue X A z 0+a₀)
    (hproj₁ : ∀ z, normalDot g (Y z) = capMixedValue X A z 1+a₁)
    (κ : Measure Ξ) [SFinite κ]
    (Z W : Fin N → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i)) (hWm : ∀ i, Measurable (W i))
    (hZ : ∀ i j k, Integrable (fun ξ => Z i ξ j*Z i ξ k) κ)
    (hW : ∀ i j k, Integrable (fun ξ => W i ξ j*W i ξ k) κ)
    (c : Fin N → (Ω × Vector q) × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (D d : Fin N → (Ω × Vector q) × Ξ → Vector p)
    (hD : ∀ i, Measurable (D i)) (hd : ∀ i, Measurable (d i))
    {b K Δ R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hΔ : 0 ≤ Δ) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, |c i z| ≤ b)
    (hDb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖D i z‖ ≤ Δ)
    (hdb : ∀ i, ∀ᵐ z ∂(μ.prod (standardGaussian q)).prod κ, ‖d i z‖ ≤ R)
    (hbZ : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (Z i ξ))^2 ∂κ ≤ K*vectorNormSq e)
    (hbW : ∀ e : Vector r, ∑ i, ∫ ξ, (faceDot e (W i ξ))^2 ∂κ ≤ K*vectorNormSq e)
    (hRh : R ≤ s.bandwidth) :
    |(1/s.bandwidth^2)*(∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
        capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q))| ≤
      7168*Real.exp 6*Real.pi^3*b*K*Δ^2*Real.sqrt (1-(dotProduct u v)^2)/s.bandwidth^2 := by
  have ht := cap_small_angle_actual_expectation hdata A s hband f g hfg Y hY u v hu hv hρ hv₀ hcov
    a₀ a₁ hproj₀ hproj₁ κ Z W hZm hWm hZ hW c hc D d hD hd hb hK hΔ hR hcb hDb hdb hbZ hbW
  have hh := s.bandwidth_pos
  have hRdiv : R/s.bandwidth ≤ 1 := (div_le_iff₀ hh).mpr (by linarith)
  have he : Real.exp (1+5*R/s.bandwidth) ≤ Real.exp 6 := by
    apply Real.exp_le_exp.mpr
    calc
      _ = 1+5*(R/s.bandwidth) := by ring
      _ ≤ 6 := by linarith
  calc
    _ = (1/s.bandwidth^2)*|∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capPairCoefficient u v (Z i ξ) (W i ξ))*
        capSoftFaceSecond s {f,g} (D i (ω,ξ)) (Y ω+d i (ω,ξ)) ∂κ
          ∂μ.prod (standardGaussian q)| := by
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ 1/s.bandwidth^2)]
    _ ≤ (1/s.bandwidth^2)*(7168*Real.exp (1+5*R/s.bandwidth)*Real.pi^3*b*K*Δ^2*
        Real.sqrt (1-(dotProduct u v)^2)) := mul_le_mul_of_nonneg_left ht.2 (by positivity)
    _ ≤ (1/s.bandwidth^2)*(7168*Real.exp 6*Real.pi^3*b*K*Δ^2*
        Real.sqrt (1-(dotProduct u v)^2)) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      gcongr
    _ = _ := by ring

end
end RectangleCLTArxivV1
