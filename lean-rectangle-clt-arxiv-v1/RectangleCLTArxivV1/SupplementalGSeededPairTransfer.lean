import RectangleCLTArxivV1.SupplementalGSeededContributions

/-! Exact H2 transfer and collapse of the two genuine Gaussian halves in
an actual seeded pair contribution. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem cap_secondHermite_pair_halves_transfer {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (x : Vector p) (Z : Vector r)
    (f g : Face p) (hfg : f ≠ g) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    (∫ g₁, ∫ g₀, repeatedDirectionScore g₁ Z*
      selectorTupleWeight s ![f,g] ((seededSplitGaussianScale ε t • A).mulVec g₁+
        (seededSplitGaussianScale ε t • A).mulVec g₀+x) ∂standardGaussian r ∂standardGaussian r) =
      (seededSplitGaussianScale ε t)^2*(∫ z,
        capSoftFaceSecond s {f,g} (A.mulVec Z) ((Real.sqrt (t+ε) • A).mulVec z+x) ∂standardGaussian r) := by
  let M := seededSplitGaussianScale ε t • A
  have hm : Measurable (fun z : Vector r × Vector r => selectorTupleWeight s ![f,g] (M.mulVec z.1+M.mulVec z.2+x)) :=
    measurable_selectorTupleWeight_comp s _ _
      ((((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst).add
        ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)).add_const x)
  have hi : Integrable (fun z : Vector r × Vector r => repeatedDirectionScore z.1 Z*
      selectorTupleWeight s ![f,g] (M.mulVec z.1+M.mulVec z.2+x)) ((standardGaussian r).prod (standardGaussian r)) := by
    have hs := (integrable_fixed_gaussian_repeated_score Z).mul_prod (integrable_const (1:ℝ) (μ := standardGaussian r))
    have hsi : Integrable (fun z : Vector r × Vector r => repeatedDirectionScore z.1 Z) ((standardGaussian r).prod (standardGaussian r)) := by simpa only [mul_one] using hs
    simpa only [mul_comm] using hsi.bdd_mul' hm.aestronglyMeasurable
      (ae_of_all _ (fun z => by
        rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]
        exact selectorTupleWeight_le_one s _ _))
  have hcard : ({f,g} : Finset (Face p)).card ≤ 2 := by
    classical
    simp [hfg]
  let F := fun y => capSoftFaceSecond s {f,g} (A.mulVec Z) (y+x)
  have hFm : Measurable F := measurable_capSoftFaceSecond_comp s _ (fun _ => A.mulVec Z)
    (fun y => y+x) measurable_const (measurable_id.add_const x)
  have hFb : ∃ C : ℝ, ∀ y, |F y| ≤ C := by
    refine ⟨28*‖A.mulVec Z‖^2/s.bandwidth^2,fun y => ?_⟩
    exact (capSoftFaceSecond_abs_le s {f,g} hcard (y+x) (A.mulVec Z) (norm_nonneg _) le_rfl).trans
      (by
        have hh := mul_le_mul_of_nonneg_left (s.softFaceWeight_le_one {f,g} (y+x))
          (by positivity : 0 ≤ 28*‖A.mulVec Z‖^2/s.bandwidth^2)
        simpa only [mul_one] using hh)
  have hcollapse := cap_gaussian_halves_integral_rectangular A hε ht F hFm hFb
  calc
    _ = ∫ g₀, ∫ g₁, repeatedDirectionScore g₁ Z*selectorTupleWeight s ![f,g]
        (M.mulVec g₁+M.mulVec g₀+x) ∂standardGaussian r ∂standardGaussian r := integral_integral_swap hi
    _ = ∫ g₀, (seededSplitGaussianScale ε t)^2*(∫ g₁,
        capSoftFaceSecond s {f,g} (A.mulVec Z) (M.mulVec g₁+M.mulVec g₀+x) ∂standardGaussian r)
          ∂standardGaussian r := by
      apply integral_congr_ae
      exact ae_of_all _ (fun g₀ => by
        simpa only [add_assoc] using cap_secondHermite_pair_transfer_scaled s A (M.mulVec g₀+x) Z f g hfg (seededSplitGaussianScale ε t))
    _ = (seededSplitGaussianScale ε t)^2*(∫ g₀, ∫ g₁,
        F (M.mulVec g₀+M.mulVec g₁) ∂standardGaussian r ∂standardGaussian r) := by
      rw [← integral_const_mul]
      apply integral_congr_ae
      exact ae_of_all _ (fun g₀ => by
        apply congrArg (fun a : ℝ => (seededSplitGaussianScale ε t)^2*a)
        apply integral_congr_ae
        exact ae_of_all _ (fun g₁ => by
          dsimp only [F]
          apply congrArg (capSoftFaceSecond s {f,g} (A.mulVec Z))
          abel))
    _ = _ := congrArg (fun a => (seededSplitGaussianScale ε t)^2*a) hcollapse

/-- Actual moment-dominated Fubini and Gaussian-half collapse with random
copies. The physical test point may be any measurable copy-dependent shift. -/
theorem cap_random_pair_halves_transfer
    {Ω : Type*} [MeasurableSpace Ω] {p r : ℕ} (ν : Measure Ω) [IsProbabilityMeasure ν]
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ)
    (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) ν)
    (c : Ω → ℝ) (hc : Measurable c) (X : Ω → Vector p) (hX : Measurable X)
    {b Δ : ℝ} (hb : 0 ≤ b) (hΔ : 0 ≤ Δ)
    (hcb : ∀ᵐ ω ∂ν, |c ω| ≤ b) (hDb : ∀ᵐ ω ∂ν, ‖A.mulVec (Z ω)‖ ≤ Δ)
    (f g : Face p) (hfg : f ≠ g) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    Integrable (fun z : Ω × Vector r => c z.1*
      capSoftFaceSecond s {f,g} (A.mulVec (Z z.1)) ((Real.sqrt (t+ε) • A).mulVec z.2+X z.1))
        (ν.prod (standardGaussian r)) ∧
    Integrable (fun g₁ => ∫ ω, ∫ g₀, c ω*(repeatedDirectionScore g₁ (Z ω)*
      selectorTupleWeight s ![f,g] ((seededSplitGaussianScale ε t • A).mulVec g₁+
        (seededSplitGaussianScale ε t • A).mulVec g₀+X ω)) ∂standardGaussian r ∂ν) (standardGaussian r) ∧
    (∫ g₁, ∫ ω, ∫ g₀, c ω*(repeatedDirectionScore g₁ (Z ω)*
      selectorTupleWeight s ![f,g] ((seededSplitGaussianScale ε t • A).mulVec g₁+
        (seededSplitGaussianScale ε t • A).mulVec g₀+X ω))
          ∂standardGaussian r ∂ν ∂standardGaussian r) =
      (seededSplitGaussianScale ε t)^2*(∫ ω, ∫ z, c ω*
        capSoftFaceSecond s {f,g} (A.mulVec (Z ω)) ((Real.sqrt (t+ε) • A).mulVec z+X ω)
          ∂standardGaussian r ∂ν) := by
  let G := standardGaussian r
  let M := seededSplitGaussianScale ε t • A
  let w := fun z : Ω × (Vector r × Vector r) => selectorTupleWeight s ![f,g]
    (M.mulVec z.2.1+M.mulVec z.2.2+X z.1)
  let K := fun z : Ω × (Vector r × Vector r) => repeatedDirectionScore z.2.1 (Z z.1)
  let F := fun z : Ω × (Vector r × Vector r) => c z.1*(K z*w z)
  have hwm : Measurable w := measurable_selectorTupleWeight_comp s _ _
    ((((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd.fst).add
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd.snd)).add (hX.comp measurable_fst))
  have hKm : Measurable K := by unfold K repeatedDirectionScore faceDot vectorNormSq; fun_prop
  have hKi : Integrable K (ν.prod (G.prod G)) := by
    apply ((measurePreserving_prodAssoc ν G G).integrable_comp hKm.aestronglyMeasurable).mp
    change Integrable (fun z : (Ω × Vector r) × Vector r => repeatedDirectionScore z.1.2 (Z z.1.1)) ((ν.prod G).prod G)
    simpa only [mul_one] using (integrable_random_repeatedDirectionScore ν Z hZ).mul_prod
      (integrable_const (1:ℝ) (μ := G))
  have hFm : Measurable F := (hc.comp measurable_fst).mul (hKm.mul hwm)
  have hFi : Integrable F (ν.prod (G.prod G)) :=
    cap_integrable_bounded_coefficient_score ν (G.prod G) K w hKi hwm
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _) c hc hcb
  have hFs : Integrable (fun z : (Ω × Vector r) × Vector r => F (z.1.1,(z.1.2,z.2))) ((ν.prod G).prod G) :=
    ((measurePreserving_prodAssoc ν G G).integrable_comp hFm.aestronglyMeasurable).mpr hFi
  have hMarg : Integrable (fun z : Ω × Vector r => ∫ g₀, F (z.1,(z.2,g₀)) ∂G) (ν.prod G) := hFs.integral_prod_left
  have hswap := integral_integral_swap (f := fun ω g₁ => ∫ g₀, F (ω,(g₁,g₀)) ∂G) hMarg
  have hcard : ({f,g} : Finset (Face p)).card ≤ 2 := by
    classical
    simp [hfg]
  have hDm : Measurable (fun z : Ω × Vector r => c z.1*
      capSoftFaceSecond s {f,g} (A.mulVec (Z z.1)) ((Real.sqrt (t+ε) • A).mulVec z.2+X z.1)) :=
    (hc.comp measurable_fst).mul (measurable_capSoftFaceSecond_comp s _ _ _
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp (hZm.comp measurable_fst))
      (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add (hX.comp measurable_fst)))
  have hDi : Integrable (fun z : Ω × Vector r => c z.1*
      capSoftFaceSecond s {f,g} (A.mulVec (Z z.1)) ((Real.sqrt (t+ε) • A).mulVec z.2+X z.1)) (ν.prod G) := by
    apply (integrable_const (b*(28*Δ^2/s.bandwidth^2))).mono' hDm.aestronglyMeasurable
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae hcb,Measure.quasiMeasurePreserving_fst.ae hDb] with z hcz hDz
    rw [Real.norm_eq_abs,abs_mul]
    have hd := capSoftFaceSecond_abs_le s {f,g} hcard ((Real.sqrt (t+ε) • A).mulVec z.2+X z.1) (A.mulVec (Z z.1)) hΔ hDz
    have hd' : |capSoftFaceSecond s {f,g} (A.mulVec (Z z.1)) ((Real.sqrt (t+ε) • A).mulVec z.2+X z.1)| ≤ 28*Δ^2/s.bandwidth^2 :=
      hd.trans (by simpa only [mul_one] using mul_le_mul_of_nonneg_left (s.softFaceWeight_le_one _ _) (by positivity : 0 ≤ 28*Δ^2/s.bandwidth^2))
    exact mul_le_mul hcz hd' (abs_nonneg _) hb
  refine ⟨hDi, hMarg.integral_prod_right, ?_⟩
  calc
    _ = ∫ ω, ∫ g₁, ∫ g₀, F (ω,(g₁,g₀)) ∂G ∂G ∂ν := hswap.symm
    _ = ∫ ω, (seededSplitGaussianScale ε t)^2*(∫ z, c ω*
        capSoftFaceSecond s {f,g} (A.mulVec (Z ω)) ((Real.sqrt (t+ε) • A).mulVec z+X ω) ∂G) ∂ν := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        dsimp only [F,K,w,M,G]
        simp_rw [integral_const_mul]
        have hp := cap_secondHermite_pair_halves_transfer s A (X ω) (Z ω) f g hfg hε ht
        simp_rw [integral_const_mul] at hp
        rw [hp]
        ring)
    _ = _ := integral_const_mul _ _

/-- Swap a Gaussian middle factor with the independent copy factor while
retaining the finite observation sum. Integrability is transported by the
actual measure-preserving product permutation. -/
theorem cap_array_middle_swap
    {Ω Ξ Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] [MeasurableSpace Γ] {N : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (κ : Measure Ξ) [IsProbabilityMeasure κ]
    (G : Measure Γ) [IsProbabilityMeasure G]
    (F : Fin N → (Ω × Ξ) × Γ → ℝ) (hF : ∀ i, Integrable (F i) ((μ.prod κ).prod G)) :
    (∫ z, ∑ i, ∫ ξ, F i ((z.1,ξ),z.2) ∂κ ∂μ.prod G) =
      ∑ i, ∫ ω, ∫ g, F i (ω,g) ∂G ∂μ.prod κ := by
  let e : ((Ω × Γ) × Ξ) ≃ᵐ ((Ω × Ξ) × Γ) :=
    MeasurableEquiv.prodAssoc.trans
      (((MeasurableEquiv.refl Ω).prodCongr (MeasurableEquiv.prodComm : Γ × Ξ ≃ᵐ Ξ × Γ)).trans MeasurableEquiv.prodAssoc.symm)
  have hp : MeasurePreserving e ((μ.prod G).prod κ) ((μ.prod κ).prod G) :=
    (MeasurePreserving.symm MeasurableEquiv.prodAssoc (measurePreserving_prodAssoc μ κ G)).comp
      (((MeasurePreserving.id μ).prod (Measure.measurePreserving_swap (μ := G) (ν := κ))).comp
        (measurePreserving_prodAssoc μ G κ))
  have hi (i : Fin N) : Integrable (fun z => F i (e z)) ((μ.prod G).prod κ) :=
    (hp.integrable_comp (hF i).aestronglyMeasurable).mpr (hF i)
  calc
    _ = ∫ z, ∑ i, F i (e z) ∂(μ.prod G).prod κ :=
      (cap_product_array_marginal (μ.prod G) κ (fun i z => F i (e z)) hi).symm
    _ = ∫ z, ∑ i, F i z ∂(μ.prod κ).prod G := hp.integral_comp e.measurableEmbedding (fun z => ∑ i, F i z)
    _ = _ := by
      rw [integral_finset_sum _ (fun i _ => hF i)]
      exact Finset.sum_congr rfl (fun i _ => integral_prod _ (hF i))

theorem cap_fixed_gaussian_score_copy_integrable
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (ν : Measure Ω) (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) ν) (g : Vector r) :
    Integrable (fun ω => repeatedDirectionScore g (Z ω)) ν := by
  simp_rw [repeatedDirectionScore_eq_quadratic,matrixQuadratic]
  apply integrable_finset_sum
  intro j _
  apply integrable_finset_sum
  intro k _
  convert (hZ j k).const_mul ((rankOne g-1) j k) using 1
  funext ω
  ring

/-- The named actual seeded pair contribution equals its whole-point
second directional derivative, with the inverse Gaussian variance canceled.
All Gaussian/copy exchanges use actual integrable moment majorants. -/
theorem cap_seeded_pair_contribution_eq_second
    {Ω : Type*} [MeasurableSpace Ω] {p r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (A : Matrix (Fin p) (Fin r) ℝ)
    (hA : A*A.transpose = covariance μ (sumVector ξ))
    (hunit : ∀ j, covariance μ (sumVector ξ) j j = 1)
    (s : FaceSmoother p) (x : Vector p) (f g : Face p) (hfg : f ≠ g)
    {ε t θ : ℝ} (hε : 0 ≤ ε) (ht : t ∈ Set.Icc (0:ℝ) 1) (hpos : 0 < t+ε)
    (freshY freshW freshShift : Bool) :
    capSeededPairContribution s μ ξ A x ε t θ f g freshY freshW freshShift =
      (1/s.bandwidth^2)*(∫ ω, ∑ i, ∫ a,
        capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a) (capOriginalCopy ξ freshW i a)*
          capSoftFaceSecond s {f,g} (capOriginalCopy ξ false i a)
            (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂μ.prod μ
              ∂(bernoulliArrayLaw μ ξ t).prod (standardGaussian r)) := by
  let B := bernoulliArrayLaw μ ξ t
  let κ := μ.prod μ
  let G := standardGaussian r
  let ν := B.prod κ
  letI := bernoulliArrayLaw_isProbability μ ξ h.measurable t ht.1 ht.2
  let σ := seededSplitGaussianScale ε t
  let M := σ • A
  let Z := fun i (z : (Fin n → Vector p) × (Ω × Ω)) => capWhitenedCopy A ξ i z.2
  let C := fun i (z : (Fin n → Vector p) × (Ω × Ω)) =>
    capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i z.2) (capOriginalCopy ξ freshW i z.2)
  let X := fun i (z : (Fin n → Vector p) × (Ω × Ω)) =>
    x+arraySum z.1+(θ*(1+t)) • capOriginalCopy ξ freshShift i z.2-z.1 i
  let Q := fun g₁ i (z : ((Fin n → Vector p) × (Ω × Ω)) × Vector r) =>
    C i z.1*(repeatedDirectionScore g₁ (Z i z.1)*selectorTupleWeight s ![f,g] (M.mulVec g₁+M.mulVec z.2+X i z.1))
  let D := fun i (z : ((Fin n → Vector p) × (Ω × Ω)) × Vector r) =>
    C i z.1*capSoftFaceSecond s {f,g} (A.mulVec (Z i z.1)) ((Real.sqrt (t+ε) • A).mulVec z.2+X i z.1)
  have hdiag : ∀ j, (A*A.transpose) j j=1 := by intro j; rw [hA]; exact hunit j
  have hσ : σ ≠ 0 := (seededSplitGaussianScale_pos hpos).ne'
  have hZm (i : Fin n) : Measurable (Z i) := (capWhitenedCopy_measurable h A i).comp measurable_snd
  have hZ (i : Fin n) (j k : Fin r) : Integrable (fun z => Z i z j*Z i z k) ν := by
    simpa only [one_mul] using (integrable_const (1:ℝ) (μ := B)).mul_prod (capWhitenedCopy_integrable_coordinate_pair h A i j k)
  have hCm (i : Fin n) : Measurable (C i) := by
    have hYm : Measurable (fun z : (Fin n → Vector p) × (Ω × Ω) => capOriginalCopy ξ freshY i z.2) :=
      (capOriginalCopy_measurable ξ h.measurable freshY i).comp measurable_snd
    have hWm : Measurable (fun z : (Fin n → Vector p) × (Ω × Ω) => capOriginalCopy ξ freshW i z.2) :=
      (capOriginalCopy_measurable ξ h.measurable freshW i).comp measurable_snd
    unfold C capRectangularPairCoefficient normalDot
    split <;> split <;> fun_prop
  have hXm (i : Fin n) : Measurable (X i) := by
    unfold X
    exact ((measurable_const.add ((measurable_arraySum p n).comp measurable_fst)).add
      (measurable_const.smul ((capOriginalCopy_measurable ξ h.measurable freshShift i).comp measurable_snd))).sub
        ((measurable_pi_apply i).comp measurable_fst)
  have hCb (i : Fin n) : ∀ᵐ z ∂ν, |C i z| ≤ 4*δ^2 := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshY i),
      Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h freshW i)] with z hy hw
    exact cap_original_pair_coefficient_abs_le A hdiag f g _ _ h.delta_nonneg hy hw
  have hDb (i : Fin n) : ∀ᵐ z ∂ν, ‖A.mulVec (Z i z)‖ ≤ δ := by
    filter_upwards [Measure.quasiMeasurePreserving_snd.ae (capWhitenedCopy_reconstruct h A hA i),
      Measure.quasiMeasurePreserving_snd.ae (capOriginalCopy_bounded h false i)] with z he hz
    rw [he]
    exact hz
  have hT (i : Fin n) := cap_random_pair_halves_transfer ν s A (Z i) (hZm i) (hZ i)
    (C i) (hCm i) (X i) (hXm i) (by positivity : 0 ≤ 4*δ^2) h.delta_nonneg (hCb i) (hDb i) f g hfg hε ht.1
  have hQi (g₁ : Vector r) (i : Fin n) : Integrable (Q g₁ i) (ν.prod G) := by
    have hscore : Integrable (fun z : ((Fin n → Vector p) × (Ω × Ω)) × Vector r => repeatedDirectionScore g₁ (Z i z.1)) (ν.prod G) := by
      simpa only [mul_one] using (cap_fixed_gaussian_score_copy_integrable ν (Z i) (hZ i) g₁).mul_prod
        (integrable_const (1:ℝ) (μ := G))
    have hwm : Measurable (fun z : ((Fin n → Vector p) × (Ω × Ω)) × Vector r =>
      selectorTupleWeight s ![f,g] (M.mulVec g₁+M.mulVec z.2+X i z.1)) :=
      measurable_selectorTupleWeight_comp s _ _
        ((measurable_const.add ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)).add
          ((hXm i).comp measurable_fst))
    exact cap_integrable_bounded_coefficient_score ν G _ _ hscore hwm
      (fun z => by rw [abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _)
      (C i) (hCm i) (hCb i)
  have hHalfPoint (ω : (Fin n → Vector p) × Vector r) (a : Ω × Ω) (g₁ : Vector r) (i : Fin n) :
      M.mulVec g₁+capSeededBaseValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a) =
        M.mulVec g₁+M.mulVec ω.2+X i (ω.1,a) := by
    dsimp only [capSeededBaseValue,capSeededCopyShift,X,M,σ]
    abel
  have hWholePoint (ω : (Fin n → Vector p) × Vector r) (a : Ω × Ω) (i : Fin n) :
      capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a) =
        (Real.sqrt (t+ε) • A).mulVec ω.2+X i (ω.1,a) := by
    dsimp only [capSeededWholeValue,capSeededCopyShift,X]
    abel
  let L := fun g₁ : Vector r => (∫ ω, ∑ i, ∫ a,
        (capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a) (capOriginalCopy ξ freshW i a)*
          repeatedDirectionScore g₁ (capWhitenedCopy A ξ i a))*
        selectorTupleWeight s ![f,g] (M.mulVec g₁+capSeededBaseValue A x ε t ω+
          capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂κ ∂B.prod G)
  have hInner (g₁ : Vector r) : L g₁ =
      ∑ i, ∫ z, ∫ g₀, Q g₁ i (z,g₀) ∂G ∂ν := by
    dsimp only [L]
    simp_rw [hHalfPoint,mul_assoc]
    exact cap_array_middle_swap B κ G (Q g₁) (hQi g₁)
  let T := (∫ ω, ∑ i, ∫ a,
        capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a) (capOriginalCopy ξ freshW i a)*
          capSoftFaceSecond s {f,g} (capOriginalCopy ξ false i a)
            (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂κ ∂B.prod G)
  have hOuter : T =
      ∑ i, ∫ z, ∫ g₀, D i (z,g₀) ∂G ∂ν := by
    have he : (∫ ω, ∑ i, ∫ a,
        capRectangularPairCoefficient A f g (capOriginalCopy ξ freshY i a) (capOriginalCopy ξ freshW i a)*
          capSoftFaceSecond s {f,g} (capOriginalCopy ξ false i a)
            (capSeededWholeValue A x ε t ω+capSeededCopyShift ξ freshShift t θ i (ω,a)) ∂κ ∂B.prod G) =
        ∫ ω, ∑ i, ∫ a, D i ((ω.1,a),ω.2) ∂κ ∂B.prod G := by
      apply integral_congr_ae
      exact ae_of_all _ (fun ω => by
        apply Finset.sum_congr rfl
        intro i _
        apply integral_congr_ae
        filter_upwards [capWhitenedCopy_reconstruct h A hA i] with a ha
        dsimp only [D,C,Z]
        rw [ha,hWholePoint])
    dsimp only [T]
    rw [he]
    exact cap_array_middle_swap B κ G D (fun i => (hT i).1)
  unfold capSeededPairContribution
  change (1/(s.bandwidth^2*σ^2))*(∫ g₁, L g₁ ∂G) = (1/s.bandwidth^2)*T
  simp_rw [hInner]
  rw [integral_finset_sum Finset.univ
    (f := fun i g₁ => ∫ z, ∫ g₀, Q g₁ i (z,g₀) ∂G ∂ν) (fun i _ => (hT i).2.1)]
  have hTeq (i : Fin n) : (∫ g₁, ∫ z, ∫ g₀, Q g₁ i (z,g₀) ∂G ∂ν ∂G) =
      σ^2*(∫ z, ∫ g₀, D i (z,g₀) ∂G ∂ν) := (hT i).2.2
  change (1/(s.bandwidth^2*σ^2))*(∑ i, ∫ g₁, ∫ z, ∫ g₀, Q g₁ i (z,g₀) ∂G ∂ν ∂G) = (1/s.bandwidth^2)*T
  simp_rw [hTeq]
  rw [← Finset.mul_sum,← hOuter]
  field_simp [hσ,s.bandwidth_pos.ne']
  <;> ring

end
end RectangleCLTArxivV1
