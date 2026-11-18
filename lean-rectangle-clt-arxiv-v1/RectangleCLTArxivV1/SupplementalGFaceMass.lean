import RectangleCLTArxivV1.CapWeightMass
import RectangleCLTArxivV1.SupplementalGScoreRestoration

/-! The G.2 masses for the actual signed-coordinate rectangle smoother,
including missing faces. The hypotheses contain only the raw independent
projected array and its actual mixed covariance. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open RectangleCLT.FaceSmoother
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem cap_original_single_le_capLaplace {p : ℕ}
    (s : FaceSmoother p) (f : Face p) (x : Vector p) :
    selectorTupleWeight s ![f] x ≤ capLaplace ((normalDot f x-s.offsets f)/s.bandwidth) := by
  classical
  by_cases hf : f ∈ s.faces
  · let D := 1+(s.weights x).T
    have hD1 : 1 ≤ D := by dsimp only [D]; linarith [(s.weights x).T_nonneg]
    have hDs : Real.exp ((normalDot f x-s.offsets f)/s.bandwidth) ≤ D := by
      have ht := (s.weights x).weight_le_T f
      rw [show (s.weights x).weight f = Real.exp ((normalDot f x-s.offsets f)/s.bandwidth) by
        simp only [FaceSmoother.weights,hf,if_pos,faceScore]] at ht
      dsimp only [D]
      linarith
    have he : selectorTupleWeight s ![f] x =
        Real.exp ((normalDot f x-s.offsets f)/s.bandwidth)/D^2 := by
      simp only [selectorTupleWeight,Fin.prod_univ_one,Matrix.cons_val_zero,
        FaceSmoother.F,FaceSmoother.pi,FaceWeights.F,FaceWeights.pi]
      change (1/D)*((s.weights x).weight f/D) = _
      simp only [FaceSmoother.weights,hf,if_pos,faceScore]
      field_simp
      ring
    rw [he]
    exact cap_logistic_single_le _ D hD1 hDs
  · have he : selectorTupleWeight s ![f] x = 0 := by
      simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf]
    rw [he]
    exact capLaplace_nonneg _

theorem cap_original_pair_le_capLaplace {p : ℕ}
    (s : FaceSmoother p) (f g : Face p) (x : Vector p) :
    selectorTupleWeight s ![f,g] x ≤
      capLaplace ((normalDot f x-s.offsets f)/s.bandwidth)*
      capLaplace ((normalDot g x-s.offsets g)/s.bandwidth) := by
  classical
  by_cases hf : f ∈ s.faces
  · by_cases hg : g ∈ s.faces
    · let D := 1+(s.weights x).T
      have hD1 : 1 ≤ D := by dsimp only [D]; linarith [(s.weights x).T_nonneg]
      have hD (a : Face p) (ha : a ∈ s.faces) :
          Real.exp ((normalDot a x-s.offsets a)/s.bandwidth) ≤ D := by
        have ht := (s.weights x).weight_le_T a
        rw [show (s.weights x).weight a = Real.exp ((normalDot a x-s.offsets a)/s.bandwidth) by
          simp only [FaceSmoother.weights,ha,if_pos,faceScore]] at ht
        dsimp only [D]
        linarith
      have he : selectorTupleWeight s ![f,g] x =
          Real.exp ((normalDot f x-s.offsets f)/s.bandwidth)*
          Real.exp ((normalDot g x-s.offsets g)/s.bandwidth)/D^3 := by
        simp only [selectorTupleWeight,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
          FaceSmoother.F,FaceSmoother.pi,FaceWeights.F,FaceWeights.pi]
        change (1/D)*(((s.weights x).weight f/D)*((s.weights x).weight g/D)) = _
        simp only [FaceSmoother.weights,hf,hg,if_pos,faceScore]
        field_simp
        ring
      rw [he]
      exact cap_logistic_pair_le _ _ D hD1 (hD f hf) (hD g hg)
    · have he : selectorTupleWeight s ![f,g] x = 0 := by
        simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hg]
      rw [he]
      exact mul_nonneg (capLaplace_nonneg _) (capLaplace_nonneg _)
  · have he : selectorTupleWeight s ![f,g] x = 0 := by
      simp [selectorTupleWeight,FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf]
    rw [he]
    exact mul_nonneg (capLaplace_nonneg _) (capLaplace_nonneg _)

/-- The actual one-face selector mass, with no local-mass premise. -/
theorem cap_original_single_face_mass
    {Ω : Type*} [MeasurableSpace Ω] {r n p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (A : Matrix (Fin 2) (Fin r) ℝ)
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X A 0 0)
    (s : FaceSmoother p) (hband : δ ≤ s.bandwidth) (f : Face p)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c : ℝ)
    (hproj : ∀ z, normalDot f (Y z) = capMixedValue X A z 0+c) :
    (∫ z, selectorTupleWeight s ![f] (Y z) ∂μ.prod (standardGaussian r)) ≤
      16*Real.exp (1/2)*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by
  have hh := s.bandwidth_pos
  have hfj : Measurable (fun z => normalDot f (Y z)) := by unfold normalDot; split <;> fun_prop
  have hsmall (t : ℝ) : (μ.prod (standardGaussian r)).real
      {z | |normalDot f (Y z)-t| ≤ s.bandwidth} ≤
        8*s.bandwidth*Real.sqrt (Real.pi/capGaussianExponent) := by
    have he : {z | |normalDot f (Y z)-t| ≤ s.bandwidth} =
        {z | |capMixedValue X A z 0-(t-c)| ≤ s.bandwidth} := by
      ext z
      simp only [Set.mem_setOf_eq,hproj]
      ring_nf
    rw [he]
    exact cap_one_projection_small_interval hdata A hvar s.bandwidth_pos hband (t-c)
  have hp := integral_capLaplace_le_of_intervals (μ.prod (standardGaussian r)) _ hfj
    (s.offsets f) s.bandwidth _ s.bandwidth_pos (by positivity) hsmall
  have hLi : Integrable (fun z => selectorTupleWeight s ![f] (Y z)) (μ.prod (standardGaussian r)) :=
    (integrable_const (1:ℝ)).mono'
      (measurable_selectorTupleWeight_comp s ![f] Y hY).aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _))
  have hQi : Integrable (fun z => capLaplace ((normalDot f (Y z)-s.offsets f)/s.bandwidth))
      (μ.prod (standardGaussian r)) :=
    (integrable_const (1:ℝ)).mono'
      (((hfj.sub_const _).div_const _).abs.div_const 2 |>.neg.exp).aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (capLaplace_nonneg _)]; exact capLaplace_le_one _))
  exact ((integral_mono hLi hQi (fun z => cap_original_single_le_capLaplace s f (Y z))).trans hp).trans_eq (by ring)

/-- The actual two-face selector mass, including its correlation-angle loss. -/
theorem cap_original_pair_face_mass
    {Ω : Type*} [MeasurableSpace Ω] {r n p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ) (A : Matrix (Fin 2) (Fin r) ℝ)
    {v ρ : ℝ} (hv : (1/2 : ℝ) ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (s : FaceSmoother p) (hband : 2*δ ≤ s.bandwidth) (f g : Face p)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c₀ c₁ : ℝ)
    (hproj₀ : ∀ z, normalDot f (Y z) = capMixedValue X A z 0+c₀)
    (hproj₁ : ∀ z, normalDot g (Y z) = capMixedValue X A z 1+c₁) :
    (∫ z, selectorTupleWeight s ![f,g] (Y z) ∂μ.prod (standardGaussian r)) ≤
      64*Real.exp 1*Real.pi^3*s.bandwidth^2/Real.sqrt (1-ρ^2) := by
  let F := fun z => (normalDot f (Y z),normalDot g (Y z))
  have hfj (a : Face p) : Measurable (fun z => normalDot a (Y z)) := by
    unfold normalDot; split <;> fun_prop
  have hFm : Measurable F := (hfj f).prodMk (hfj g)
  have hsmall (a b : ℝ) : (μ.prod (standardGaussian r)).real
      {z | |(F z).1-a| ≤ s.bandwidth ∧ |(F z).2-b| ≤ s.bandwidth} ≤
        16*Real.pi^3*s.bandwidth^2/Real.sqrt (1-ρ^2) := by
    have he : {z | |(F z).1-a| ≤ s.bandwidth ∧ |(F z).2-b| ≤ s.bandwidth} =
        {z | |capMixedValue X A z 0-(a-c₀)| ≤ s.bandwidth ∧
          |capMixedValue X A z 1-(b-c₁)| ≤ s.bandwidth} := by
      ext z
      simp only [Set.mem_setOf_eq]
      dsimp only [F]
      rw [hproj₀,hproj₁]
      ring_nf
    rw [he]
    exact cap_two_projection_small_box hdata A hv hρ hcov s.bandwidth_pos hband (a-c₀) (b-c₁)
  have hp := integral_capPairLaplace_le_of_boxes (μ.prod (standardGaussian r)) F hFm
    (s.offsets f) (s.offsets g) s.bandwidth _ s.bandwidth_pos (by positivity) hsmall
  have hLi : Integrable (fun z => selectorTupleWeight s ![f,g] (Y z)) (μ.prod (standardGaussian r)) :=
    (integrable_const (1:ℝ)).mono'
      (measurable_selectorTupleWeight_comp s ![f,g] Y hY).aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs,abs_of_nonneg (selectorTupleWeight_nonneg s _ _)]; exact selectorTupleWeight_le_one s _ _))
  have hQm : Measurable (fun z => capPairLaplace (((F z).1-s.offsets f)/s.bandwidth,
      ((F z).2-s.offsets g)/s.bandwidth)) := by
    unfold capPairLaplace capLaplace F normalDot; split <;> split <;> fun_prop
  have hQi : Integrable (fun z => capPairLaplace (((F z).1-s.offsets f)/s.bandwidth,
      ((F z).2-s.offsets g)/s.bandwidth)) (μ.prod (standardGaussian r)) :=
    (integrable_const (1:ℝ)).mono' hQm.aestronglyMeasurable
      (ae_of_all _ (fun z => by
        unfold capPairLaplace
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (capLaplace_nonneg _) (capLaplace_nonneg _))]
        exact (mul_le_mul (capLaplace_le_one _) (capLaplace_le_one _) (capLaplace_nonneg _) zero_le_one).trans_eq (one_mul _)))
  have ht := integral_mono hLi hQi (fun z => cap_original_pair_le_capLaplace s f g (Y z))
  exact (ht.trans hp).trans_eq (by ring)

end
end RectangleCLTArxivV1
