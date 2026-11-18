import RectangleCLTArxivV1.IntrinsicGaussianBoundary

/-! The probabilistic localization step of Supplemental H.
An actual independent Gaussian tube with random radius is integrated
against the concentrated base. The geometric comparison of Hausdorff
surface integrals to this tube is a separate obligation. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT
open scoped BigOperators
noncomputable section

theorem faceLayer_translate {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (b : Vector r) (s : ℝ) :
    {x | x+b ∈ faceLayer U a s} =
      faceLayer U (fun j => a j-dotProduct (U j) b) s := by
  ext x
  have he (d : ℝ) : (∀ j, dotProduct (U j) (x+b) ≤ a j+d) ↔
      ∀ j, dotProduct (U j) x ≤ (a j-dotProduct (U j) b)+d := by
    simp only [dotProduct_add]
    constructor <;> intro h j <;> linarith [h j]
  change ((∀ j, dotProduct (U j) (x+b) ≤ a j+s) ∧
      ¬∀ j, dotProduct (U j) (x+b) ≤ a j+-s) ↔
    ((∀ j, dotProduct (U j) x ≤ (a j-dotProduct (U j) b)+s) ∧
      ¬∀ j, dotProduct (U j) x ≤ (a j-dotProduct (U j) b)+-s)
  rw [he s,he (-s)]

/-- A common threshold radius may depend on the Gaussian realization. -/
def gaussianVariableTube {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (σ : ℝ)
    (R : Vector r → ℝ) : Set (Vector r × Vector r) :=
  {z | z.1+σ • z.2 ∈ faceLayer U a (σ/R z.2)}

theorem measurableSet_gaussianVariableTube {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (σ : ℝ)
    (R : Vector r → ℝ) (hR : Measurable R) :
    MeasurableSet (gaussianVariableTube U a σ R) := by
  have hX : Measurable (fun z : Vector r × Vector r => z.1+σ • z.2) :=
    measurable_fst.add (measurable_const.smul measurable_snd)
  have hproj (j : Fin m) : Measurable (fun z : Vector r × Vector r =>
      dotProduct (U j) (z.1+σ • z.2)) :=
    (measurable_pi_apply j).comp ((measurable_faceProjection U).comp hX)
  have hradius : Measurable (fun z : Vector r × Vector r => σ/R z.2) :=
    measurable_const.div (hR.comp measurable_snd)
  change MeasurableSet
    ({z : Vector r × Vector r | ∀ j, dotProduct (U j) (z.1+σ • z.2) ≤ a j+σ/R z.2} \
      {z : Vector r × Vector r | ∀ j, dotProduct (U j) (z.1+σ • z.2) ≤ a j+-(σ/R z.2)})
  apply MeasurableSet.diff
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hproj j) (measurable_const.add hradius))
  · rw [Set.setOf_forall]
    exact MeasurableSet.iInter (fun j => measurableSet_le (hproj j) (measurable_const.add hradius.neg))

/-- The exact weighted tube estimate underlying H's localization. The
only probability bound among the premises is H's displayed hypothesis
on the concentrated base; the Gaussian tube estimate is proved by Fubini.
All moments on the right are actual standard Gaussian integrals. -/
theorem concentrated_base_gaussian_weighted_tube {r m : ℕ}
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m)
    {K δ σ : ℝ} (hσ : 0 < σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer U b s) ≤ K*(s+δ))
    (R : Vector r → ℝ) (hR : Measurable R) (hRpos : ∀ g, 0 < R g)
    (hR3 : Integrable (fun g => (R g)^3) (standardGaussian r))
    (hR4 : Integrable (fun g => (R g)^4) (standardGaussian r)) :
    (∫ z, (gaussianVariableTube U a σ R).indicator (fun z => (R z.2)^4) z
      ∂ν.prod (standardGaussian r)) ≤
      K*(σ*(∫ g, (R g)^3 ∂standardGaussian r)+
        δ*(∫ g, (R g)^4 ∂standardGaussian r)) := by
  let S := gaussianVariableTube U a σ R
  let I : Vector r × Vector r → ℝ := S.indicator (fun z => (R z.2)^4)
  have hS := measurableSet_gaussianVariableTube U a σ R hR
  have hI : Measurable I :=
    ((hR.comp measurable_snd).pow_const 4).indicator hS
  have hprod : Integrable (fun z : Vector r × Vector r => (R z.2)^4)
      (ν.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod hR4
  have hiI : Integrable I (ν.prod (standardGaussian r)) := by
    apply hprod.mono' hI.aestronglyMeasurable
    exact ae_of_all _ (fun z => by
      by_cases hz : z ∈ S
      · simp only [I,Set.indicator_of_mem hz,Real.norm_eq_abs,
          abs_of_nonneg (pow_nonneg (hRpos z.2).le 4),le_refl]
      · simp only [I,Set.indicator_of_not_mem hz,norm_zero]
        exact pow_nonneg (hRpos z.2).le 4)
  have hfixed (g : Vector r) : (∫ x, I (x,g) ∂ν) =
      (R g)^4*ν.real {x | x+σ • g ∈ faceLayer U a (σ/R g)} := by
    have hE : MeasurableSet {x | x+σ • g ∈ faceLayer U a (σ/R g)} :=
      (measurableSet_faceLayer U a (σ/R g)).preimage (measurable_id.add_const _)
    change (∫ x, {x | x+σ • g ∈ faceLayer U a (σ/R g)}.indicator
      (fun _ => (R g)^4) x ∂ν) = _
    rw [integral_indicator hE,setIntegral_const,smul_eq_mul,mul_comm]
  have hsection (g : Vector r) : (∫ x, I (x,g) ∂ν) ≤
      K*(σ*(R g)^3+δ*(R g)^4) := by
    rw [hfixed,faceLayer_translate]
    have hh := hbase (fun j => a j-dotProduct (U j) (σ • g)) (σ/R g)
      (div_pos hσ (hRpos g))
    apply (mul_le_mul_of_nonneg_left hh (pow_nonneg (hRpos g).le 4)).trans_eq
    field_simp [(hRpos g).ne']
    ring
  have hiBound : Integrable (fun g => K*(σ*(R g)^3+δ*(R g)^4)) (standardGaussian r) :=
    ((hR3.const_mul σ).add (hR4.const_mul δ)).const_mul K
  change (∫ z, I z ∂ν.prod (standardGaussian r)) ≤ _
  rw [integral_prod_symm I hiI]
  apply (integral_mono hiI.integral_prod_right hiBound hsection).trans_eq
  rw [integral_const_mul,integral_add (hR3.const_mul σ) (hR4.const_mul δ),
    integral_const_mul,integral_const_mul]

/-- The one-sided outward tube appearing in the surface localization. -/
def gaussianOutwardVariableTube {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) (σ : ℝ)
    (R : Vector r → ℝ) : Set (Vector r × Vector r) :=
  {z | z.1+σ • z.2 ∈ facePolyhedron U a (σ/R z.2)} \
    {z | z.1+σ • z.2 ∈ facePolyhedron U a 0}

theorem gaussianOutwardVariableTube_eq {r m : ℕ}
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m) {σ : ℝ} (hσ : 0 ≤ σ)
    (R : Vector r → ℝ) (hRpos : ∀ g, 0 < R g) :
    gaussianOutwardVariableTube U a σ R = gaussianVariableTube U a σ R \
      {z | z.1+σ • z.2 ∈ facePolyhedron U a 0} := by
  ext z
  have hs : 0 ≤ σ/R z.2 := div_nonneg hσ (hRpos z.2).le
  have hinner : z.1+σ • z.2 ∈ facePolyhedron U a (-(σ/R z.2)) →
      z.1+σ • z.2 ∈ facePolyhedron U a 0 := by
    intro hx j
    have hh := hx j
    change dotProduct (U j) (z.1+σ • z.2) ≤ a j+0
    linarith
  change ((z.1+σ • z.2 ∈ facePolyhedron U a (σ/R z.2)) ∧
      ¬z.1+σ • z.2 ∈ facePolyhedron U a 0) ↔
    (((z.1+σ • z.2 ∈ facePolyhedron U a (σ/R z.2)) ∧
      ¬z.1+σ • z.2 ∈ facePolyhedron U a (-(σ/R z.2))) ∧
      ¬z.1+σ • z.2 ∈ facePolyhedron U a 0)
  tauto

/-- The actual outward Gaussian tube has the same weighted bound as its
two-sided enlargement; this is the tube used on H's localized right side. -/
theorem concentrated_base_gaussian_weighted_outward_tube {r m : ℕ}
    (ν : Measure (Vector r)) [IsProbabilityMeasure ν]
    (U : Matrix (Fin m) (Fin r) ℝ) (a : Vector m)
    {K δ σ : ℝ} (hσ : 0 < σ)
    (hbase : ∀ (b : Vector m) (s : ℝ), 0 < s → ν.real (faceLayer U b s) ≤ K*(s+δ))
    (R : Vector r → ℝ) (hR : Measurable R) (hRpos : ∀ g, 0 < R g)
    (hR3 : Integrable (fun g => (R g)^3) (standardGaussian r))
    (hR4 : Integrable (fun g => (R g)^4) (standardGaussian r)) :
    (∫ z, (gaussianOutwardVariableTube U a σ R).indicator (fun z => (R z.2)^4) z
      ∂ν.prod (standardGaussian r)) ≤
      K*(σ*(∫ g, (R g)^3 ∂standardGaussian r)+
        δ*(∫ g, (R g)^4 ∂standardGaussian r)) := by
  have he := gaussianOutwardVariableTube_eq U a hσ.le R hRpos
  have hS := measurableSet_gaussianVariableTube U a σ R hR
  have hzero : MeasurableSet {z : Vector r × Vector r |
      z.1+σ • z.2 ∈ facePolyhedron U a 0} := by
    change MeasurableSet {z : Vector r × Vector r |
      ∀ j, dotProduct (U j) (z.1+σ • z.2) ≤ a j+0}
    rw [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro j
    exact measurableSet_le
      ((measurable_pi_apply j).comp ((measurable_faceProjection U).comp
        (measurable_fst.add (measurable_const.smul measurable_snd)))) measurable_const
  have hOut : MeasurableSet (gaussianOutwardVariableTube U a σ R) := by
    rw [he]
    exact hS.diff hzero
  have hi : Integrable (fun z : Vector r × Vector r => (R z.2)^4)
      (ν.prod (standardGaussian r)) := by
    simpa only [one_mul] using (integrable_const (μ := ν) (1:ℝ)).mul_prod hR4
  apply (integral_mono (hi.indicator hOut) (hi.indicator hS) ?_).trans
    (concentrated_base_gaussian_weighted_tube ν U a hσ hbase R hR hRpos hR3 hR4)
  intro z
  by_cases hz : z ∈ gaussianOutwardVariableTube U a σ R
  · have hzS : z ∈ gaussianVariableTube U a σ R := by rw [he] at hz; exact hz.1
    simp only [Set.indicator_of_mem hz,Set.indicator_of_mem hzS,le_refl]
  · simp only [Set.indicator_of_not_mem hz]
    by_cases hzS : z ∈ gaussianVariableTube U a σ R
    · simp only [Set.indicator_of_mem hzS]
      exact pow_nonneg (hRpos z.2).le 4
    · simp only [Set.indicator_of_not_mem hzS,le_refl]

end
end RectangleCLTArxivV1
