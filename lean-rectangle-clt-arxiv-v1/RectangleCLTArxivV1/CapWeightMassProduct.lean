import RectangleCLTArxivV1.CapWeightMass

/-! Independent translations preserve the actual uniform G.2 tuple masses. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- Actual averaging of a uniformly translated tuple mass. No moment or
boundedness assumption on the independent translation is needed. -/
theorem integral_logisticTupleWeight_product_le
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (τ : Measure Ξ) [IsProbabilityMeasure τ]
    {m p k : ℕ} (U : Fin m → Vector p) (a : Vector m) {h M : ℝ} (hh : 0 < h)
    (α : Fin k → Fin m) (Y : Ω → Vector p) (hY : Measurable Y)
    (R : Ξ → Vector p) (hR : Measurable R)
    (hfixed : ∀ b : Vector p, (∫ ω, logisticTupleWeight U a h α (Y ω+b) ∂μ) ≤ M) :
    (∫ z, logisticTupleWeight U a h α (Y z.1+R z.2) ∂μ.prod τ) ≤ M := by
  let F : Ω × Ξ → ℝ := fun z => logisticTupleWeight U a h α (Y z.1+R z.2)
  have hFm : Measurable F := (continuous_logisticTupleWeight U a h hh α).measurable.comp
    ((hY.comp measurable_fst).add (hR.comp measurable_snd))
  have hFi : Integrable F (μ.prod τ) :=
    (integrable_const (1:ℝ)).mono' hFm.aestronglyMeasurable
      (ae_of_all _ (fun z => by rw [Real.norm_eq_abs]; exact logisticTupleWeight_abs_le_one U a h hh α _))
  rw [integral_prod_symm _ hFi]
  have hi := integral_mono hFi.integral_prod_right (integrable_const M) (fun b => hfixed (R b))
  simpa only [integral_const,measureReal_univ_eq_one,one_smul] using hi

/-- G.2 single-face mass with an arbitrary independent shift. -/
theorem cap_one_face_tuple_mass_product
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {h : ℝ}
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 < h) (hband : δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c : ℝ)
    (hproj : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+c)
    (τ : Measure Ξ) [IsProbabilityMeasure τ] (R : Ξ → Vector p) (hR : Measurable R) :
    (∫ z, logisticTupleWeight U a h ![j] (Y z.1+R z.2)
      ∂(μ.prod (standardGaussian r)).prod τ) ≤
      16*Real.exp (1/2)*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  apply integral_logisticTupleWeight_product_le _ τ U a hh ![j] Y hY R hR
  intro b
  apply cap_one_face_tuple_mass hdata A hvar hh hband U a j
    (fun z => Y z+b) (hY.add_const b) (c+faceDot (U j) b)
  intro z
  rw [show faceDot (U j) (Y z+b) = faceDot (U j) (Y z)+faceDot (U j) b from by
    simp [faceDot,mul_add,Finset.sum_add_distrib],hproj]
  ring

/-- G.2 pair-face mass with an arbitrary independent shift. -/
theorem cap_two_face_tuple_mass_product
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {v ρ h : ℝ}
    (hv : (1/2 : ℝ) ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 < h) (hband : 2*δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j k : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c₀ c₁ : ℝ)
    (hproj₀ : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+c₀)
    (hproj₁ : ∀ z, faceDot (U k) (Y z) = capMixedValue X A z 1+c₁)
    (τ : Measure Ξ) [IsProbabilityMeasure τ] (R : Ξ → Vector p) (hR : Measurable R) :
    (∫ z, logisticTupleWeight U a h ![j,k] (Y z.1+R z.2)
      ∂(μ.prod (standardGaussian r)).prod τ) ≤
      64*Real.exp 1*Real.pi^3*h^2/Real.sqrt (1-ρ^2) := by
  apply integral_logisticTupleWeight_product_le _ τ U a hh ![j,k] Y hY R hR
  intro b
  apply cap_two_face_tuple_mass hdata A hv hρ hcov hh hband U a j k
    (fun z => Y z+b) (hY.add_const b) (c₀+faceDot (U j) b) (c₁+faceDot (U k) b)
  · intro z
    rw [show faceDot (U j) (Y z+b) = faceDot (U j) (Y z)+faceDot (U j) b from by
      simp [faceDot,mul_add,Finset.sum_add_distrib],hproj₀]
    ring
  · intro z
    rw [show faceDot (U k) (Y z+b) = faceDot (U k) (Y z)+faceDot (U k) b from by
      simp [faceDot,mul_add,Finset.sum_add_distrib],hproj₁]
    ring

end
end RectangleCLTArxivV1
