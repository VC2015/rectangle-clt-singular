import RectangleCLTArxivV1.SupplementalGScoreRestoration

/-! Conditional averaging of the signed restoration bound. The local selector
mass hypothesis is an explicit intermediate input; it is supplied by G.2. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

/-- A uniform translated local-mass estimate can be used after the signed
copy average. The positive weight remains inside the base expectation. -/
theorem cap_conditional_mass_integral_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ν : Measure Ξ)
    (f w : Ω × Ξ → ℝ) (N : Ξ → ℝ)
    (hfm : StronglyMeasurable f) (hwm : Measurable w) (hNi : Integrable N ν)
    {C M : ℝ} (hC : 0 ≤ C) (hM : 0 ≤ M)
    (hN : ∀ g, 0 ≤ N g) (hw : ∀ z, 0 ≤ w z) (hw1 : ∀ z, w z ≤ 1)
    (hf : ∀ z, |f z| ≤ C*N z.2*w z)
    (hmass : ∀ g, ∫ ω, w (ω,g) ∂μ ≤ M) :
    Integrable (fun g => ∫ ω, f (ω,g) ∂μ) ν ∧
    |∫ g, ∫ ω, f (ω,g) ∂μ ∂ν| ≤ C*M*∫ g, N g ∂ν := by
  have hwi (g : Ξ) : Integrable (fun ω => w (ω,g)) μ := by
    apply (integrable_const (1 : ℝ)).mono'
      (hwm.comp measurable_prodMk_right).aestronglyMeasurable
    exact ae_of_all _ (fun ω => by
      change ‖w (ω,g)‖ ≤ 1
      rw [Real.norm_eq_abs,abs_of_nonneg (hw (ω,g))]
      exact hw1 (ω,g))
  have hb (g : Ξ) : |∫ ω, f (ω,g) ∂μ| ≤ C*M*N g := by
    have ht := norm_integral_le_of_norm_le (f := fun ω => f (ω,g)) ((hwi g).const_mul (C*N g))
      (ae_of_all _ (fun ω => by simpa only [Real.norm_eq_abs] using hf (ω,g)))
    rw [Real.norm_eq_abs,integral_const_mul] at ht
    calc
      _ ≤ (C*N g)*(∫ ω, w (ω,g) ∂μ) := ht
      _ ≤ (C*N g)*M := mul_le_mul_of_nonneg_left (hmass g) (mul_nonneg hC (hN g))
      _ = _ := by ring
  have hFi : Integrable (fun g => ∫ ω, f (ω,g) ∂μ) ν :=
    (hNi.const_mul (C*M)).mono' hfm.integral_prod_left'.aestronglyMeasurable
      (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  refine ⟨hFi, ?_⟩
  have ht := norm_integral_le_of_norm_le (f := fun g => ∫ ω, f (ω,g) ∂μ) (hNi.const_mul (C*M))
    (ae_of_all _ (fun g => by simpa only [Real.norm_eq_abs] using hb g))
  simpa only [Real.norm_eq_abs,integral_const_mul] using ht

/-- Measurability of the actual conditional copy contraction. -/
theorem capThirdHermite_conditional_copy_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZ : ∀ i, Measurable (Z i))
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p) (u : Vector r) :
    StronglyMeasurable (fun z : Ω × Vector r => ∑ i, ∫ ξ,
      (c i (z.1,ξ)*capThirdHermiteScore u (Z i ξ) z.2)*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i (z.1,ξ)) ∂μ) := by
  apply Finset.stronglyMeasurable_sum
  intro i _
  have hc' : Measurable (fun z : (Ω × Vector r) × Ξ => c i (z.1.1,z.2)) :=
    (hc i).comp (measurable_fst.fst.prod_mk measurable_snd)
  have hv' : Measurable (fun z : (Ω × Vector r) × Ξ => v i (z.1.1,z.2)) :=
    (hv i).comp (measurable_fst.fst.prod_mk measurable_snd)
  have hs' : Measurable (fun z : (Ω × Vector r) × Ξ => capThirdHermiteScore u (Z i z.2) z.1.2) :=
    (measurable_capThirdHermiteScore_product u (Z i) (hZ i)).comp
      (measurable_snd.prod_mk measurable_fst.snd)
  have hx : Measurable (fun z : (Ω × Vector r) × Ξ => A.mulVec z.1.2+V z.1.1+v i (z.1.1,z.2)) := by
    exact (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst.snd).add
      (hV.comp measurable_fst.fst)).add hv'
  have hmi := (hc'.mul hs').mul (measurable_selectorTupleWeight_comp s α _ hx)
  exact hmi.stronglyMeasurable.integral_prod_right'

/-- G.3 intermediate bound with an explicit G.2 selector-mass input.
The copy distribution has only an actual quadratic budget; the displacement
and coefficient may depend jointly on the copy and the base point. -/
theorem capThirdHermite_conditional_mass_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Measure Ξ) [SFinite κ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p) (u : Vector r)
    {b K R M : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hcb : ∀ i ω, ∀ᵐ ξ ∂κ, |c i (ω,ξ)| ≤ b)
    (hvb : ∀ i ω, ∀ᵐ ξ ∂κ, ‖v i (ω,ξ)‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ))
    (hNi : Integrable (fun g => symmetricNuclearNorm (capThirdHermiteMatrix u g)) (standardGaussian r))
    (hmass : ∀ g, ∫ ω, selectorTupleWeight s α (A.mulVec g+V ω) ∂μ ≤ M) :
    Integrable (fun g => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) (standardGaussian r) ∧
    |∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r| ≤
      (2*3^k*b*K)*M*(∫ g, symmetricNuclearNorm (capThirdHermiteMatrix u g) ∂standardGaussian r) := by
  let f (z : Ω × Vector r) := ∑ i, ∫ ξ,
    (c i (z.1,ξ)*capThirdHermiteScore u (Z i ξ) z.2)*
      selectorTupleWeight s α (A.mulVec z.2+V z.1+v i (z.1,ξ)) ∂κ
  let w (z : Ω × Vector r) := selectorTupleWeight s α (A.mulVec z.2+V z.1)
  have hfm : StronglyMeasurable f := capThirdHermite_conditional_copy_measurable s κ A V hV
    Z hZm c hc v hv α u
  have hwm : Measurable w := measurable_selectorTupleWeight_comp s α _
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst))
  have hf (z : Ω × Vector r) : |f z| ≤
      (2*3^k*b*K)*symmetricNuclearNorm (capThirdHermiteMatrix u z.2)*w z := by
    exact capThirdHermite_translated_copy_bound_numeric s κ Z (fun i ξ => c i (z.1,ξ))
      (fun i ξ => v i (z.1,ξ)) α hZm hZ
      (fun i => (hc i).comp measurable_prodMk_left) (fun i => (hv i).comp measurable_prodMk_left)
      hb hK hR (fun i => hcb i z.1) (fun i => hvb i z.1) hbudget hsmall
      (A.mulVec z.2+V z.1) u z.2
  exact cap_conditional_mass_integral_bound μ (standardGaussian r) f w _ hfm hwm hNi
    (by positivity) hM (fun g => symmetricNuclearNorm_nonneg _) (fun z => selectorTupleWeight_nonneg s α _)
    (fun z => selectorTupleWeight_le_one s α _) hf hmass

end
end RectangleCLTArxivV1
