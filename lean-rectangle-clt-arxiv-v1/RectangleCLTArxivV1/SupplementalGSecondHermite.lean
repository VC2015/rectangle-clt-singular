import RectangleCLTArxivV1.SupplementalGMatrixRestoration
import RectangleCLTArxivV1.SupplementalGConditionalAE
import RectangleCLTArxivV1.SupplementalGHermiteNuclearMoments

/-! The signed second-Hermite pair restoration, preserving each original
pair selector until the actual G.2 mass is applied. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem capSecondHermite_conditional_copy_measurable
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ξ) [SFinite μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZ : ∀ i, Measurable (Z i))
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p) :
    StronglyMeasurable (fun z : Ω × Vector r => ∑ i, ∫ ξ,
      (c i (z.1,ξ)*repeatedDirectionScore z.2 (Z i ξ))*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i (z.1,ξ)) ∂μ) := by
  apply Finset.stronglyMeasurable_sum
  intro i _
  have hc' : Measurable (fun z : (Ω × Vector r) × Ξ => c i (z.1.1,z.2)) :=
    (hc i).comp (measurable_fst.fst.prodMk measurable_snd)
  have hv' : Measurable (fun z : (Ω × Vector r) × Ξ => v i (z.1.1,z.2)) :=
    (hv i).comp (measurable_fst.fst.prodMk measurable_snd)
  have hs' : Measurable (fun z : (Ω × Vector r) × Ξ => repeatedDirectionScore z.1.2 (Z i z.2)) :=
    (measurable_repeatedDirectionScore_product (Z i) (hZ i)).comp
      (measurable_snd.prodMk measurable_fst.snd)
  have hx : Measurable (fun z : (Ω × Vector r) × Ξ => A.mulVec z.1.2+V z.1.1+v i (z.1.1,z.2)) := by
    exact (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_fst.snd).add
      (hV.comp measurable_fst.fst)).add hv'
  have hmi := (hc'.mul hs').mul (measurable_selectorTupleWeight_comp s α _ hx)
  exact hmi.stronglyMeasurable.integral_prod_right'

/-- G.3 intermediate bound with an explicit G.2 selector-mass input.
The copy distribution has only an actual quadratic budget; the displacement
and coefficient may depend jointly on the copy and the base point. -/
theorem capSecondHermite_conditional_mass_bound
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Measure Ξ) [SFinite κ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p)
    {b K R M : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hcb : ∀ i ω, ∀ᵐ ξ ∂κ, |c i (ω,ξ)| ≤ b)
    (hvb : ∀ i ω, ∀ᵐ ξ ∂κ, ‖v i (ω,ξ)‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ))
    (hNi : Integrable (fun g => symmetricNuclearNorm (rankOne g-1)) (standardGaussian r))
    (hmass : ∀ g, ∫ ω, selectorTupleWeight s α (A.mulVec g+V ω) ∂μ ≤ M) :
    Integrable (fun g => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) (standardGaussian r) ∧
    |∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r| ≤
      (2*3^k*b*K)*M*(∫ g, symmetricNuclearNorm (rankOne g-1) ∂standardGaussian r) := by
  let f (z : Ω × Vector r) := ∑ i, ∫ ξ,
    (c i (z.1,ξ)*repeatedDirectionScore z.2 (Z i ξ))*
      selectorTupleWeight s α (A.mulVec z.2+V z.1+v i (z.1,ξ)) ∂κ
  let w (z : Ω × Vector r) := selectorTupleWeight s α (A.mulVec z.2+V z.1)
  have hfm : StronglyMeasurable f := capSecondHermite_conditional_copy_measurable s κ A V hV
    Z hZm c hc v hv α
  have hwm : Measurable w := measurable_selectorTupleWeight_comp s α _
    (((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst))
  have hf (z : Ω × Vector r) : |f z| ≤
      (2*3^k*b*K)*symmetricNuclearNorm (rankOne z.2-1)*w z := by
    have hM : (rankOne z.2-(1 : Matrix (Fin r) (Fin r) ℝ)).IsHermitian := by
      rw [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial]
      ext j l
      simp [rankOne,Matrix.one_apply,eq_comm,mul_comm]
    have ht := capMatrix_translated_copy_bound_numeric s κ Z (fun i ξ => c i (z.1,ξ))
      (fun i ξ => v i (z.1,ξ)) α hZm hZ
      (fun i => (hc i).comp measurable_prodMk_left) (fun i => (hv i).comp measurable_prodMk_left)
      hb hK hR (fun i => hcb i z.1) (fun i => hvb i z.1) hbudget hsmall
      (A.mulVec z.2+V z.1) (rankOne z.2-1) hM
    simpa only [← repeatedDirectionScore_eq_quadratic] using ht
  exact cap_conditional_mass_integral_bound μ (standardGaussian r) f w _ hfm hwm hNi
    (by positivity) hM (fun g => symmetricNuclearNorm_nonneg _) (fun z => selectorTupleWeight_nonneg s α _)
    (fun z => selectorTupleWeight_le_one s α _) hf hmass


theorem capSecondHermite_conditional_mass_bound_ae
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Measure Ξ) [SFinite κ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p)
    {b K R M : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hcb : ∀ i, ∀ᵐ z ∂μ.prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂μ.prod κ, ‖v i z‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ))
    (hNi : Integrable (fun g => symmetricNuclearNorm (rankOne g-1)) (standardGaussian r))
    (hmass : ∀ g, ∫ ω, selectorTupleWeight s α (A.mulVec g+V ω) ∂μ ≤ M) :
    Integrable (fun g => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) (standardGaussian r) ∧
    |∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r| ≤
      (2*3^k*b*K)*M*(∫ g, symmetricNuclearNorm (rankOne g-1) ∂standardGaussian r) := by
  let c' i := capClippedCoefficient (c i) (v i) b R
  let v' i := capClippedShift (c i) (v i) b R
  have ht := capSecondHermite_conditional_mass_bound s μ κ A V hV Z hZm hZ c'
    (fun i => capClippedCoefficient_measurable _ _ (hc i) (hv i) b R) v'
    (fun i => capClippedShift_measurable _ _ (hc i) (hv i) b R) α hb hK hR hM
    (fun i _ => ae_of_all _ (fun ξ => capClippedCoefficient_abs_le _ _ hb _))
    (fun i _ => ae_of_all _ (fun ξ => capClippedShift_norm_le _ _ hR _)) hbudget hsmall hNi hmass
  have he : (fun g : Vector r => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) =
      (fun g : Vector r => ∫ ω, ∑ i, ∫ ξ,
      (c' i (ω,ξ)*repeatedDirectionScore g (Z i ξ))*
        selectorTupleWeight s α (A.mulVec g+V ω+v' i (ω,ξ)) ∂κ ∂μ) := by
    funext g
    exact cap_joint_clipping_iterated_eq s μ κ c hc v hv hcb hvb
      (fun i ξ => repeatedDirectionScore g (Z i ξ)) (fun ω => A.mulVec g+V ω) α
  rw [he]
  exact ht

end
end RectangleCLTArxivV1
