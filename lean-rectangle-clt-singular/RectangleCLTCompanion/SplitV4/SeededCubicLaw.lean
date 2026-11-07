import RectangleCLTCompanion.SplitV4.SeededFourthLaw
import RectangleCLTCompanion.SplitV4.DirectCubicMoments
import RectangleCLTCompanion.SplitV4.GenericC4CubicLaw

/-! The signed cubic contraction under the actual seeded interpolation
law equals the unshifted paired-restoration product expectation. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem restorationThirdDerivative_diagonal_eq_canonical {p : ℕ} (s : FaceSmoother p)
    (x y : Vector p) : restorationThirdDerivative s x y y = canonicalDiagonal s.F 3 x y := by
  unfold restorationThirdDerivative canonicalDiagonal
  congr 1
  funext i
  fin_cases i <;> rfl

theorem relativeCubicContraction_eq_copy_integral
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {M₃ M₄ : ℝ} (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (x : Vector p) :
    relativeCubicContraction s μ ξ x =
      ∫ a : Ω × Ω, ∑ i, canonicalDiagonal s.F 3 x (ξ i a.1) ∂μ.prod μ := by
  have hi (i : Fin n) : Integrable (fun a : Ω × Ω => canonicalDiagonal s.F 3 x (ξ i a.1)) (μ.prod μ) := by
    have hf : MeasurePreserving (Prod.fst : Ω × Ω → Ω) (μ.prod μ) μ := ⟨measurable_fst, by simp⟩
    have he := hrel.integrable_canonical_third_diagonal s x i
    exact (hf.integrable_comp he.aestronglyMeasurable).mpr he
  rw [integral_finset_sum _ (fun i _ => hi i),
    relativeCubicContraction_eq_sum_integral_canonical_third s hrel x]
  apply Finset.sum_congr rfl
  intro i _
  simpa only [canonicalDiagonal, measureReal_univ_eq_one, one_smul] using
    (integral_fun_fst (μ := μ) (ν := μ) (fun ω => iteratedFDeriv ℝ 3 s.F x (fun _ => ξ i ω))).symm

theorem relativeCubicContraction_eq_generic
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    {M₃ M₄ : ℝ} (hrel : RelativeMomentBounds μ ξ M₃ M₄) :
    relativeCubicContraction s μ ξ = genericCubicContraction μ s.F ξ := by
  funext x
  exact relativeCubicContraction_eq_sum_integral_canonical_third s hrel x

theorem continuous_smoother_canonicalDiagonal {p k : ℕ} (s : FaceSmoother p) (hk : k ≤ 4) :
    Continuous (fun z : Vector p × Vector p => canonicalDiagonal s.F k z.1 z.2) := by
  have hF : ContDiff ℝ 4 s.F := s.contDiff_F_translation.of_le (by simp)
  unfold canonicalDiagonal
  exact ((hF.continuous_iteratedFDeriv (m := k) (by exact_mod_cast hk)).comp continuous_fst).eval
    (continuous_pi (fun _ => continuous_snd))

set_option maxHeartbeats 1000000 in
theorem seeded_relative_cubic_law_eq_product
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ M₃ M₄ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hrel : RelativeMomentBounds μ ξ M₃ M₄)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A * A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (∫ y, relativeCubicContraction s μ ξ (x + y) ∂seededInterpolationLaw μ ξ A ε t) =
      restorationThirdExpectation s ((splitBaseLaw μ ξ t).prod (μ.prod μ)) A
        (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
        (seededCopyOriginal ξ) (fun _ _ => 0) (seededSplitGaussianScale ε t) := by
  let Β := (Fin n → Vector p) × Vector p
  let ρ := splitBaseLaw μ ξ t
  let τ := μ.prod μ
  let γ := standardGaussian p
  let σ := seededSplitGaussianScale ε t
  letI : IsProbabilityMeasure ρ := splitBaseLaw_isProbability μ ξ h.measurable ht ht1
  have hF : ContDiff ℝ 4 s.F := s.contDiff_F_translation.of_le (by simp)
  have hC := smootherC4Bound_nonneg s
  have hjet : ∀ y, ‖iteratedFDeriv ℝ 3 s.F y‖ ≤ smootherC4Bound s :=
    smoother_iteratedFDeriv_norm_le s 3 (by decide) (by decide)
  let P : Β × Vector p → Vector p := fun bg => seededSplitBaseValue A x ε t bg.1 + (σ • A).mulVec bg.2
  have hP : Measurable P :=
    ((measurable_seededSplitBaseValue A x ε t).comp measurable_fst).add
      ((measurable_mulVec _).comp measurable_snd)
  let F : Β × (Vector p × (Ω × Ω)) → ℝ := fun z =>
    ∑ i, canonicalDiagonal s.F 3 (P (z.1, z.2.1)) (ξ i z.2.2.1)
  have hFm : Measurable F := Finset.measurable_sum _ (fun i _ =>
    (continuous_smoother_canonicalDiagonal s (by decide : 3 ≤ 4)).measurable.comp
      ((hP.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
        ((h.measurable i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))))
  have hFi : Integrable F (ρ.prod (γ.prod τ)) := by
    apply integrable_finset_sum
    intro i _
    exact integrable_canonicalDiagonal_bounded (ρ.prod (γ.prod τ)) hF (by decide) _ _
      (hP.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))
      ((h.measurable i).comp (measurable_fst.comp (measurable_snd.comp measurable_snd)))
      hC h.delta_nonneg hjet
      (Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_snd.ae
        (Measure.quasiMeasurePreserving_fst.ae (h.bounded i))))
  have hperm : MeasurePreserving (fun z : (Β × (Ω × Ω)) × Vector p => (z.1.1, (z.2, z.1.2)))
      ((ρ.prod τ).prod γ) (ρ.prod (γ.prod τ)) :=
    ((MeasurePreserving.id ρ).prod (Measure.measurePreserving_swap (μ := τ) (ν := γ))).comp
      (measurePreserving_prodAssoc ρ τ γ)
  have htransport : (∫ z : (Β × (Ω × Ω)) × Vector p, F (z.1.1, (z.2, z.1.2)) ∂(ρ.prod τ).prod γ) =
      ∫ z, F z ∂ρ.prod (γ.prod τ) := by
    calc
      _ = ∫ z, F z ∂((ρ.prod τ).prod γ).map (fun z : (Β × (Ω × Ω)) × Vector p =>
          (z.1.1, (z.2, z.1.2))) := (integral_map hperm.measurable.aemeasurable hFm.aestronglyMeasurable).symm
      _ = _ := by rw [hperm.map_eq]
  have hraw : restorationThirdExpectation s (ρ.prod τ) A
      (fun z => seededSplitBaseValue A x ε t z.1) (seededCopyWhitened A ξ)
      (seededCopyOriginal ξ) (fun _ _ => 0) σ =
      ∫ z : (Β × (Ω × Ω)) × Vector p, F (z.1.1, (z.2, z.1.2)) ∂(ρ.prod τ).prod γ := by
    unfold restorationThirdExpectation
    apply integral_congr_ae
    have hre := seededCopyWhitened_reconstruct ρ μ ξ h A hA
    filter_upwards [Measure.quasiMeasurePreserving_fst.ae (ae_all_iff.mpr hre)] with z hz
    apply Finset.sum_congr rfl
    intro i _
    rw [hz i, add_zero, restorationThirdDerivative_diagonal_eq_canonical]
    dsimp only [F, P, seededCopyOriginal]
    rw [add_comm ((σ • A).mulVec z.2)]
  have hRi : Integrable (fun bg => relativeCubicContraction s μ ξ (P bg)) (ρ.prod γ) := by
    rw [relativeCubicContraction_eq_generic s μ ξ hrel]
    exact integrable_genericCubicContraction_comp (ρ.prod γ) μ ξ h hF hC hjet P hP
  have hcollapse : (∫ z, F z ∂ρ.prod (γ.prod τ)) =
      ∫ bg, relativeCubicContraction s μ ξ (P bg) ∂ρ.prod γ := by
    rw [integral_prod _ hFi, integral_prod _ hRi]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro b
    have hsection : Integrable (fun ga : Vector p × (Ω × Ω) => F (b, ga)) (γ.prod τ) := by
      apply integrable_finset_sum
      intro i _
      exact integrable_canonicalDiagonal_bounded (γ.prod τ) hF (by decide) _ _
        (hP.comp (measurable_const.prodMk measurable_fst))
        ((h.measurable i).comp (measurable_fst.comp measurable_snd)) hC h.delta_nonneg hjet
        (Measure.quasiMeasurePreserving_snd.ae (Measure.quasiMeasurePreserving_fst.ae (h.bounded i)))
    dsimp only
    rw [integral_prod _ hsection]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun g => (relativeCubicContraction_eq_copy_integral s μ ξ hrel (P (b, g))).symm)
  have hCm : Measurable (relativeCubicContraction s μ ξ) := by
    rw [relativeCubicContraction_eq_generic s μ ξ hrel]
    exact (continuous_genericCubicContraction μ ξ h hF hC hjet).measurable
  have hlaw := seededGaussianSplit_law μ ξ h.measurable A x hε ht ht1
  change (ρ.prod γ).map P = (seededInterpolationLaw μ ξ A ε t).map (fun y => x + y) at hlaw
  have hfinal : (∫ bg, relativeCubicContraction s μ ξ (P bg) ∂ρ.prod γ) =
      ∫ y, relativeCubicContraction s μ ξ (x + y) ∂seededInterpolationLaw μ ξ A ε t := by
    rw [← integral_map hP.aemeasurable hCm.aestronglyMeasurable, hlaw]
    have hshift : Measurable (fun y : Vector p => x + y) := measurable_const.add measurable_id
    exact integral_map hshift.aemeasurable hCm.aestronglyMeasurable
  exact (hraw.trans (htransport.trans (hcollapse.trans hfinal))).symm

end

end RectangleCLT.Companion.SplitV4
