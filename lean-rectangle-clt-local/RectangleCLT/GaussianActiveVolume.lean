import RectangleCLT.GaussianTubeDisintegration
import RectangleCLT.GaussianNormalMap

/-! The actual standard-Gaussian and active-exponential product experiment as
an augmented Lebesgue integral. This is a nonnegative transport identity and
requires no geometry, nondegeneracy, or integrability hypothesis. -/

open MeasureTheory
open scoped BigOperators ENNReal

namespace RectangleCLT.GaussianTube

theorem measurable_base_projection {p q : ℕ} :
    Measurable (base : Coordinates p q → Vector p) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (Sum.inl j))

theorem measurable_tube_projection {p q : ℕ} :
    Measurable (tube : Coordinates p q → (Fin q → ℝ)) :=
  measurable_pi_lambda _ (fun i => measurable_pi_apply (Sum.inr i))

theorem measurableSet_positive_tube (p q : ℕ) :
    MeasurableSet {y : Coordinates p q | ∀ i, 0 < tube y i} := by
  simp only [Set.setOf_forall]
  exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const
    (measurable_pi_apply (Sum.inr i)))

/-- Split the actual Gaussian and independent exponential coordinates into
augmented Lebesgue coordinates. Zero-dimensional blocks are allowed. -/
theorem lintegral_standardGaussian_exponential_eq_volume
    {p q : ℕ} (H : Vector p × (Fin q → ℝ) → ℝ≥0∞) (hH : Measurable H) :
    (∫⁻ z : Vector p, ∫⁻ a : Fin q → ℝ, H (z, a)
      ∂Measure.pi (fun _ : Fin q => unitExponential) ∂standardGaussian p) =
      ∫⁻ y : Coordinates p q in {y | ∀ i, 0 < tube y i},
        ENNReal.ofReal (standardGaussianDensity p (base y) * Real.exp (-(∑ i, tube y i))) *
          H (base y, tube y) := by
  let P : Set (Fin q → ℝ) := {a | ∀ i, 0 < a i}
  let D : Set (Vector p × (Fin q → ℝ)) := {w | ∀ i, 0 < w.2 i}
  let E : Vector p × (Fin q → ℝ) → ℝ≥0∞ := fun w =>
    ENNReal.ofReal (standardGaussianDensity p w.1 * Real.exp (-(∑ i, w.2 i))) * H w
  let F : Vector p × (Fin q → ℝ) → ℝ≥0∞ := D.indicator E
  have hP : MeasurableSet P := by
    simp only [P, Set.setOf_forall]
    exact MeasurableSet.iInter (fun i => measurableSet_lt measurable_const (measurable_pi_apply i))
  have hD : MeasurableSet D := hP.preimage measurable_snd
  have hsum : Measurable (fun w : Vector p × (Fin q → ℝ) => ∑ i, w.2 i) :=
    Finset.measurable_sum _ (fun i _ => (measurable_pi_apply i).comp measurable_snd)
  have hE : Measurable E :=
    (((standardGaussianDensity_measurable p).comp measurable_fst).mul hsum.neg.exp).ennreal_ofReal.mul hH
  have hF : Measurable F := hE.indicator hD
  have hinner (z : Vector p) :
      ENNReal.ofReal (standardGaussianDensity p z) *
          (∫⁻ a : Fin q → ℝ, H (z, a) ∂Measure.pi (fun _ : Fin q => unitExponential)) =
        ∫⁻ a : Fin q → ℝ, F (z, a) := by
    have hsec : Measurable (fun a : Fin q → ℝ => H (z, a)) :=
      hH.comp (measurable_const.prodMk measurable_id)
    rw [exponentialProductLaw_lintegral q _ hsec]
    rw [← lintegral_const_mul' (ENNReal.ofReal (standardGaussianDensity p z)) _ ENNReal.ofReal_ne_top]
    rw [← lintegral_indicator hP]
    apply lintegral_congr_ae
    refine ae_of_all _ (fun a => ?_)
    by_cases ha : ∀ i, 0 < a i
    · simp [F, D, E, P, Set.indicator, ha,
        ENNReal.ofReal_mul (standardGaussianDensity_pos p z).le, mul_assoc]
    · simp [F, D, E, P, Set.indicator, ha]
  have houter : Measurable (fun z : Vector p =>
      ∫⁻ a : Fin q → ℝ, H (z, a) ∂Measure.pi (fun _ : Fin q => unitExponential)) := by
    have hunc : Measurable (Function.uncurry
        (fun (z : Vector p) (a : Fin q → ℝ) => H (z, a))) := hH
    exact hunc.lintegral_prod_right
  have hsplit := (volume_measurePreserving_sumPiEquivProdPi
    (fun _ : Fin p ⊕ Fin q => ℝ)).lintegral_comp hF
  calc
    _ = ∫⁻ z : Vector p, ENNReal.ofReal (standardGaussianDensity p z) *
        (∫⁻ a : Fin q → ℝ, H (z, a) ∂Measure.pi (fun _ : Fin q => unitExponential)) := by
      rw [standardGaussian_eq_withDensity,
        lintegral_withDensity_eq_lintegral_mul _
          (standardGaussianDensity_measurable p).ennreal_ofReal houter]
      rfl
    _ = ∫⁻ z : Vector p, ∫⁻ a : Fin q → ℝ, F (z, a) := by simp_rw [hinner]
    _ = ∫⁻ w : Vector p × (Fin q → ℝ), F w ∂(volume.prod volume) :=
      (lintegral_prod _ hF.aemeasurable).symm
    _ = ∫⁻ y : Coordinates p q, F (base y, tube y) := by
      exact hsplit.symm
    _ = _ := by
      rw [← lintegral_indicator (measurableSet_positive_tube p q)]
      rfl

end RectangleCLT.GaussianTube
