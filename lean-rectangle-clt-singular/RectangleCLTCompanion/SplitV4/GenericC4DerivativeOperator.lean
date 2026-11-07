import RectangleCLTCompanion.SplitV4.GenericC4SelectorAlgebra

/-! The actual general-C4 seeded-path derivative as the Gaussian average
of the finite selector operator. Gaussian integration by parts, product
integrability, and finite selector regrouping are proved independently. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

/-- No rank or lower eigenvalue assumption is made on the Gaussian factor.
The test itself may be unbounded; its genuine bounded derivatives give all
value, gradient and Hessian integrability used in this identity. -/
theorem genericVariableSelectorDerivative_eq_operator
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    {δ : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (A : Matrix (Fin p) (Fin p) ℝ) (γ γ' : ℝ → ℝ) (ε : ℝ)
    (x : Vector p) {t : ℝ} (ht : 0 < t+ε) :
    (C4Test.ofContDiff F hF C hC hjet).genericVariableSelectorDerivative μ ξ A γ γ' ε x t =
      ∫ g, genericSelectorOperator μ F ξ (A*A.transpose) (x+Real.sqrt (t+ε) • g)
        (variableRetention γ t) (γ t) (variableRetentionDerivative γ γ' t)
        (variableRetention γ t*γ' t) ∂gaussianLaw A := by
  let f := C4Test.ofContDiff F hF C hC hjet
  let ν := gaussianLaw A
  let q := variableRetention γ t
  let a := γ t
  let c := variableRetentionDerivative γ γ' t
  let s := Real.sqrt (t+ε)
  let S := A*A.transpose
  let P : Kane.Cube n → Ω × Vector p → Vector p := fun mask z =>
    x+a • maskObservationSum ξ mask z.1+s • z.2
  let V : Kane.Cube n → Vector p → ℝ := fun mask g => ∫ ω, f.value (P mask (ω,g)) ∂μ
  let G : Fin n → Kane.Cube n → Vector p → ℝ := fun i mask g =>
    ∫ ω, f.gradient (P mask (ω,g)) (ξ i ω) ∂μ
  let H : Kane.Cube n → Vector p → ℝ := fun mask g =>
    (1/2 : ℝ)*∑ j, ∑ k, S j k*(∫ ω, f.hessianCoordinate (P mask (ω,g)) j k ∂μ)
  have hP (mask : Kane.Cube n) : Measurable (P mask) :=
    (measurable_const.add (measurable_const.smul
      ((measurable_maskObservationSum ξ h.measurable mask).comp measurable_fst))).add
      (measurable_const.smul measurable_snd)
  have hval (mask : Kane.Cube n) : Integrable (fun z : Ω × Vector p => f.value (P mask z)) (μ.prod ν) :=
    f.integrable_genericVariableHeatValue μ _ (measurable_maskObservationSum ξ h.measurable mask)
      (maskObservationSum_bounded μ ξ h.delta_nonneg h.bounded mask) A γ ε x t
  have hgrad (i : Fin n) (mask : Kane.Cube n) :
      Integrable (fun z : Ω × Vector p => f.gradient (P mask z) (ξ i z.1)) (μ.prod ν) := by
    apply f.integrable_gradient_direction_of_norm _ _ _ (hP mask) ((h.measurable i).comp measurable_fst)
    have hh : Integrable (fun ω => ‖ξ i ω‖) μ :=
      ((integrable_const δ).mono' (h.measurable i).aestronglyMeasurable (h.bounded i)).norm
    simpa only [mul_one] using hh.mul_prod (integrable_const (1 : ℝ) : Integrable (fun _ : Vector p => (1 : ℝ)) ν)
  have hhess (mask : Kane.Cube n) (j k : Fin p) :
      Integrable (fun z : Ω × Vector p => f.hessianCoordinate (P mask z) j k) (μ.prod ν) :=
    f.integrable_hessianCoordinate _ _ (hP mask) j k
  have hVi (mask : Kane.Cube n) : Integrable (V mask) ν := (hval mask).integral_prod_right
  have hGi (i : Fin n) (mask : Kane.Cube n) : Integrable (G i mask) ν := (hgrad i mask).integral_prod_right
  have hHi (mask : Kane.Cube n) : Integrable (H mask) ν :=
    (integrable_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
      (fun k _ => (hhess mask j k).integral_prod_right.const_mul (S j k)))).const_mul (1/2)
  have hGif (mask : Kane.Cube n) (i : Fin n) :
      Integrable (fun g => if mask i then G i mask g else 0) ν := by
    by_cases hi : mask i = true
    · simpa only [hi, ↓reduceIte] using hGi i mask
    · simpa only [hi, ↓reduceIte] using (integrable_const (0 : ℝ) : Integrable (fun _ : Vector p => (0 : ℝ)) ν)
  have hGsum (mask : Kane.Cube n) : Integrable (fun g => ∑ i, if mask i then G i mask g else 0) ν :=
    integrable_finset_sum Finset.univ (fun i _ => hGif mask i)
  have hvalue (mask : Kane.Cube n) :
      f.genericVariableHeatExpectation μ (maskObservationSum ξ mask) A γ ε x t = ∫ g, V mask g ∂ν :=
    integral_prod_symm _ (hval mask)
  have hspace (mask : Kane.Cube n) :
      (∫ z : Ω × Vector p, f.gradient (P mask z) (maskObservationSum ξ mask z.1) ∂μ.prod ν) =
        ∫ g, ∑ i, if mask i then G i mask g else 0 ∂ν := by
    have hi (i : Fin n) : Integrable (fun z : Ω × Vector p =>
        if mask i then f.gradient (P mask z) (ξ i z.1) else 0) (μ.prod ν) := by
      by_cases hii : mask i = true
      · simpa only [hii, ↓reduceIte] using hgrad i mask
      · simpa only [hii, ↓reduceIte] using (integrable_const (0 : ℝ) : Integrable (fun _ : Ω × Vector p => (0 : ℝ)) (μ.prod ν))
    have he (z : Ω × Vector p) : f.gradient (P mask z) (maskObservationSum ξ mask z.1) =
        ∑ i, if mask i then f.gradient (P mask z) (ξ i z.1) else 0 := by
      simp only [maskObservationSum, map_sum]
      apply Finset.sum_congr rfl
      intro i _
      split <;> simp_all only [map_zero]
    simp_rw [he]
    rw [integral_finset_sum Finset.univ (fun i _ => hi i),
      integral_finset_sum Finset.univ (fun i _ => hGif mask i)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hii : mask i = true
    · simp only [hii, ↓reduceIte]
      exact integral_prod_symm _ (hgrad i mask)
    · simp only [hii, Bool.false_eq_true, ↓reduceIte, integral_zero]
  have hheat (mask : Kane.Cube n) :
      (1/2 : ℝ)*∑ j, ∑ k, S j k*(∫ z : Ω × Vector p,
        f.hessianCoordinate (P mask z) j k ∂μ.prod ν) = ∫ g, H mask g ∂ν := by
    rw [integral_const_mul]
    congr 1
    rw [integral_finset_sum Finset.univ (fun j _ => integrable_finset_sum Finset.univ
      (fun k _ => (hhess mask j k).integral_prod_right.const_mul (S j k)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ => (hhess mask j k).integral_prod_right.const_mul (S j k))]
    apply Finset.sum_congr rfl
    intro k _
    rw [integral_const_mul]
    exact congrArg (fun z => S j k*z) (integral_prod_symm _ (hhess mask j k))
  have hsplit (mask : Kane.Cube n) :
      f.genericVariableHeatDerivative μ (maskObservationSum ξ mask) A γ γ' ε x t =
        ∫ g, (γ' t*(∑ i, if mask i then G i mask g else 0)+H mask g) ∂ν := by
    rw [f.genericVariableHeatDerivative_eq_spatial_add_heat μ _
      (measurable_maskObservationSum ξ h.measurable mask)
      (maskObservationSum_bounded μ ξ h.delta_nonneg h.bounded mask) A γ γ' ε x ht]
    change γ' t*(∫ z : Ω × Vector p, f.gradient (P mask z) (maskObservationSum ξ mask z.1) ∂μ.prod ν)+
      (1/2 : ℝ)*∑ j, ∑ k, S j k*(∫ z : Ω × Vector p, f.hessianCoordinate (P mask z) j k ∂μ.prod ν) = _
    rw [hspace, hheat]
    simpa only [integral_const_mul] using
      (integral_add ((hGsum mask).const_mul (γ' t)) (hHi mask)).symm
  have hpoint (g : Vector p) :
      (∑ mask : Kane.Cube n, (selectorWeightDerivative q c mask*V mask g+
        Kane.maskWeight q mask*(γ' t*(∑ i, if mask i then G i mask g else 0)+H mask g))) =
      genericSelectorOperator μ F ξ S (x+s • g) q a c (q*γ' t) := by
    have hmass : (∑ mask : Kane.Cube n, selectorWeightDerivative q c mask*V mask g) =
        c*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
          (V (Function.update mask i true) g-V (Function.update mask i false) g)) := by
      simpa only [selectorWeightDerivative, BernoulliSelectorAlgebra.massDerivative,
        BernoulliSelectorAlgebra.coordinateMassDerivative, BernoulliSelectorAlgebra.weightExcept] using
        BernoulliSelectorAlgebra.mass_derivative_regroup q c (fun mask => V mask g)
    have hamp : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(γ' t*∑ i, if mask i then G i mask g else 0)) =
        (q*γ' t)*(∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*G i (Function.update mask i true) g) := by
      calc
        _ = γ' t*(∑ mask : Kane.Cube n, Kane.maskWeight q mask*∑ i, if mask i then G i mask g else 0) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro mask _
          ring
        _ = _ := by rw [BernoulliSelectorAlgebra.retained_amplitude_regroup]; ring
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hmass, hamp]
    have hp (mask : Kane.Cube n) (ω : Ω) : P mask (ω,g) = (x+s • g)+a • maskObservationSum ξ mask ω := by
      dsimp only [P]
      abel
    have hv (mask : Kane.Cube n) : V mask g = genericFixedValue μ F ξ (x+s • g) a mask := by
      simp only [V, hp, genericFixedValue]
      rfl
    have hg (i : Fin n) (mask : Kane.Cube n) : G i mask g = genericFixedGradient μ F ξ (x+s • g) a i mask := by
      simp only [G, hp, genericFixedGradient, f, ofContDiff_gradient_eq_canonicalDiagonal hF hC hjet]
    have hh (mask : Kane.Cube n) : H mask g = genericFixedHeat μ F ξ S (x+s • g) a mask := by
      simp only [H, hp, genericFixedHeat, f, ofContDiff_hessianCoordinate_eq_canonicalHessianCoordinate hF hC hjet]
    simp_rw [hv, hg, hh]
    unfold genericSelectorOperator
    ring
  change (∑ mask : Kane.Cube n, (selectorWeightDerivative q c mask*
    f.genericVariableHeatExpectation μ (maskObservationSum ξ mask) A γ ε x t+
    Kane.maskWeight q mask*f.genericVariableHeatDerivative μ (maskObservationSum ξ mask) A γ γ' ε x t)) = _
  simp_rw [hvalue, hsplit]
  have hi (mask : Kane.Cube n) : Integrable (fun g =>
      selectorWeightDerivative q c mask*V mask g+
      Kane.maskWeight q mask*(γ' t*(∑ i, if mask i then G i mask g else 0)+H mask g)) ν :=
    ((hVi mask).const_mul _).add ((((hGsum mask).const_mul _).add (hHi mask)).const_mul _)
  calc
    _ = ∑ mask : Kane.Cube n, ∫ g,
        (selectorWeightDerivative q c mask*V mask g+
          Kane.maskWeight q mask*(γ' t*(∑ i, if mask i then G i mask g else 0)+H mask g)) ∂ν := by
      apply Finset.sum_congr rfl
      intro mask _
      simpa only [integral_const_mul] using
        (integral_add ((hVi mask).const_mul (selectorWeightDerivative q c mask))
          ((((hGsum mask).const_mul (γ' t)).add (hHi mask)).const_mul (Kane.maskWeight q mask))).symm
    _ = ∫ g, ∑ mask : Kane.Cube n,
        (selectorWeightDerivative q c mask*V mask g+
          Kane.maskWeight q mask*(γ' t*(∑ i, if mask i then G i mask g else 0)+H mask g)) ∂ν :=
      (integral_finset_sum Finset.univ (fun mask _ => hi mask)).symm
    _ = _ := integral_congr_ae (ae_of_all _ hpoint)

end
end RectangleCLT.Companion.SplitV4
