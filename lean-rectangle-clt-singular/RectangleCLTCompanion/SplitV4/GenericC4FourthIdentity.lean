import RectangleCLTCompanion.SplitV4.GenericC4SelectorAlgebra
import RectangleCLTCompanion.SplitV4.GenericBernoulliAveraging

/-! Exact signed fourth-order identity for the fixed Gaussian point of
the general smooth-test interpolation. Covariance cancellation and all
copy/mask averaging are conclusions for the actual independent array. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

theorem canonicalDiagonal_two_eq_coordinates {p : ℕ} {F : Vector p → ℝ}
    (hF : ContDiff ℝ 4 F) {C : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (x v : Vector p) : canonicalDiagonal F 2 x v =
      ∑ j, ∑ k, (v j*v k)*canonicalHessianCoordinate F x j k := by
  let f := C4Test.ofContDiff F hF C hC hjet
  have he := f.secondDiagonal_eq_rankOne_hessianTrace x v
  change canonicalDiagonal F 2 x v = ∑ j, ∑ k, (v j*v k)*f.hessianCoordinate x j k at he
  simpa only [f, ofContDiff_hessianCoordinate_eq_canonicalHessianCoordinate] using he

theorem integral_canonicalDiagonal_two_eq_coordinates
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (T : Ω → Vector p) (hT : Measurable T) (hbound : ∀ᵐ ω ∂μ, ‖T ω‖ ≤ δ) (x : Vector p) :
    (∫ u, canonicalDiagonal F 2 x (T u) ∂μ) =
      ∑ j, ∑ k, (∫ u, T u j*T u k ∂μ)*canonicalHessianCoordinate F x j k := by
  have hi (j k : Fin p) : Integrable (fun u => T u j*T u k) μ := by
    simpa [Fin.prod_univ_succ] using integrable_bounded_coordinate_product μ T hT hbound (![j,k] : Fin 2 → Fin p)
  simp_rw [canonicalDiagonal_two_eq_coordinates hF hC hjet]
  rw [integral_finset_sum _ fun j _ => integrable_finset_sum _ fun k _ =>
    (hi j k).mul_const (canonicalHessianCoordinate F x j k)]
  simp_rw [integral_finset_sum _ fun k _ => (hi _ k).mul_const _, integral_mul_const]

theorem canonical_hessianTrace_covariance_eq_moments
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ)) (x : Vector p) :
    (∑ j, ∑ k, (A*A.transpose) j k*canonicalHessianCoordinate F x j k) =
      ∑ i, ∫ u, canonicalDiagonal F 2 x (ξ i u) ∂μ := by
  symm
  simp_rw [integral_canonicalDiagonal_two_eq_coordinates μ hF hC hjet _ (h.measurable _) (h.bounded _)]
  have he : (∑ i, ∑ j, ∑ k, (∫ u, ξ i u j*ξ i u k ∂μ)*canonicalHessianCoordinate F x j k) =
      ∑ j, ∑ k, (∑ i, ∫ u, ξ i u j*ξ i u k ∂μ)*canonicalHessianCoordinate F x j k := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    rw [Finset.sum_comm]
  rw [he]
  have hm (j k : Fin p) : (∑ i, ∫ u, ξ i u j*ξ i u k ∂μ) = (A*A.transpose) j k := by
    rw [hA]
    exact (h.covariance_sum j k).symm
  simp_rw [hm]

theorem genericFixedHeat_eq_half_sum_moments
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (a : ℝ) (mask : Kane.Cube n) :
    genericFixedHeat μ F ξ (A*A.transpose) x a mask =
      (1/2 : ℝ)*∑ i, ∫ ω, (∫ u, canonicalDiagonal F 2 (x+a • maskObservationSum ξ mask ω) (ξ i u) ∂μ) ∂μ := by
  let f := C4Test.ofContDiff F hF C hC hjet
  let W := fun ω => x+a • maskObservationSum ξ mask ω
  have hW : Measurable W := measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ h.measurable mask))
  have he := f.integral_hessianTrace_eq μ W hW (A*A.transpose)
  have hc (y : Vector p) (j k : Fin p) : f.hessianCoordinate y j k = canonicalHessianCoordinate F y j k :=
    ofContDiff_hessianCoordinate_eq_canonicalHessianCoordinate hF hC hjet y j k
  simp_rw [hc] at he
  have hp (y : Vector p) : f.hessianTrace (A*A.transpose) y = ∑ i, ∫ u, canonicalDiagonal F 2 y (ξ i u) ∂μ := by
    unfold C4Test.hessianTrace
    simp_rw [hc]
    exact canonical_hessianTrace_covariance_eq_moments μ hF hC hjet ξ h A hA y
  unfold genericFixedHeat
  rw [← he]
  simp_rw [hp]
  have hi (i : Fin n) : Integrable (fun ω => ∫ u, canonicalDiagonal F 2 (W ω) (ξ i u) ∂μ) μ := by
    have hh := integrable_genericBernoulliMoment_base μ μ hF (by decide) hC h.delta_nonneg
      (hjet 2 (by decide) (by decide)) W hW (ξ i) (h.measurable i) (h.bounded i) 0 0
    simpa only [genericBernoulliMoment, sub_zero, one_mul, zero_mul, add_zero] using hh
  rw [integral_finset_sum _ fun i _ => hi i]

def genericFullMoment {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (k : ℕ) (ξ : Fin n → Ω → Vector p)
    (i : Fin n) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ ω, (∫ u, canonicalDiagonal F k (x+a • maskObservationSum ξ mask ω) (ξ i u) ∂μ) ∂μ

def genericCommonCubic {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p) (x : Vector p) (q a : ℝ) : ℝ :=
  ∑ i, genericFullMoment μ F 3 ξ i x q a

def genericSelectorFourthRemainder {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (F : Vector p → ℝ) (ξ : Fin n → Ω → Vector p)
    (x : Vector p) (q a c b d : ℝ) : ℝ :=
  ∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
    ∫ ω, genericRowFourthTotal μ F (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ

private theorem generic_weighted_three {α : Type*} [Fintype α]
    (w f g r : α → ℝ) (c d : ℝ) :
    (∑ z, w z*(c*f z+d*g z+r z)) =
      c*(∑ z, w z*f z)+d*(∑ z, w z*g z)+∑ z, w z*r z := by
  calc
    _ = ∑ z, (c*(w z*f z)+d*(w z*g z)+w z*r z) := by
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by simp only [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem generic_row_mask_commonPoint_identity
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (i : Fin n) (x : Vector p) (q a c b d : ℝ) (ha : a ≠ 0)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω, genericRowOperator μ F (ξ i)
      (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) =
      -(1/2 : ℝ)*genericFullMoment μ F 2 ξ i x q a+d*genericFullMoment μ F 3 ξ i x q a+
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω, genericRowFourthTotal μ F (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ) := by
  let W := fun (mask : Kane.Cube n) ω => x+a • maskObservationSum ξ (Function.update mask i false) ω
  have hw (mask : Kane.Cube n) : Measurable (W mask) :=
    measurable_const.add (measurable_const.smul (measurable_maskObservationSum ξ h.measurable _))
  have he (mask : Kane.Cube n) := (integral_genericRow_commonPoint_identity μ μ hF hC h.delta_nonneg hjet
    (W mask) (hw mask) (ξ i) (h.measurable i) (h.bounded i) (h.centered i) q a c b d ha h2 h3).2
  change (∑ mask, Kane.maskWeight q mask*(∫ ω, genericRowOperator μ F (ξ i) (W mask ω) a c b ∂μ)) = _
  simp_rw [he]
  rw [generic_weighted_three]
  rw [sum_mask_genericBernoulliMoment_commonPoint μ ξ h hF (by decide) hC
      (hjet 2 (by decide) (by decide)) i x q a,
    sum_mask_genericBernoulliMoment_commonPoint μ ξ h hF (by decide) hC
      (hjet 3 (by decide) (by decide)) i x q a]
  rfl

theorem genericSelectorOperator_fourth_identity
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    {F : Vector p → ℝ} (hF : ContDiff ℝ 4 F) {C δ : ℝ} (hC : 0 ≤ C)
    (hjet : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ∀ x, ‖iteratedFDeriv ℝ k F x‖ ≤ C)
    (ξ : Fin n → Ω → Vector p) (h : BoundedIndependentHypotheses μ ξ δ)
    (A : Matrix (Fin p) (Fin p) ℝ) (hA : A*A.transpose = covariance μ (sumVector ξ))
    (x : Vector p) (q a c b d : ℝ) (ha : a ≠ 0)
    (h2 : c*a^2/2+b*a = -(1/2 : ℝ)) (h3 : c*a^3/6+b*a^2/2 = d) :
    genericSelectorOperator μ F ξ (A*A.transpose) x q a c b =
      d*genericCommonCubic μ F ξ x q a+genericSelectorFourthRemainder μ F ξ x q a c b d := by
  let V := genericFixedValue μ F ξ x a
  let G := fun i mask => genericFixedGradient μ F ξ x a i mask
  let R := fun i => ∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω,
    genericRowFourthTotal μ F (ξ i) (x+a • maskObservationSum ξ (Function.update mask i false) ω) q a c b d ∂μ)
  have hforced : genericSelectorOperator μ F ξ (A*A.transpose) x q a c b =
      (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω, genericRowOperator μ F (ξ i)
        (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ))+
      ∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask := by
    unfold genericSelectorOperator
    have he (i : Fin n) :
        (∑ mask : Kane.Cube n, Kane.maskWeight q mask*
          (c*(V (Function.update mask i true)-V (Function.update mask i false))+b*G i (Function.update mask i true))) =
        c*(∑ mask, Kane.maskWeight q mask*(V (Function.update mask i true)-V (Function.update mask i false)))+
        b*(∑ mask, Kane.maskWeight q mask*G i (Function.update mask i true)) := by
      simpa only [add_zero, mul_zero, Finset.sum_const_zero] using generic_weighted_three (Kane.maskWeight q)
        (fun mask => V (Function.update mask i true)-V (Function.update mask i false))
        (fun mask => G i (Function.update mask i true)) (fun _ => 0) c b
    calc
      _ = (∑ i, ∑ mask : Kane.Cube n, Kane.maskWeight q mask*
          (c*(V (Function.update mask i true)-V (Function.update mask i false))+b*G i (Function.update mask i true)))+
          ∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask := by
        simp_rw [he]
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ = _ := by
        congr 1
        apply Finset.sum_congr rfl
        intro i _
        apply Finset.sum_congr rfl
        intro mask _
        congr 1
        exact generic_forced_increment_eq_rowOperator μ hF hC hjet ξ h mask i x a c b
  have hone (i : Fin n) : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*(∫ ω,
      genericRowOperator μ F (ξ i) (x+a • maskObservationSum ξ (Function.update mask i false) ω) a c b ∂μ)) =
      -(1/2 : ℝ)*genericFullMoment μ F 2 ξ i x q a+d*genericFullMoment μ F 3 ξ i x q a+R i :=
    generic_row_mask_commonPoint_identity μ hF hC hjet ξ h i x q a c b d ha h2 h3
  have hheat : (∑ mask : Kane.Cube n, Kane.maskWeight q mask*genericFixedHeat μ F ξ (A*A.transpose) x a mask) =
      (1/2 : ℝ)*∑ i, genericFullMoment μ F 2 ξ i x q a := by
    simp_rw [genericFixedHeat_eq_half_sum_moments μ hF hC hjet ξ h A hA x a]
    unfold genericFullMoment
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro mask _
    ring
  rw [hforced]
  simp_rw [hone]
  rw [hheat, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [← Finset.mul_sum]
  change -(1/2 : ℝ)*(∑ i, genericFullMoment μ F 2 ξ i x q a)+
    d*(∑ i, genericFullMoment μ F 3 ξ i x q a)+(∑ i, R i)+
      (1/2 : ℝ)*(∑ i, genericFullMoment μ F 2 ξ i x q a) = _
  change _ = d*(∑ i, genericFullMoment μ F 3 ξ i x q a)+∑ i, R i
  ring

end
end RectangleCLT.Companion.SplitV4
