import RectangleCLT.BernoulliPath
import RectangleCLT.Normalization

/-! Mixed moments under the actual Bernoulli-thinned array law. These are
identities of integrals against the finite-mixture probability law, rather
than assumptions about an interpolating random vector. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

universe u

namespace RectangleCLT

/-- A homogeneous product of coordinates of one observation in an array. -/
def arrayCoordinateProduct {p n r : ℕ} (i : Fin n) (J : Fin r → Fin p)
    (a : Fin n → Vector p) : ℝ := ∏ k, a i (J k)

theorem measurable_arrayCoordinateProduct {p n r : ℕ} (i : Fin n) (J : Fin r → Fin p) :
    Measurable (arrayCoordinateProduct i J) := by
  exact Finset.measurable_prod Finset.univ fun k _ =>
    (measurable_pi_apply (J k)).comp (measurable_pi_apply i)

theorem retainedArray_coordinateProduct {Ω : Type u} {p n r : ℕ}
    (ξ : Fin n → Ω → Vector p) (t : ℝ) (mask : Kane.Cube n) (ω : Ω)
    (i : Fin n) (J : Fin r → Fin p) (hr : 0 < r) :
    arrayCoordinateProduct i J (retainedArray ξ t mask ω) =
      Kane.boolVal (mask i) * thinningScale t ^ r * (∏ k, ξ i ω (J k)) := by
  by_cases hi : mask i = true
  · simp [arrayCoordinateProduct, retainedArray, hi, Kane.boolVal,
      Pi.smul_apply, smul_eq_mul, Finset.prod_mul_distrib]
  · simp [arrayCoordinateProduct, retainedArray, hi, Kane.boolVal,
      Finset.prod_const, zero_pow (Nat.ne_of_gt hr)]

/-- Any positive-degree mixed moment of one retained observation has its
exact Bernoulli factor `q * scale^r` under the actual array law. -/
theorem integral_bernoulliArrayLaw_coordinateProduct
    {Ω : Type u} [MeasurableSpace Ω] {p n r : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) (J : Fin r → Fin p)
    (hr : 0 < r) (hprod : Integrable (fun ω => ∏ k, ξ i ω (J k)) μ) :
    (∫ a, arrayCoordinateProduct i J a ∂bernoulliArrayLaw μ ξ t) =
      thinningProbability t * thinningScale t ^ r * ∫ ω, ∏ k, ξ i ω (J k) ∂μ := by
  have hg := measurable_arrayCoordinateProduct i J
  have hF := measurable_retainedArray ξ hξ t
  have hint (mask : Kane.Cube n) :
      Integrable (arrayCoordinateProduct i J) (μ.map (retainedArray ξ t mask)) := by
    apply (integrable_map_measure hg.aestronglyMeasurable (hF mask).aemeasurable).mpr
    change Integrable (fun ω => arrayCoordinateProduct i J (retainedArray ξ t mask ω)) μ
    simp_rw [retainedArray_coordinateProduct ξ t mask _ i J hr]
    exact hprod.const_mul _
  unfold bernoulliArrayLaw
  rw [integral_bernoulliMixtureLaw μ (retainedArray ξ t) _
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _ hint]
  have hmap (mask : Kane.Cube n) :
      (∫ a, arrayCoordinateProduct i J a ∂μ.map (retainedArray ξ t mask)) =
        Kane.boolVal (mask i) * thinningScale t ^ r * ∫ ω, ∏ k, ξ i ω (J k) ∂μ := by
    rw [integral_map (hF mask).aemeasurable hg.aestronglyMeasurable]
    simp_rw [retainedArray_coordinateProduct ξ t mask _ i J hr]
    rw [integral_const_mul]
  simp_rw [hmap]
  calc
    _ = (∑ mask : Kane.Cube n, Kane.maskWeight (thinningProbability t) mask *
        Kane.boolVal (mask i)) *
          (thinningScale t ^ r * ∫ ω, ∏ k, ξ i ω (J k) ∂μ) := by
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro mask _
      ring
    _ = _ := by rw [maskWeight_coordinate]; ring

/-- The first moment under the actual thinned array law. -/
theorem integral_bernoulliArrayLaw_coordinate
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) (j : Fin p)
    (hint : Integrable (fun ω => ξ i ω j) μ) :
    (∫ a, a i j ∂bernoulliArrayLaw μ ξ t) =
      thinningProbability t * thinningScale t * ∫ ω, ξ i ω j ∂μ := by
  simpa only [arrayCoordinateProduct, Fin.prod_univ_one, pow_one] using
    integral_bernoulliArrayLaw_coordinateProduct μ ξ hξ t ht ht1 i
      (fun _ : Fin 1 => j) (by decide) (by simpa only [Fin.prod_univ_one] using hint)

/-- The second mixed moment of a single retained observation. -/
theorem integral_bernoulliArrayLaw_coordinate_mul
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) (j k : Fin p)
    (hint : Integrable (fun ω => ξ i ω j * ξ i ω k) μ) :
    (∫ a, a i j * a i k ∂bernoulliArrayLaw μ ξ t) =
      (1 - t) * ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
  have hh := integral_bernoulliArrayLaw_coordinateProduct μ ξ hξ t ht ht1 i
    (![j, k] : Fin 2 → Fin p) (by decide)
    (by simpa [Fin.prod_univ_succ] using hint)
  simpa [arrayCoordinateProduct, Fin.prod_univ_succ, thinning_covariance ht] using hh

/-- The third mixed moment of a single retained observation. -/
theorem integral_bernoulliArrayLaw_coordinate_triple
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i : Fin n) (j k l : Fin p)
    (hint : Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) μ) :
    (∫ a, a i j * a i k * a i l ∂bernoulliArrayLaw μ ξ t) =
      (1 - t ^ 2) * ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ := by
  have hh := integral_bernoulliArrayLaw_coordinateProduct μ ξ hξ t ht ht1 i
    (![j, k, l] : Fin 3 → Fin p) (by decide)
    (by simpa [Fin.prod_univ_succ, mul_assoc] using hint)
  simpa [arrayCoordinateProduct, Fin.prod_univ_succ, mul_assoc,
    thinning_third_moment ht] using hh

/-- Original centering is preserved by the actual Bernoulli-array law. -/
theorem bernoulliArrayLaw_centered
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (hint : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) :
    ∀ i j, (∫ a, a i j ∂bernoulliArrayLaw μ ξ t) = 0 := by
  intro i j
  rw [integral_bernoulliArrayLaw_coordinate μ ξ hξ t ht ht1 i j (hint i j), hcenter i j]
  ring

/-- Integrability passes from every pushforward component to the finite
Bernoulli mixture. Zero selector weights need no exceptional convention. -/
theorem integrable_bernoulliMixtureLaw
    {Ω : Type u} [MeasurableSpace Ω] {E : Type*} [MeasurableSpace E] {n : ℕ}
    (μ : Measure Ω) (F : Kane.Cube n → Ω → E) (q : ℝ) (g : E → ℝ)
    (hg : ∀ mask, Integrable g (μ.map (F mask))) :
    Integrable g (bernoulliMixtureLaw μ F q) := by
  unfold bernoulliMixtureLaw
  apply integrable_finset_sum_measure.mpr
  intro mask _
  exact (hg mask).smul_measure ENNReal.ofReal_ne_top

theorem integrable_bernoulliArrayLaw_coordinateProduct
    {Ω : Type u} [MeasurableSpace Ω] {p n r : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (i : Fin n) (J : Fin r → Fin p) (hr : 0 < r)
    (hprod : Integrable (fun ω => ∏ k, ξ i ω (J k)) μ) :
    Integrable (arrayCoordinateProduct i J) (bernoulliArrayLaw μ ξ t) := by
  apply integrable_bernoulliMixtureLaw
  intro mask
  apply (integrable_map_measure (measurable_arrayCoordinateProduct i J).aestronglyMeasurable
    (measurable_retainedArray ξ hξ t mask).aemeasurable).mpr
  change Integrable (fun ω => arrayCoordinateProduct i J (retainedArray ξ t mask ω)) μ
  simp_rw [retainedArray_coordinateProduct ξ t mask _ i J hr]
  exact hprod.const_mul _

private theorem retainedArray_cross {Ω : Type u} {p n : ℕ}
    (ξ : Fin n → Ω → Vector p) (t : ℝ) (mask : Kane.Cube n) (ω : Ω)
    (i l : Fin n) (j k : Fin p) :
    retainedArray ξ t mask ω i j * retainedArray ξ t mask ω l k =
      (Kane.boolVal (mask i) * Kane.boolVal (mask l) * thinningScale t ^ 2) *
        (ξ i ω j * ξ l ω k) := by
  by_cases hi : mask i = true <;> by_cases hl : mask l = true <;>
    simp [retainedArray, hi, hl, Kane.boolVal, Pi.smul_apply, smul_eq_mul,
      pow_two, mul_assoc, mul_left_comm, mul_comm]

private theorem measurable_array_cross {p n : ℕ} (i l : Fin n) (j k : Fin p) :
    Measurable (fun a : Fin n → Vector p => a i j * a l k) :=
  ((measurable_pi_apply j).comp (measurable_pi_apply i)).mul
    ((measurable_pi_apply k).comp (measurable_pi_apply l))

private theorem integrable_map_retained_cross
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (i l : Fin n) (j k : Fin p)
    (hint : Integrable (fun ω => ξ i ω j * ξ l ω k) μ) (mask : Kane.Cube n) :
    Integrable (fun a : Fin n → Vector p => a i j * a l k)
      (μ.map (retainedArray ξ t mask)) := by
  apply (integrable_map_measure (measurable_array_cross i l j k).aestronglyMeasurable
    (measurable_retainedArray ξ hξ t mask).aemeasurable).mpr
  change Integrable (fun ω => retainedArray ξ t mask ω i j * retainedArray ξ t mask ω l k) μ
  simp_rw [retainedArray_cross]
  exact hint.const_mul _

/-- Integrability of cross-observation second moments under the array law
does not require independence of the thinned observations as an assumption. -/
theorem integrable_bernoulliArrayLaw_cross
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (i l : Fin n) (j k : Fin p)
    (hint : Integrable (fun ω => ξ i ω j * ξ l ω k) μ) :
    Integrable (fun a => a i j * a l k) (bernoulliArrayLaw μ ξ t) :=
  integrable_bernoulliMixtureLaw μ (retainedArray ξ t) _ _
    (integrable_map_retained_cross μ ξ hξ t i l j k hint)

/-- A zero original cross moment stays zero under the actual array law. -/
theorem integral_bernoulliArrayLaw_cross_zero
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (i l : Fin n) (j k : Fin p)
    (hint : Integrable (fun ω => ξ i ω j * ξ l ω k) μ)
    (hzero : (∫ ω, ξ i ω j * ξ l ω k ∂μ) = 0) :
    (∫ a, a i j * a l k ∂bernoulliArrayLaw μ ξ t) = 0 := by
  unfold bernoulliArrayLaw
  rw [integral_bernoulliMixtureLaw μ (retainedArray ξ t) _
    (thinningProbability_nonneg ht1) (thinningProbability_le_one ht) _
    (integrable_map_retained_cross μ ξ hξ t i l j k hint)]
  have hmap (mask : Kane.Cube n) :
      (∫ a, a i j * a l k ∂μ.map (retainedArray ξ t mask)) = 0 := by
    rw [integral_map (measurable_retainedArray ξ hξ t mask).aemeasurable
      (measurable_array_cross i l j k).aestronglyMeasurable]
    simp_rw [retainedArray_cross]
    rw [integral_const_mul, hzero, mul_zero]
  simp_rw [hmap, mul_zero]
  exact Finset.sum_const_zero

/-- Expand the covariance of an actual sum when all observations are centered
and cross-observation mixed moments vanish. -/
theorem covariance_sum_of_centered_cross
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p}
    (hint : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (hprod : ∀ i l j k, Integrable (fun ω => ξ i ω j * ξ l ω k) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (hcross : ∀ i l, i ≠ l → ∀ j k, (∫ ω, ξ i ω j * ξ l ω k ∂μ) = 0)
    (j k : Fin p) :
    covariance μ (sumVector ξ) j k = ∑ i, ∫ ω, ξ i ω j * ξ i ω k ∂μ := by
  have hmean (j : Fin p) : (∫ ω, sumVector ξ ω j ∂μ) = 0 := by
    simp only [sumVector, Finset.sum_apply]
    rw [integral_finset_sum Finset.univ (fun i _ => hint i j)]
    simp_rw [hcenter]
    exact Finset.sum_const_zero
  unfold covariance
  rw [hmean, hmean, mul_zero, sub_zero]
  calc
    _ = ∫ ω, ∑ i, ∑ l, ξ i ω j * ξ l ω k ∂μ := by
      apply integral_congr_ae
      filter_upwards [] with ω
      simp only [sumVector, Finset.sum_apply, Finset.sum_mul, Finset.mul_sum]
      exact Finset.sum_comm
    _ = ∑ i, ∑ l, ∫ ω, ξ i ω j * ξ l ω k ∂μ := by
      rw [integral_finset_sum Finset.univ (fun i _ =>
        integrable_finset_sum Finset.univ (fun l _ => hprod i l j k))]
      apply Finset.sum_congr rfl
      intro i _
      exact integral_finset_sum Finset.univ (fun l _ => hprod i l j k)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_eq_single i]
      · intro l _ hli
        exact hcross i l (Ne.symm hli) j k
      · simp

/-- Independent centered original observations supply the cross-moment
vanishing needed for the deterministic covariance expansion. -/
theorem independent_centered_cross_zero
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ} {μ : Measure Ω}
    {ξ : Fin n → Ω → Vector p}
    (hind : iIndepFun ξ μ) (hint : ∀ i j, Integrable (fun ω => ξ i ω j) μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (i l : Fin n) (hil : i ≠ l) (j k : Fin p) :
    (∫ ω, ξ i ω j * ξ l ω k ∂μ) = 0 := by
  have hi := (hind.indepFun hil).comp (measurable_pi_apply j) (measurable_pi_apply k)
  have hh := hi.integral_mul_of_integrable (hint i j) (hint l k)
  change (∫ ω, ξ i ω j * ξ l ω k ∂μ) =
    (∫ ω, ξ i ω j ∂μ) * (∫ ω, ξ l ω k ∂μ) at hh
  simpa only [hcenter, zero_mul] using hh

/-- The actual Bernoulli-thinned sum has covariance `(1-t)` times the original
sum covariance. Independence is required only for the original observations;
the conclusion is proved by integrating the finite selector mixture. -/
theorem bernoulliArrayLaw_sum_covariance
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hLp : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    covariance (bernoulliArrayLaw μ ξ t) (fun a => ∑ i, a i) =
      (1 - t) • covariance μ (sumVector ξ) := by
  have hInt (i : Fin n) (j : Fin p) : Integrable (fun ω => ξ i ω j) μ :=
    (hLp i j).integrable (by norm_num)
  have hProd (i l : Fin n) (j k : Fin p) :
      Integrable (fun ω => ξ i ω j * ξ l ω k) μ :=
    (hLp i j).integrable_mul (hLp l k)
  have hnewInt (i : Fin n) (j : Fin p) :
      Integrable (fun a : Fin n → Vector p => a i j) (bernoulliArrayLaw μ ξ t) := by
    have hp := integrable_bernoulliArrayLaw_coordinateProduct μ ξ hξ t i (fun _ : Fin 1 => j)
      (by decide) (by simpa only [Fin.prod_univ_one] using hInt i j)
    have heq : arrayCoordinateProduct i (fun _ : Fin 1 => j) =
        (fun a : Fin n → Vector p => a i j) := by
      funext a
      simp [arrayCoordinateProduct]
    rwa [heq] at hp
  have hnewProd (i l : Fin n) (j k : Fin p) :=
    integrable_bernoulliArrayLaw_cross μ ξ hξ t i l j k (hProd i l j k)
  have hnewCenter := bernoulliArrayLaw_centered μ ξ hξ t ht ht1 hInt hcenter
  have hcross := independent_centered_cross_zero hind hInt hcenter
  have hnewCross (i l : Fin n) (hil : i ≠ l) (j k : Fin p) :
      (∫ a, a i j * a l k ∂bernoulliArrayLaw μ ξ t) = 0 :=
    integral_bernoulliArrayLaw_cross_zero μ ξ hξ t ht ht1 i l j k
      (hProd i l j k) (hcross i l hil j k)
  ext j k
  change covariance (bernoulliArrayLaw μ ξ t) (sumVector (fun i a => a i)) j k = _
  rw [covariance_sum_of_centered_cross hnewInt hnewProd hnewCenter hnewCross j k]
  change _ = (1 - t) * covariance μ (sumVector ξ) j k
  rw [covariance_sum_of_centered_cross hInt hProd hcenter hcross j k]
  have hm (i : Fin n) :=
    integral_bernoulliArrayLaw_coordinate_mul μ ξ hξ t ht ht1 i j k (hProd i i j k)
  simp_rw [hm]
  exact (Finset.mul_sum _ _ _).symm

/-- The signed aggregate third-moment tensor receives a single common factor.
Cancellation between the original observations is therefore preserved. -/
theorem bernoulliArrayLaw_aggregate_third_moment
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) (j k l : Fin p)
    (hint : ∀ i, Integrable (fun ω => ξ i ω j * ξ i ω k * ξ i ω l) μ) :
    (∑ i, ∫ a, a i j * a i k * a i l ∂bernoulliArrayLaw μ ξ t) =
      (1 - t ^ 2) * ∑ i, ∫ ω, ξ i ω j * ξ i ω k * ξ i ω l ∂μ := by
  simp_rw [integral_bernoulliArrayLaw_coordinate_triple μ ξ hξ t ht ht1 _ j k l (hint _)]
  exact (Finset.mul_sum _ _ _).symm

/-- The covariance path identity under only bounded measurable independent
centered original observations; no global spectral lower bound is used. -/
theorem bernoulliArrayLaw_sum_covariance_of_bounded
    {Ω : Type u} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsFiniteMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (hcenter : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) {δ : ℝ}
    (hbound : ∀ i j, ∀ᵐ ω ∂μ, |ξ i ω j| ≤ δ)
    (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    covariance (bernoulliArrayLaw μ ξ t) (fun a => ∑ i, a i) =
      (1 - t) • covariance μ (sumVector ξ) := by
  apply bernoulliArrayLaw_sum_covariance μ ξ hξ hind _ hcenter t ht ht1
  intro i j
  apply MemLp.of_bound (((measurable_pi_apply j).comp (hξ i)).aestronglyMeasurable) δ
  simpa only [Real.norm_eq_abs] using hbound i j

end RectangleCLT
