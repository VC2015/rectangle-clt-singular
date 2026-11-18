import RectangleCLTArxivV1.GaussianRectangleIntrinsic
import RectangleCLT.CoordinateRescaling
import RectangleCLT.RectangleExtension
import RectangleCLT.GaussianComparisonLaw
import RectangleCLTCompanion.RectangleDistance

/-! Gaussian additions controlled by their actual expected maxima.
The reference law may be singular; only its coordinate variances are
bounded below. The perturbation is independent and its first norm moment
is an actual integral, not an assumed probability comparison. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable section

private theorem closedBox_outerSet {p : ℕ} (lo hi : Vector p) (d : ℝ) :
    (FaceSmoother.closedBox lo hi 1 (by norm_num)).outerSet d =
      (Rect.closedBox (fun j => lo j-d) (fun j => hi j+d)).carrier := by
  ext x
  simp only [FaceSmoother.outerSet, FaceSmoother.closedBox, Finset.mem_univ,
    forall_true_left, Set.mem_setOf_eq, Rect.carrier, Rect.closedBox,
    Set.mem_pi, Set.mem_univ, Set.mem_Icc]
  constructor
  · intro hx j
    have hl := hx (j, false)
    have hu := hx (j, true)
    simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] at hl hu
    constructor <;> linarith
  · intro hx f
    rcases f with ⟨j,b⟩
    cases b <;> simp only [FaceSmoother.normalDot, Bool.false_eq_true, ↓reduceIte] <;>
      linarith [(hx j).1, (hx j).2]

private theorem abs_probability_sub_le_of_sandwich
    {E : Type*} [MeasurableSpace E] (μ : Measure E) [IsFiniteMeasure μ]
    {I O S T : Set E} (hI : MeasurableSet I)
    (hIS : I ⊆ S) (hIT : I ⊆ T) (hSO : S ⊆ O) (hTO : T ⊆ O) :
    |μ.real S-μ.real T| ≤ μ.real (O\I) := by
  rw [measureReal_diff (hIS.trans hSO) hI]
  have h₁ := measureReal_mono (μ := μ) hIS
  have h₂ := measureReal_mono (μ := μ) hIT
  have h₃ := measureReal_mono (μ := μ) hSO
  have h₄ := measureReal_mono (μ := μ) hTO
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem shifted_closedBox_sandwich {p : ℕ} (lo hi b : Vector p) :
    (Rect.closedBox (fun j => lo j+‖b‖) (fun j => hi j-‖b‖)).carrier ⊆
        {x | x+b ∈ (Rect.closedBox lo hi).carrier} ∧
      {x | x+b ∈ (Rect.closedBox lo hi).carrier} ⊆
        (Rect.closedBox (fun j => lo j-‖b‖) (fun j => hi j+‖b‖)).carrier := by
  have hb (j : Fin p) : -‖b‖ ≤ b j ∧ b j ≤ ‖b‖ := by
    have h := norm_le_pi_norm b j
    simpa only [Real.norm_eq_abs, abs_le] using h
  constructor
  · intro x hx j hj
    have hh := hx j (Set.mem_univ j)
    change lo j+‖b‖ ≤ x j ∧ x j ≤ hi j-‖b‖ at hh
    change lo j ≤ x j+b j ∧ x j+b j ≤ hi j
    constructor <;> linarith [(hb j).1,(hb j).2]
  · intro x hx j hj
    have hh := hx j (Set.mem_univ j)
    change lo j ≤ x j+b j ∧ x j+b j ≤ hi j at hh
    change lo j-‖b‖ ≤ x j ∧ x j ≤ hi j+‖b‖
    constructor <;> linarith [(hb j).1,(hb j).2]

/-- The deterministic-shift step with the actual intrinsic Gaussian
coefficient. Every measurable coordinate interval convention is allowed. -/
theorem gaussian_rectangle_shift_common_variance {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, (A*A.transpose) j j = v) (b : Vector p) (R : Rect p) :
    rectangleError (gaussianLaw A) (fun x => x+b) A R ≤
      (2/v)*gaussianMaximumMean A*‖b‖ := by
  by_cases hb : b=0
  · simp [hb,rectangleError]
  apply rectangleError_le_of_closedBox hp (gaussianLaw A) (fun x => x+b)
    (measurable_id.add_const b) A
  intro lo hi
  let s := FaceSmoother.closedBox lo hi 1 (by norm_num)
  have hs : 0 < ‖b‖ := norm_pos_iff.mpr hb
  have hbounds := shifted_closedBox_sandwich lo hi b
  have hinner : (Rect.closedBox (fun j => lo j+‖b‖) (fun j => hi j-‖b‖)).carrier ⊆
      (Rect.closedBox lo hi).carrier := by
    intro x hx j hj
    have hh := hx j (Set.mem_univ j)
    change lo j+‖b‖ ≤ x j ∧ x j ≤ hi j-‖b‖ at hh
    change lo j ≤ x j ∧ x j ≤ hi j
    constructor <;> linarith [norm_nonneg b]
  have houter : (Rect.closedBox lo hi).carrier ⊆
      (Rect.closedBox (fun j => lo j-‖b‖) (fun j => hi j+‖b‖)).carrier := by
    intro x hx j hj
    have hh := hx j (Set.mem_univ j)
    change lo j ≤ x j ∧ x j ≤ hi j at hh
    change lo j-‖b‖ ≤ x j ∧ x j ≤ hi j+‖b‖
    constructor <;> linarith [norm_nonneg b]
  have hprob := abs_probability_sub_le_of_sandwich (gaussianLaw A)
    (Rect.measurableSet_carrier _) hbounds.1 hinner hbounds.2 houter
  have he : s.boundaryLayer ‖b‖ =
      (Rect.closedBox (fun j => lo j-‖b‖) (fun j => hi j+‖b‖)).carrier \
        (Rect.closedBox (fun j => lo j+‖b‖) (fun j => hi j-‖b‖)).carrier := by
    simp only [FaceSmoother.boundaryLayer,s,closedBox_outerSet,sub_neg_eq_add,sub_eq_add_neg,neg_neg]
  have hbound := gaussianRectangleBoundary_intrinsic_fixed_shift s A 0 hv hs hdiag
  simp only [add_zero] at hbound
  change |(gaussianLaw A).real {x | x+b ∈ (Rect.closedBox lo hi).carrier} -
    (gaussianLaw A).real (Rect.closedBox lo hi).carrier| ≤ _
  rw [← he] at hprob
  exact hprob.trans (hbound.trans_eq (by ring))

/-- Positive coordinate normalization controls the actual infinity norm. -/
theorem norm_scaleCoordinates_inv_le {p : ℕ} (σ x : Vector p) {a : ℝ}
    (ha : 0 < a) (hσ : ∀ j, a ≤ σ j) :
    ‖scaleCoordinates (fun j => (σ j)⁻¹) x‖ ≤ ‖x‖/a := by
  apply (pi_norm_le_iff_of_nonneg (div_nonneg (norm_nonneg x) ha.le)).mpr
  intro j
  have hσpos : 0 < σ j := ha.trans_le (hσ j)
  change ‖(σ j)⁻¹*x j‖ ≤ _
  rw [norm_mul,Real.norm_eq_abs,abs_inv,abs_of_pos hσpos,inv_mul_eq_div]
  exact (div_le_div_of_nonneg_right (norm_le_pi_norm x j) hσpos.le).trans
    (div_le_div_of_nonneg_left (norm_nonneg x) ha (hσ j))

/-- Row normalization retains the Gaussian expected maximum, with the
same pointwise infinity-norm bound used for the perturbing vector. -/
theorem gaussianMaximumMean_rowNormalize_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : Vector p) {a : ℝ}
    (ha : 0 < a) (hσ : ∀ j, a ≤ σ j) :
    gaussianMaximumMean (rowScaledFactor (fun j => (σ j)⁻¹) A) ≤
      gaussianMaximumMean A/a := by
  unfold gaussianMaximumMean
  rw [gaussianLaw_rowScaledFactor,
    integral_map (measurable_scaleCoordinates _).aemeasurable measurable_norm.aestronglyMeasurable]
  have hm : AEStronglyMeasurable
      (fun x : Vector p => ‖scaleCoordinates (fun j => (σ j)⁻¹) x‖) (gaussianLaw A) :=
    (measurable_norm.comp (measurable_scaleCoordinates _)).aestronglyMeasurable
  have hi : Integrable (fun x : Vector p => ‖scaleCoordinates (fun j => (σ j)⁻¹) x‖)
      (gaussianLaw A) :=
    ((gaussianLaw_integrable_norm A).div_const a).mono' hm
      (ae_of_all _ (fun x => by
        rw [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _)]
        exact norm_scaleCoordinates_inv_le σ x ha hσ))
  exact (integral_mono hi ((gaussianLaw_integrable_norm A).div_const a)
    (fun x => norm_scaleCoordinates_inv_le σ x ha hσ)).trans_eq (integral_div _ _)

/-- A lower bound on marginal variances suffices for the intrinsic
deterministic Gaussian shift bound. No inverse covariance is used. -/
theorem gaussian_rectangle_shift_min_variance {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, v ≤ (A*A.transpose) j j) (b : Vector p) (R : Rect p) :
    rectangleError (gaussianLaw A) (fun x => x+b) A R ≤
      (2/v)*gaussianMaximumMean A*‖b‖ := by
  let σ : Vector p := fun j => Real.sqrt ((A*A.transpose) j j)
  have hs : 0 < Real.sqrt v := Real.sqrt_pos.mpr hv
  have hσ (j : Fin p) : Real.sqrt v ≤ σ j := Real.sqrt_le_sqrt (hdiag j)
  have hσpos (j : Fin p) : 0 < σ j := hs.trans_le (hσ j)
  let D := rowScaledFactor (fun j => (σ j)⁻¹) A
  have hunit (j : Fin p) : (D*D.transpose) j j = 1 := by
    rw [rowScaledFactor_covariance]
    have he : σ j ^ 2 = (A*A.transpose) j j :=
      Real.sq_sqrt (hv.le.trans (hdiag j))
    rw [← he]
    field_simp [(hσpos j).ne']; ring
  have hnormalized := gaussian_rectangle_shift_common_variance hp D (by norm_num : (0:ℝ)<1)
    hunit (scaleCoordinates (fun j => (σ j)⁻¹) b) (R.preimageCoordinateScale σ hσpos)
  have he : rectangleError (gaussianLaw A) (fun x => x+b) A R =
      rectangleError (gaussianLaw D) (fun x => x+scaleCoordinates (fun j => (σ j)⁻¹) b)
        D (R.preimageCoordinateScale σ hσpos) := by
    rw [rectangleError_coordinateNormalize (gaussianLaw A) (fun x => x+b) A σ hσpos R]
    unfold rectangleError
    rw [gaussianLaw_rowScaledFactor]
    have hmap := map_measureReal_apply (μ := gaussianLaw A)
      (measurable_scaleCoordinates (fun j => (σ j)⁻¹))
      ((R.preimageCoordinateScale σ hσpos).measurableSet_carrier.preimage
        (measurable_id.add_const (scaleCoordinates (fun j => (σ j)⁻¹) b)))
    simp only [id_eq] at hmap
    rw [hmap]
    have hsets : (fun x => scaleCoordinates (fun j => (σ j)⁻¹) (x+b)) ⁻¹'
        (R.preimageCoordinateScale σ hσpos).carrier =
        (scaleCoordinates (fun j => (σ j)⁻¹)) ⁻¹'
          ((fun x => x+scaleCoordinates (fun j => (σ j)⁻¹) b) ⁻¹'
            (R.preimageCoordinateScale σ hσpos).carrier) := by
      ext x
      simp only [Set.mem_preimage]
      have hadd : scaleCoordinates (fun j => (σ j)⁻¹) (x+b) =
          scaleCoordinates (fun j => (σ j)⁻¹) x+scaleCoordinates (fun j => (σ j)⁻¹) b := by
        ext j
        simp only [scaleCoordinates,Pi.add_apply,mul_add]
      rw [hadd]
    rw [hsets]
  rw [he]
  apply hnormalized.trans
  have hg := gaussianMaximumMean_rowNormalize_le A σ hs hσ
  have hb := norm_scaleCoordinates_inv_le σ b hs hσ
  dsimp only [D] at hg ⊢
  have hb0 : 0 ≤ gaussianMaximumMean A := gaussianMaximumMean_nonneg A
  have hbb : 0 ≤ ‖scaleCoordinates (fun j => (σ j)⁻¹) b‖ := norm_nonneg _
  have hh := mul_le_mul hg hb hbb (div_nonneg hb0 hs.le)
  norm_num only [div_one] at hnormalized ⊢
  calc
    _ ≤ 2*(gaussianMaximumMean A/Real.sqrt v*(‖b‖/Real.sqrt v)) := by nlinarith [hh]
    _ = _ := by
      rw [div_mul_div_comm,←pow_two,Real.sq_sqrt hv.le]
      ring

/-- Conditioning on the perturbation integrates the proved deterministic
Gaussian shift comparison. Independence is represented by the actual
product law; only its genuine first norm moment is required. -/
theorem independent_add_rectangleDistance_intrinsic
    {E : Type*} [MeasurableSpace E] {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (τ : Measure E) [IsProbabilityMeasure τ]
    (R : E → Vector p) (hR : Measurable R)
    (hiR : Integrable (fun e => ‖R e‖) τ)
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, v ≤ (A*A.transpose) j j) :
    rectangleDistance ((gaussianLaw A).prod τ) (fun z => z.1+R z.2) A ≤
      (2/v)*gaussianMaximumMean A*(∫ e, ‖R e‖ ∂τ) := by
  apply rectangleDistance_le
  intro Q
  let S : Set (Vector p × E) := {z | z.1+R z.2 ∈ Q.carrier}
  have hS : MeasurableSet S := Q.measurableSet_carrier.preimage
    (measurable_fst.add (hR.comp measurable_snd))
  let I : Vector p × E → ℝ := S.indicator (fun _ => 1)
  have hiI : Integrable I ((gaussianLaw A).prod τ) := (integrable_const (1:ℝ)).indicator hS
  have hfixed (e : E) : (∫ x, I (x,e) ∂gaussianLaw A) =
      (gaussianLaw A).real {x | x+R e ∈ Q.carrier} := by
    change (∫ x, {x | x+R e ∈ Q.carrier}.indicator (fun _ => (1:ℝ)) x ∂gaussianLaw A) = _
    exact integral_indicator_one (Q.measurableSet_carrier.preimage (measurable_id.add_const _))
  have hprod : ((gaussianLaw A).prod τ).real S =
      ∫ e, ∫ x, I (x,e) ∂gaussianLaw A ∂τ := by
    rw [← integral_indicator_one hS]
    exact integral_prod_symm I hiI
  let c := (gaussianLaw A).real Q.carrier
  have he : (∫ e, ((∫ x, I (x,e) ∂gaussianLaw A)-c) ∂τ) =
      ((gaussianLaw A).prod τ).real S-c := by
    rw [integral_sub hiI.integral_prod_right (integrable_const c),←hprod]
    simp only [integral_const,measureReal_univ_eq_one,one_smul]
  change |((gaussianLaw A).prod τ).real S-c| ≤ _
  rw [←he]
  apply abs_integral_le_integral_abs.trans
  apply (integral_mono (hiI.integral_prod_right.sub (integrable_const c)).abs
    (hiR.const_mul ((2/v)*gaussianMaximumMean A)) ?_).trans_eq (integral_const_mul _ _)
  intro e
  change |(∫ x, I (x,e) ∂gaussianLaw A)-c| ≤ (2/v)*gaussianMaximumMean A*‖R e‖
  rw [hfixed]
  exact gaussian_rectangle_shift_min_variance hp A hv hdiag (R e) Q

/-- The intrinsic addition comparison for two actual independent Gaussian
laws. Singular perturbation covariance, including the zero law, is allowed. -/
theorem gaussian_addition_rectangleDistance_le {p : ℕ} (hp : 1 ≤ p)
    (A B : Matrix (Fin p) (Fin p) ℝ) {v : ℝ} (hv : 0 < v)
    (hdiag : ∀ j, v ≤ (A*A.transpose) j j) :
    rectangleDistance ((gaussianLaw A).prod (gaussianLaw B)) (fun z => z.1+z.2) A ≤
      (2/v)*gaussianMaximumMean A*gaussianMaximumMean B :=
  independent_add_rectangleDistance_intrinsic hp A (gaussianLaw B) id measurable_id
    (gaussianLaw_integrable_norm B) hv hdiag

/-- Two independent Gaussian additions with the same summed covariance
have exactly the same law, including singular covariance matrices. -/
theorem gaussian_addition_law_eq_of_covariance_sum {p : ℕ}
    (A D B H : Matrix (Fin p) (Fin p) ℝ)
    (hcov : A*A.transpose+D*D.transpose = B*B.transpose+H*H.transpose) :
    ((gaussianLaw A).prod (gaussianLaw D)).map (fun z => z.1+z.2) =
      ((gaussianLaw B).prod (gaussianLaw H)).map (fun z => z.1+z.2) := by
  have hfun : gaussianScaledSum (p := p) 1 1 = (fun z => z.1+z.2) := by
    funext z
    simp only [gaussianScaledSum,one_smul]
  rw [←hfun]
  apply measure_eq_of_vectorFourier_eq
  intro t
  rw [vectorFourier_gaussianScaledSum,vectorFourier_gaussianScaledSum]
  simp only [one_pow,one_smul,hcov]

/-- A covariance factor identifies the Gaussian addition in the
comparison inequality. The factor equality is an exact law identity. -/
theorem gaussian_addition_factor_rectangleDistance_le {p : ℕ} (hp : 1 ≤ p)
    (A B C : Matrix (Fin p) (Fin p) ℝ)
    (hcov : C*C.transpose = A*A.transpose+B*B.transpose)
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, v ≤ (A*A.transpose) j j) :
    rectangleDistance (gaussianLaw C) id A ≤
      (2/v)*gaussianMaximumMean A*gaussianMaximumMean B := by
  have hlaw : ((gaussianLaw A).prod (gaussianLaw B)).map (fun z => z.1+z.2) =
      gaussianLaw C := by
    have h := gaussianLaw_scaled_sum A B C 1 1 (by simpa only [one_pow,one_smul] using hcov)
    have hfun : gaussianScaledSum (p := p) 1 1 = (fun z => z.1+z.2) := by
      funext z
      simp only [gaussianScaledSum,one_smul]
    rw [hfun] at h
    exact h
  apply rectangleDistance_le
  intro R
  have he : rectangleError (gaussianLaw C) id A R =
      rectangleError ((gaussianLaw A).prod (gaussianLaw B)) (fun z => z.1+z.2) A R := by
    unfold rectangleError
    rw [←hlaw,Set.preimage_id,map_measureReal_apply (measurable_fst.add measurable_snd)
      R.measurableSet_carrier]
  rw [he]
  exact (rectangleError_le_rectangleDistance _ _ _ R).trans
    (gaussian_addition_rectangleDistance_le hp A B hv hdiag)

/-- The genuine rectangle distance satisfies the triangle inequality
through an intermediate concrete Gaussian law. -/
theorem rectangleDistance_gaussian_triangle
    {E : Type*} [MeasurableSpace E] {p : ℕ}
    (μ : Measure E) [IsProbabilityMeasure μ] (W : E → Vector p)
    (A B : Matrix (Fin p) (Fin p) ℝ) :
    rectangleDistance μ W B ≤ rectangleDistance μ W A+rectangleDistance (gaussianLaw A) id B := by
  apply rectangleDistance_le
  intro R
  have ha := rectangleError_le_rectangleDistance μ W A R
  have hb := rectangleError_le_rectangleDistance (gaussianLaw A) id B R
  unfold rectangleError at ha hb ⊢
  simp only [Set.preimage_id] at hb
  exact (abs_sub_le _ ((gaussianLaw A).real R.carrier) _).trans (add_le_add ha hb)

/-- The two Gaussian additions used in the second covariance comparison
of Appendix E.1. All four factors are actual Gaussian laws; neither
comparison uses an inverse covariance or a dimension-only boundary bound. -/
theorem gaussian_two_additions_rectangleDistance_le {p : ℕ} (hp : 1 ≤ p)
    (A D B H : Matrix (Fin p) (Fin p) ℝ)
    (hcov : A*A.transpose+D*D.transpose = B*B.transpose+H*H.transpose)
    {vA vB : ℝ} (hvA : 0 < vA) (hvB : 0 < vB)
    (hdiagA : ∀ j, vA ≤ (A*A.transpose) j j)
    (hdiagB : ∀ j, vB ≤ (B*B.transpose) j j) :
    rectangleDistance (gaussianLaw A) id B ≤
      (2/vA)*gaussianMaximumMean A*gaussianMaximumMean D+
        (2/vB)*gaussianMaximumMean B*gaussianMaximumMean H := by
  apply rectangleDistance_le
  intro R
  have ha := (rectangleError_le_rectangleDistance _ _ _ R).trans
    (gaussian_addition_rectangleDistance_le hp A D hvA hdiagA)
  have hb := (rectangleError_le_rectangleDistance _ _ _ R).trans
    (gaussian_addition_rectangleDistance_le hp B H hvB hdiagB)
  have heq := congrArg (fun μ : Measure (Vector p) => μ.real R.carrier)
    (gaussian_addition_law_eq_of_covariance_sum A D B H hcov)
  dsimp only at heq
  rw [map_measureReal_apply (measurable_fst.add measurable_snd) R.measurableSet_carrier,
    map_measureReal_apply (measurable_fst.add measurable_snd) R.measurableSet_carrier] at heq
  unfold rectangleError at ha hb ⊢
  simp only [Set.preimage_id]
  rw [←abs_sub_comm] at ha
  calc
    _ = |((gaussianLaw A).real R.carrier-
        ((gaussianLaw A).prod (gaussianLaw D)).real ((fun z => z.1+z.2) ⁻¹' R.carrier))+
        (((gaussianLaw B).prod (gaussianLaw H)).real ((fun z => z.1+z.2) ⁻¹' R.carrier)-
          (gaussianLaw B).real R.carrier)| := by rw [heq]; congr 1; ring
    _ ≤ _ := (abs_add _ _).trans (add_le_add ha hb)

end
end RectangleCLTArxivV1
