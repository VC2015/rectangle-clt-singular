import RectangleCLTArxivV1.SupplementalHCubicMatrix

/-! The one-dimensional projected reference for the cubic weights.
The positive-part factor is allowed to be unbounded. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem supplementalH_rankOne_mulVec {r : ℕ} (u g : Vector r) :
    (rankOne u).mulVec g = faceDot u g • u := by
  ext j
  change (∑ k, u j*u k*g k) = (∑ k, u k*g k)*u j
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem supplementalH_rankOne_transpose {r : ℕ} (u : Vector r) :
    (rankOne u).transpose=rankOne u := by
  ext j k
  change u k*u j=u j*u k
  ring

theorem supplementalH_rankOne_idempotent {r : ℕ} (u : Vector r) (hu : vectorNormSq u=1) :
    rankOne u*rankOne u=rankOne u := by
  ext j k
  change (∑ l, (u j*u l)*(u l*u k))=u j*u k
  calc
    _ = (u j*u k)*vectorNormSq u := by
      unfold vectorNormSq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    _ = _ := by rw [hu,mul_one]

theorem supplementalH_rankOne_coordinate {r : ℕ} (u g : Vector r) (hu : vectorNormSq u=1) :
    faceDot u ((rankOne u).mulVec g)=faceDot u g := by
  rw [supplementalH_rankOne_mulVec]
  change (∑ j, u j*((faceDot u g)*u j))=faceDot u g
  calc
    _ = faceDot u g*vectorNormSq u := by
      unfold vectorNormSq
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = _ := by rw [hu,mul_one]

theorem supplementalH_rankOne_normSq {r : ℕ} (u g : Vector r) (hu : vectorNormSq u=1) :
    vectorNormSq ((rankOne u).mulVec g)=(faceDot u g)^2 := by
  rw [supplementalH_rankOne_mulVec]
  calc
    _ = (faceDot u g)^2*vectorNormSq u := by
      unfold vectorNormSq
      simp only [Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
    _ = _ := by rw [hu,mul_one]

/-- The projected mean inequality for the actual first-face cubic
weight, with a genuine unbounded one-dimensional reference. -/
theorem supplementalH_cubic_mean_reference_bound {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ)
    (α : Fin (K+1) → Face p) (ha : ∀ i, α i ∈ s.faces)
    (hu : vectorNormSq (selectorFaceNormal A (α 0))=1) :
    supplementalHCubicMeanEnergy s (σ • A) v α (selectorFaceNormal A (α 0)) ≤
      (∫ g, (supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
        selectorWeight s α ((σ • A).mulVec g+v))*(faceDot (selectorFaceNormal A (α 0)) g)^2
        ∂standardGaussian r)+
      2*weightMass (standardGaussian r)
        (fun g => supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
          selectorWeight s α ((σ • A).mulVec g+v))*
        Real.log ((∫ g, supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
          oneFaceReference s (α 0) ((σ • A).mulVec g+v) ∂standardGaussian r)/
          weightMass (standardGaussian r)
            (fun g => supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
              selectorWeight s α ((σ • A).mulVec g+v))) := by
  let u := selectorFaceNormal A (α 0)
  let P := rankOne u
  let w := fun g => supplementalHPositiveDirection u g*selectorWeight s α ((σ • A).mulVec g+v)
  let β := fun x : Vector r => supplementalHPositiveDirection u x*
    oneFaceReferenceProfile s v σ (α 0) (faceDot u x)
  have hβm : Measurable β := by
    unfold β supplementalHPositiveDirection faceDot oneFaceReferenceProfile
    fun_prop
  have hβ0 (x : Vector r) : 0 ≤ β x := mul_nonneg
    (supplementalHPositiveDirection_nonneg u x) (oneFaceReferenceProfile_bounds s v σ (α 0) _).1
  have href (g : Vector r) : β (P.mulVec g)=supplementalHPositiveDirection u g*
      oneFaceReference s (α 0) ((σ • A).mulVec g+v) := by
    dsimp only [β,P,supplementalHPositiveDirection]
    rw [supplementalH_rankOne_coordinate u g hu]
    rw [oneFaceReferenceProfile_eq]
    simp only [Matrix.smul_mulVec_assoc]
  have hβi : Integrable (fun g => β (P.mulVec g)) (standardGaussian r) := by
    have hm : Measurable (fun g => β (P.mulVec g)) := by
      apply hβm.comp
      unfold P rankOne Matrix.mulVec dotProduct
      fun_prop
    apply (standardGaussian_integrable_faceDot u).abs.mono' hm.aestronglyMeasurable
    exact ae_of_all _ (fun g => by
      rw [href,Real.norm_eq_abs,abs_of_nonneg (mul_nonneg
        (supplementalHPositiveDirection_nonneg u g) (oneFaceReference_bounds s (α 0) _).1)]
      exact (mul_le_of_le_one_right (supplementalHPositiveDirection_nonneg u g)
        (oneFaceReference_bounds s (α 0) _).2).trans (max_le (le_abs_self _) (abs_nonneg _)))
  have hwi := supplementalH_positive_selector_moments s (σ • A) v α u
  have hwm : Measurable w := by
    apply Measurable.mul _ (continuous_selectorWeight_affine s α (σ • A) v).measurable
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hdom (g : Vector r) : 0 ≤ w g ∧ w g ≤ β (P.mulVec g) := by
    rw [href]
    exact ⟨mul_nonneg (supplementalHPositiveDirection_nonneg u g) (selectorWeight_nonneg s α _),
      mul_le_mul_of_nonneg_left (selectorWeight_le_oneFaceReference s α _) (supplementalHPositiveDirection_nonneg u g)⟩
  have hmean := lemma_H2_projected_reference P (supplementalH_rankOne_transpose u)
    (supplementalH_rankOne_idempotent u hu) β hβm hβ0 hβi w hwm hdom hwi.1 hwi.2
    (supplementalH_positive_selector_mass_pos s (σ • A) v α ha u hu)
  have hn (g : Vector r) : vectorNormSq (P.mulVec g)=(faceDot u g)^2 :=
    supplementalH_rankOne_normSq u g hu
  simp_rw [hn,href] at hmean
  simpa only [supplementalHCubicMeanEnergy,u,w,mul_assoc] using hmean

/-- Inactive selector factors vanish, so no active-face restriction is
needed when the actual cubic mean energies are summed over all tuples. -/
theorem supplementalH_cubic_mean_reference_bound_all {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ)
    (α : Fin (K+1) → Face p)
    (hu : vectorNormSq (selectorFaceNormal A (α 0))=1) :
    supplementalHCubicMeanEnergy s (σ • A) v α (selectorFaceNormal A (α 0)) ≤
      (∫ g, (supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
        selectorWeight s α ((σ • A).mulVec g+v))*(faceDot (selectorFaceNormal A (α 0)) g)^2
        ∂standardGaussian r)+
      2*weightMass (standardGaussian r)
        (fun g => supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
          selectorWeight s α ((σ • A).mulVec g+v))*
        Real.log ((∫ g, supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
          oneFaceReference s (α 0) ((σ • A).mulVec g+v) ∂standardGaussian r)/
          weightMass (standardGaussian r)
            (fun g => supplementalHPositiveDirection (selectorFaceNormal A (α 0)) g*
              selectorWeight s α ((σ • A).mulVec g+v))) := by
  classical
  by_cases ha : ∀ i, α i ∈ s.faces
  · exact supplementalH_cubic_mean_reference_bound s A v σ α ha hu
  · have hz (g : Vector r) : selectorWeight s α ((σ • A).mulVec g+v)=0 :=
      selectorWeight_eq_zero_of_not_active s α ha _
    simp only [supplementalHCubicMeanEnergy,weightMass,hz,mul_zero,zero_mul,
      integral_zero,zero_add]
    exact le_rfl


end
end RectangleCLTArxivV1
