import RectangleCLTCompanion.SignedSurfaceBoundary

/-! Gaussian Gauss–Green on an actual affine hyperplane section, for
bounded C1 tests with bounded derivative. This proves the analytic identity
before taking hard polyhedral boundary limits; no surface estimate is a
premise. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion.SignedSurface
open scoped BigOperators
noncomputable section

/-- Coordinate tangent vectors of the orthogonal projection. -/
def gaussianSectionTangent {r : ℕ} (u : Vector r) (j : Fin r) : Vector r :=
  Pi.single j 1-u j • u

theorem sum_smul_gaussianSectionTangent {r : ℕ} (u x : Vector r) :
    (∑ j, x j • gaussianSectionTangent u j)=gaussianSectionResidual u x := by
  classical
  ext k
  simp [gaussianSectionTangent,gaussianSectionResidual,faceDot,Pi.single_apply,
    mul_sub,Finset.sum_sub_distrib,Finset.sum_mul,Finset.mul_sum,Finset.sum_ite_eq,Finset.sum_ite_eq',
    mul_comm,mul_left_comm,mul_assoc]

theorem sum_self_smul_gaussianSectionTangent {r : ℕ} (u : Vector r)
    (hu : vectorNormSq u=1) : (∑ j, u j • gaussianSectionTangent u j)=0 := by
  rw [sum_smul_gaussianSectionTangent]
  have hh : faceDot u u=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hu
  simp only [gaussianSectionResidual,hh,one_smul,sub_self]

theorem gaussianSectionPoint_update {r : ℕ} (u x : Vector r) (b t : ℝ) (j : Fin r) :
    gaussianSectionPoint u b (Function.update x j t)=
      gaussianSectionPoint u b x+(t-x j) • gaussianSectionTangent u j := by
  classical
  have hupdate : Function.update x j t = x+(t-x j) • (Pi.single j (1:ℝ) : Vector r) := by
    ext k
    by_cases hk : k=j
    · subst k
      simp
    · simp [Function.update_of_ne hk,Pi.single_apply,hk,Ne.symm hk]
  have hdot : faceDot u (Function.update x j t)=faceDot u x+(t-x j)*u j := by
    rw [hupdate]
    simp only [faceDot,Pi.add_apply,Pi.smul_apply,Pi.single_apply,smul_eq_mul,
      mul_add,Finset.sum_add_distrib,mul_ite,mul_zero,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true,eq_comm]
    ring
  ext k
  simp only [gaussianSectionPoint,gaussianSectionResidual,gaussianSectionTangent,
    Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,hdot]
  by_cases hk : k=j
  · subst k
    simp
    ring
  · simp only [Function.update_of_ne hk,Pi.single_apply,if_neg hk,if_neg (Ne.symm hk)]
    ring

/-- Chain rule along the actual tangent coordinate of the affine section. -/
theorem hasDerivAt_gaussianSection_test {r : ℕ} (u : Vector r) (b : ℝ)
    (f : Vector r → ℝ) (df : Vector r → Vector r →L[ℝ] ℝ)
    (hdf : ∀ x, HasFDerivAt f (df x) x) (j : Fin r) (x : Vector r) :
    HasDerivAt (fun t => f (gaussianSectionPoint u b (Function.update x j t)))
      (df (gaussianSectionPoint u b x) (gaussianSectionTangent u j)) (x j) := by
  have hp : HasDerivAt
      (fun t : ℝ => gaussianSectionPoint u b x+(t-x j) • gaussianSectionTangent u j)
      (gaussianSectionTangent u j) (x j) := by
    simpa using (((hasDerivAt_id (x j)).sub_const (x j)).smul_const
      (gaussianSectionTangent u j)).const_add (gaussianSectionPoint u b x)
  have hh := (hdf (gaussianSectionPoint u b x)).comp_hasDerivAt_of_eq (x j) hp (by simp)
  simpa only [sub_self,zero_smul,add_zero,←gaussianSectionPoint_update] using hh


/-- Tangential Gaussian integration by parts on a concrete affine section.
The exact dimension drop and signed normal coefficient are retained. -/
theorem gaussianSection_Green_pullback {r : ℕ} (u : Vector r) (hu : vectorNormSq u=1)
    (b : ℝ) (f : Vector r → ℝ) (df : Vector r → Vector r →L[ℝ] ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hderiv : ∀ x, HasFDerivAt f (df x) x)
    (hfb : ∃ M, ∀ x, ‖f x‖≤M) (hdfb : ∃ M, ∀ x, ‖df x‖≤M) :
    (∫ g, (vectorNormSq (gaussianSectionPoint u b g)-(r:ℝ))*f (gaussianSectionPoint u b g)
      ∂standardGaussian r) =
      (b^2-1)*(∫ g, f (gaussianSectionPoint u b g) ∂standardGaussian r)+
      ∫ g, df (gaussianSectionPoint u b g) (gaussianSectionResidual u g) ∂standardGaussian r := by
  let S := gaussianSectionPoint u b
  let F := fun g => f (S g)
  let D := fun j g => df (S g) (gaussianSectionTangent u j)
  have hS : Continuous S := by
    unfold S gaussianSectionPoint gaussianSectionResidual faceDot
    fun_prop
  have hF : Continuous F := hf.comp hS
  have hD (j : Fin r) : Continuous (D j) :=
    (hdf.comp hS).clm_apply continuous_const
  have hFb : ∃ M, ∀ x, ‖F x‖≤M := by
    obtain ⟨M,hM⟩ := hfb
    exact ⟨M,fun x => hM (S x)⟩
  have hDb (j : Fin r) : ∃ M, ∀ x, ‖D j x‖≤M := by
    obtain ⟨M,hM⟩ := hdfb
    refine ⟨M*‖gaussianSectionTangent u j‖,fun x => ?_⟩
    exact ((df (S x)).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (hM (S x)) (norm_nonneg _))
  have hFD (j : Fin r) (x : Vector r) :
      HasDerivAt (fun t => F (Function.update x j t)) (D j x) (x j) :=
    hasDerivAt_gaussianSection_test u b f df hderiv j x
  have hsum (x v : Vector r) : (∑ j, v j*D j x)=
      df (S x) (gaussianSectionResidual u v) := by
    calc
      _ = ∑ j, df (S x) (v j • gaussianSectionTangent u j) := by simp [D]
      _ = df (S x) (∑ j, v j • gaussianSectionTangent u j) := (map_sum _ _ _).symm
      _ = _ := by rw [sum_smul_gaussianSectionTangent]
  have hz (x : Vector r) : (∑ j, u j*D j x)=0 := by
    rw [hsum]
    have hh : gaussianSectionResidual u u=0 := by
      rw [←sum_smul_gaussianSectionTangent,sum_self_smul_gaussianSectionTangent u hu]
    rw [hh,map_zero]
  have hgi : Integrable F (standardGaussian r) := by
    simpa only [one_mul] using integrable_gaussian_bounded_mul hF hFb
      (integrable_const (1:ℝ))
  have hnormalI := integrable_gaussian_bounded_mul hF hFb
    (standardGaussian_integrable_faceDot_sq u)
  have hradialI := integrable_gaussian_bounded_mul hF hFb
    ((standardGaussian_integrable_vectorNormSq r).sub (integrable_const (r:ℝ)))
  have hDx (j : Fin r) := integrable_gaussian_bounded_mul (hD j) (hDb j)
    (standardGaussian_integrable_coordinate r j)
  have hDu (j : Fin r) := integrable_gaussian_bounded_mul (hD j) (hDb j)
    (standardGaussian_integrable_faceDot u)
  have hzeroR : (∑ j, u j*(∫ x, faceDot u x*D j x ∂standardGaussian r))=0 := by
    simp_rw [←integral_const_mul]
    rw [←integral_finset_sum Finset.univ (fun j _ => (hDu j).const_mul (u j))]
    have he (x : Vector r) : (∑ j, u j*(faceDot u x*D j x))=0 := by
      calc
        _ = faceDot u x*(∑ j, u j*D j x) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl (fun j _ => by ring)
        _ = 0 := by rw [hz,mul_zero]
    simp_rw [he]
    exact integral_zero _ _
  have hnormal := gaussian_affine_weight_directional_stein hF hD hFD hFb hDb 0 u u
  have huu : faceDot u u=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hu
  simp only [zero_add,huu,one_mul,hzeroR,add_zero] at hnormal
  have hnormal' : (∫ x, faceDot u x^2*F x ∂standardGaussian r)=
      ∫ x, F x ∂standardGaussian r := by simpa only [pow_two] using hnormal
  have hradial := gaussian_radial_score_stein hF hD hFD hFb hDb
  rw [←integral_finset_sum Finset.univ (fun j _ => hDx j)] at hradial
  have hright : (∫ x, ∑ j, x j*D j x ∂standardGaussian r)=
      ∫ x, df (S x) (gaussianSectionResidual u x) ∂standardGaussian r :=
    integral_congr_ae (ae_of_all _ (fun x => hsum x x))
  rw [hright] at hradial
  have he (g : Vector r) : (vectorNormSq (S g)-(r:ℝ))*F g =
      (vectorNormSq g-(r:ℝ))*F g-faceDot u g^2*F g+b^2*F g := by
    rw [vectorNormSq_gaussianSectionPoint u b hu]
    ring
  change (∫ g, (vectorNormSq (S g)-(r:ℝ))*F g ∂standardGaussian r)=_
  simp_rw [he]
  have hadd := integral_add (hradialI.sub hnormalI) (hgi.const_mul (b^2))
  have hsub := integral_sub hradialI hnormalI
  simp only [Pi.sub_apply,Pi.add_apply] at hadd hsub
  rw [hadd,hsub,integral_const_mul,hnormal',hradial]
  ring


/-- The same signed Green identity written under the actual Gaussian
probability law on the affine hyperplane `u⋅x=b`. -/
theorem gaussianSection_Green {r : ℕ} (u : Vector r) (hu : vectorNormSq u=1)
    (b : ℝ) (f : Vector r → ℝ) (df : Vector r → Vector r →L[ℝ] ℝ)
    (hf : Continuous f) (hdf : Continuous df) (hderiv : ∀ x, HasFDerivAt f (df x) x)
    (hfb : ∃ M, ∀ x, ‖f x‖≤M) (hdfb : ∃ M, ∀ x, ‖df x‖≤M) :
    (∫ x, (vectorNormSq x-(r:ℝ))*f x ∂gaussianSectionLaw u b) =
      (b^2-1)*(∫ x, f x ∂gaussianSectionLaw u b)+
      ∫ x, df x (x-b • u) ∂gaussianSectionLaw u b := by
  have hscore : Continuous (fun x : Vector r => (vectorNormSq x-(r:ℝ))*f x) := by
    unfold vectorNormSq
    fun_prop
  have htest : Continuous (fun x : Vector r => df x (x-b • u)) :=
    hdf.clm_apply (continuous_id.sub continuous_const)
  unfold gaussianSectionLaw
  rw [integral_map (measurable_gaussianSectionPoint u b).aemeasurable hscore.aestronglyMeasurable,
    integral_map (measurable_gaussianSectionPoint u b).aemeasurable hf.aestronglyMeasurable,
    integral_map (measurable_gaussianSectionPoint u b).aemeasurable htest.aestronglyMeasurable]
  simpa only [gaussianSectionPoint,add_sub_cancel_left] using
    gaussianSection_Green_pullback u hu b f df hf hdf hderiv hfb hdfb

end
end RectangleCLTArxivV1
