import RectangleCLTArxivV1.SupplementalHCubicMoments
import RectangleCLTArxivV1.SupplementalGScoreRestoration

/-! The actual cubic Hermite matrix is split into the two positive
log-concave Gaussian scores and a symmetric first-moment correction. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def supplementalHCubicSelectorScore {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p)
    (u : Vector r) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∫ g, capThirdHermiteMatrix u g j k*selectorWeight s α (A.mulVec g+v) ∂standardGaussian r

/-- The correction may be bounded by a mean-square term. This loses
only a harmless factor of sqrt(L) in the final cubic matrix estimate. -/
theorem supplementalH_cross_nuclear_le {r : ℕ} (u z : Vector r) :
    symmetricNuclearNorm (Matrix.vecMulVec u z+Matrix.vecMulVec z u) ≤
      vectorNormSq u+vectorNormSq z := by
  have hpar : vectorNormSq (u+z)+vectorNormSq (u-z)=2*(vectorNormSq u+vectorNormSq z) := by
    unfold vectorNormSq
    simp only [Pi.add_apply,Pi.sub_apply]
    rw [mul_add,Finset.mul_sum,Finset.mul_sum,←Finset.sum_add_distrib,←Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  have hid : Matrix.vecMulVec u z+Matrix.vecMulVec z u =
      (1/2:ℝ) • (rankOne (u+z)-rankOne (u-z)) := by
    ext j k
    simp only [Matrix.add_apply,Matrix.vecMulVec_apply,Matrix.smul_apply,
      Matrix.sub_apply,rankOne,Pi.add_apply,Pi.sub_apply,smul_eq_mul]
    ring
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B,hB,rfl⟩
  apply (le_abs_self _).trans
  rw [hid,Matrix.mul_smul,Matrix.trace_smul,smul_eq_mul,abs_mul,
    abs_of_pos (by norm_num : (0:ℝ)<1/2),Matrix.mul_sub,Matrix.trace_sub,
    trace_mul_rankOne,trace_mul_rankOne]
  have hh := (abs_sub _ _).trans (add_le_add (hB.2.1 (u+z)) (hB.2.1 (u-z)))
  have hs := mul_le_mul_of_nonneg_left hh (by norm_num : (0:ℝ)≤1/2)
  rw [hpar] at hs
  linarith only [hs]

/-- Entrywise Gaussian integral identity; every direction, reference
weight and independent Gaussian expectation is the actual one. -/
theorem supplementalH_cubic_selector_decomposition {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (ha : ∀ i, α i ∈ s.faces) (u : Vector r) :
    supplementalHCubicSelectorScore s A v α u =
      weightedScore (standardGaussian r) id
        (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))-
      weightedScore (standardGaussian r) id
        (fun g => supplementalHPositiveDirection (-u) g*selectorWeight s α (A.mulVec g+v))-
      supplementalHSelectorMass s A v α •
        (Matrix.vecMulVec u (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g+v)))+
        Matrix.vecMulVec (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g+v))) u) := by
  let w := fun g => selectorWeight s α (A.mulVec g+v)
  let wp := fun g => supplementalHPositiveDirection u g*w g
  let wm := fun g => supplementalHPositiveDirection (-u) g*w g
  have hm (z : Vector r) : Measurable (fun g => supplementalHPositiveDirection z g*w g) := by
    apply Measurable.mul _ (continuous_selectorWeight_affine s α A v).measurable
    unfold supplementalHPositiveDirection faceDot
    fun_prop
  have hi (z : Vector r) := supplementalH_positive_selector_moments s A v α z
  have hp0 (z : Vector r) (g : Vector r) : 0 ≤ supplementalHPositiveDirection z g*w g :=
    mul_nonneg (supplementalHPositiveDirection_nonneg z g) (selectorWeight_nonneg s α _)
  have hcoords (z : Vector r) := gaussian_weighted_coordinate_moments _ (hm z) (hp0 z) (hi z).1 (hi z).2
  have hfirst := (selectorWeight_affine_moments s α A v).2.1
  have hp := selectorWeight_affine_mass_pos s α ha A v
  have hmean (j : Fin r) : supplementalHSelectorMass s A v α *
      weightMean (standardGaussian r) id w j = ∫ g, g j*w g ∂standardGaussian r := by
    change weightMass (standardGaussian r) w*((∫ g, g j*w g ∂standardGaussian r)/weightMass (standardGaussian r) w)=_
    field_simp
  ext j k
  have hiscore (z : Vector r) : Integrable (fun g => (g j*g k-if j=k then 1 else 0)*
      (supplementalHPositiveDirection z g*w g)) (standardGaussian r) := by
    simpa only [sub_mul] using ((hcoords z).2 j k).sub ((hi z).1.const_mul (if j=k then 1 else 0))
  have hid (g : Vector r) : capThirdHermiteMatrix u g j k*w g =
      (g j*g k-if j=k then 1 else 0)*wp g-
      (g j*g k-if j=k then 1 else 0)*wm g-
        (u j*(g k*w g)+(g j*w g)*u k) := by
    have hh := supplementalHPositiveDirection_sub u g
    dsimp only [wp,wm]
    unfold capThirdHermiteMatrix
    rw [←hh]
    ring
  let fp := fun g : Vector r => (g j*g k-if j=k then 1 else 0)*wp g
  let fm := fun g : Vector r => (g j*g k-if j=k then 1 else 0)*wm g
  let fu := fun g : Vector r => u j*(g k*w g)
  let fv := fun g : Vector r => (g j*w g)*u k
  have hip : Integrable fp (standardGaussian r) := hiscore u
  have him : Integrable fm (standardGaussian r) := hiscore (-u)
  have hiu : Integrable fu (standardGaussian r) := (hfirst k).const_mul (u j)
  have hiv : Integrable fv (standardGaussian r) := (hfirst j).mul_const (u k)
  change (∫ g, capThirdHermiteMatrix u g j k*w g ∂standardGaussian r) =
    (∫ g, fp g ∂standardGaussian r)-(∫ g, fm g ∂standardGaussian r)-
    supplementalHSelectorMass s A v α*(u j*weightMean (standardGaussian r) id w k+
      weightMean (standardGaussian r) id w j*u k)
  calc
    _ = ∫ g, fp g-fm g-(fu g+fv g) ∂standardGaussian r :=
      integral_congr_ae (ae_of_all _ hid)
    _ = ((∫ g, fp g ∂standardGaussian r)-(∫ g, fm g ∂standardGaussian r))-
        (u j*(∫ g, g k*w g ∂standardGaussian r)+(∫ g, g j*w g ∂standardGaussian r)*u k) := by
      calc
        _ = (∫ g, fp g-fm g ∂standardGaussian r)-(∫ g, fu g+fv g ∂standardGaussian r) :=
          integral_sub (hip.sub him) (hiu.add hiv)
        _ = _ := by
          rw [integral_sub hip him,integral_add hiu hiv]
          simp only [fu,fv,integral_const_mul,integral_mul_const]
    _ = _ := by rw [←hmean j,←hmean k]; ring


def supplementalHCubicMeanEnergy {p r K : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (α : Fin K → Face p) (u : Vector r) : ℝ :=
  weightMass (standardGaussian r)
      (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v))*
    vectorNormSq (weightMean (standardGaussian r) id
      (fun g => supplementalHPositiveDirection u g*selectorWeight s α (A.mulVec g+v)))

/-- The H3 reduction at the genuine Gaussian expectation. The trace is
kept signed and the first-label normal need not be independent of any
later selector label. -/
theorem supplementalH_cubic_selector_nuclear_reduction {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p)
    (α : Fin K → Face p) (ha : ∀ i, α i ∈ s.faces) (u : Vector r) (hu : vectorNormSq u=1) :
    symmetricNuclearNorm (supplementalHCubicSelectorScore s A v α u) ≤
      2*supplementalHCubicMeanEnergy s A v α u+
      2*supplementalHCubicMeanEnergy s A v α (-u)+
      supplementalHSelectorMass s A v α*(1+
        vectorNormSq (weightMean (standardGaussian r) id
          (fun g => selectorWeight s α (A.mulVec g+v))))-
      ∫ g, (vectorNormSq g-(r:ℝ))*|faceDot u g| *selectorWeight s α (A.mulVec g+v) ∂standardGaussian r := by
  let w := fun g => selectorWeight s α (A.mulVec g+v)
  let wp := fun g => supplementalHPositiveDirection u g*w g
  let wm := fun g => supplementalHPositiveDirection (-u) g*w g
  let mu := weightMean (standardGaussian r) id w
  let cross := Matrix.vecMulVec u mu+Matrix.vecMulVec mu u
  let Mp := weightedScore (standardGaussian r) id wp
  let Mm := weightedScore (standardGaussian r) id wm
  let mass := supplementalHSelectorMass s A v α
  have hmass : 0 ≤ mass := integral_nonneg (fun g => selectorWeight_nonneg s α _)
  have hdecomp : supplementalHCubicSelectorScore s A v α u = Mp-Mm-mass • cross :=
    supplementalH_cubic_selector_decomposition s A v α ha u
  have hcross : symmetricNuclearNorm cross ≤ 1+vectorNormSq mu := by
    simpa only [hu] using supplementalH_cross_nuclear_le u mu
  have htri : symmetricNuclearNorm (supplementalHCubicSelectorScore s A v α u) ≤
      symmetricNuclearNorm Mp+symmetricNuclearNorm Mm+mass*(1+vectorNormSq mu) := by
    rw [hdecomp,sub_eq_add_neg,sub_eq_add_neg]
    calc
      _ ≤ symmetricNuclearNorm (Mp+-Mm)+symmetricNuclearNorm (-(mass • cross)) :=
        symmetricNuclearNorm_add_le _ _
      _ ≤ symmetricNuclearNorm Mp+symmetricNuclearNorm (-Mm)+symmetricNuclearNorm (-(mass • cross)) :=
        add_le_add_right (symmetricNuclearNorm_add_le _ _) _
      _ = symmetricNuclearNorm Mp+symmetricNuclearNorm Mm+mass*symmetricNuclearNorm cross := by
        rw [symmetricNuclearNorm_neg,symmetricNuclearNorm_neg,
          symmetricNuclearNorm_nonneg_smul cross hmass]
      _ ≤ _ := add_le_add_left (mul_le_mul_of_nonneg_left hcross hmass) _
  have hum : vectorNormSq (-u)=1 := by simpa only [vectorNormSq,Pi.neg_apply,neg_sq] using hu
  have hp := supplementalH_positive_selector_matrix_reduction s A v α ha u hu
  have hm := supplementalH_positive_selector_matrix_reduction s A v α ha (-u) hum
  have hp2 : symmetricNuclearNorm Mp ≤ 2*supplementalHCubicMeanEnergy s A v α u-
      ∫ g, (vectorNormSq g-(r:ℝ))*wp g ∂standardGaussian r := by
    simpa only [supplementalHCubicMeanEnergy,mul_assoc] using hp
  have hm2 : symmetricNuclearNorm Mm ≤ 2*supplementalHCubicMeanEnergy s A v α (-u)-
      ∫ g, (vectorNormSq g-(r:ℝ))*wm g ∂standardGaussian r := by
    simpa only [supplementalHCubicMeanEnergy,mul_assoc] using hm
  have htrace (z : Vector r) : Integrable (fun g => (vectorNormSq g-(r:ℝ))*
      (supplementalHPositiveDirection z g*w g)) (standardGaussian r) := by
    have hi := supplementalH_positive_selector_moments s A v α z
    simpa only [sub_mul] using hi.2.sub (hi.1.const_mul (r:ℝ))
  have ht : (∫ g, (vectorNormSq g-(r:ℝ))*wp g ∂standardGaussian r)+
      (∫ g, (vectorNormSq g-(r:ℝ))*wm g ∂standardGaussian r) =
      ∫ g, (vectorNormSq g-(r:ℝ))*|faceDot u g| *w g ∂standardGaussian r := by
    rw [←integral_add (htrace u) (htrace (-u))]
    apply integral_congr_ae
    exact ae_of_all _ (fun g => by
      dsimp only [wp,wm]
      rw [show (vectorNormSq g-(r:ℝ))*(supplementalHPositiveDirection u g*w g)+
          (vectorNormSq g-(r:ℝ))*(supplementalHPositiveDirection (-u) g*w g) =
          (vectorNormSq g-(r:ℝ))*(supplementalHPositiveDirection u g+
            supplementalHPositiveDirection (-u) g)*w g by ring,
        supplementalHPositiveDirection_add])
  change _ ≤ 2*supplementalHCubicMeanEnergy s A v α u+
    2*supplementalHCubicMeanEnergy s A v α (-u)+mass*(1+vectorNormSq mu)-_
  nlinarith only [htri,hp2,hm2,ht]

end
end RectangleCLTArxivV1
