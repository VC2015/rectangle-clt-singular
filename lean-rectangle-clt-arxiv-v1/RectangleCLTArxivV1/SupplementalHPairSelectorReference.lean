import RectangleCLTArxivV1.SupplementalHPairPlane
import RectangleCLTArxivV1.SupplementalHPairReference
import RectangleCLTArxivV1.SupplementalHSelectorReductions

/-! Actual two-face projected reference with every additional selector
factor retained, for the angle-weighted H2 matrix reduction. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def supplementalHPairReference {p : ℕ} (s : FaceSmoother p) (f g : Face p) (x : Vector p) : ℝ :=
  hReferencePair (s.faceScore f x/s.bandwidth,s.faceScore g x/s.bandwidth)

theorem supplementalHPairReference_bounds {p : ℕ}
    (s : FaceSmoother p) (f g : Face p) (x : Vector p) :
    0≤supplementalHPairReference s f g x ∧ supplementalHPairReference s f g x≤1 :=
  ⟨hReferencePair_nonneg _,hReferencePair_le_one _⟩

theorem measurable_supplementalHPairReference {p : ℕ}
    (s : FaceSmoother p) (f g : Face p) : Measurable (supplementalHPairReference s f g) :=
  measurable_hReferencePair.comp (((s.continuous_faceScore f).measurable.div_const _).prodMk
    ((s.continuous_faceScore g).measurable.div_const _))

theorem supplementalH_pair_first_weight_le_reference {p : ℕ}
    (s : FaceSmoother p) (f g : Face p) (hfg : f≠g) (x : Vector p) :
    s.F x*s.pi x f*s.pi x g≤supplementalHPairReference s f g x := by
  classical
  by_cases hf : f∈s.faces
  · by_cases hg : g∈s.faces
    · let w := s.weights x
      have hpair : w.weight f+w.weight g≤w.T := by
        have ht := Finset.sum_le_univ_sum_of_nonneg (fun i => w.nonneg i) (s := {f,g})
        simpa only [Finset.sum_pair hfg,FaceWeights.T] using ht
      have hwf : w.weight f=Real.exp (s.faceScore f x/s.bandwidth) := by simp only [w,FaceSmoother.weights,hf,if_true]
      have hwg : w.weight g=Real.exp (s.faceScore g x/s.bandwidth) := by simp only [w,FaceSmoother.weights,hg,if_true]
      have hpos : 0<1+Real.exp (s.faceScore f x/s.bandwidth)+Real.exp (s.faceScore g x/s.bandwidth) := by positivity
      have hden : 1+Real.exp (s.faceScore f x/s.bandwidth)+Real.exp (s.faceScore g x/s.bandwidth)≤1+w.T := by
        rw [←hwf,←hwg]
        linarith
      have he : s.F x*s.pi x f*s.pi x g=
          Real.exp (s.faceScore f x/s.bandwidth)*Real.exp (s.faceScore g x/s.bandwidth)/(1+w.T)^3 := by
        change (1/(1+w.T))*(w.weight f/(1+w.T))*(w.weight g/(1+w.T))=_
        rw [hwf,hwg]
        field_simp
        ring
      rw [he]
      exact div_le_div_of_nonneg_left (by positivity) (pow_pos hpos 3)
        (pow_le_pow_left₀ hpos.le hden 3)
    · have hz : s.pi x g=0 := by simp only [FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hg,if_false,zero_div]
      rw [hz,mul_zero]
      exact (supplementalHPairReference_bounds s f g x).1
  · have hz : s.pi x f=0 := by simp only [FaceSmoother.pi,FaceWeights.pi,FaceSmoother.weights,hf,if_false,zero_div]
    rw [hz,mul_zero,zero_mul]
    exact (supplementalHPairReference_bounds s f g x).1

theorem selectorWeight_le_supplementalHPairReference {p K : ℕ}
    (s : FaceSmoother p) (α : Fin (K+2) → Face p) (hfg : α 0≠α 1) (x : Vector p) :
    selectorWeight s α x≤supplementalHPairReference s (α 0) (α 1) x := by
  have htail : (∏ i : Fin K, s.pi x (α i.succ.succ))≤1 := by
    apply Finset.prod_le_one
    · intro i _
      exact (s.weights x).pi_nonneg _
    · intro i _
      exact ((s.weights x).pi_le_theta _).trans (s.weights x).theta_lt_one.le
  have he : selectorWeight s α x=(s.F x*s.pi x (α 0)*s.pi x (α 1))*
      (∏ i : Fin K, s.pi x (α i.succ.succ)) := by
    unfold selectorWeight
    rw [Fin.prod_univ_succ,Fin.prod_univ_succ]
    have hi : (0:Fin (K+1)).succ=(1:Fin (K+2)) := by apply Fin.ext; rfl
    rw [hi]
    ring
  rw [he]
  exact (mul_le_of_le_one_right (mul_nonneg (mul_nonneg (s.F_pos x).le ((s.weights x).pi_nonneg _))
    ((s.weights x).pi_nonneg _)) htail).trans (supplementalH_pair_first_weight_le_reference s _ _ hfg x)

/-- The true plane-projected H2 reduction for the actual pair reference.
The arbitrary later labels remain inside the original selector kernel. -/
theorem supplementalH_pair_selector_projected_reduction {p r K : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin r) ℝ) (v : Vector p) (σ : ℝ)
    (α : Fin (K+2) → Face p) (hunit : ∀ j,vectorNormSq (A j)=1)
    (hρ : (faceDot (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1)))^2<1) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id
      (fun g => selectorWeight s α ((σ • A).mulVec g+v))) ≤
      2*supplementalHSelectorProjection s (σ • A) v α
        (supplementalHPairPlane (selectorFaceNormal A (α 0)) (selectorFaceNormal A (α 1)))+
      4*(supplementalHSelectorMass s (σ • A) v α*
        Real.log ((∫ g, supplementalHPairReference s (α 0) (α 1) ((σ • A).mulVec g+v)
          ∂standardGaussian r)/supplementalHSelectorMass s (σ • A) v α))-
      supplementalHSelectorRadialTrace s (σ • A) v α := by
  let u := selectorFaceNormal A (α 0)
  let w := selectorFaceNormal A (α 1)
  let P := supplementalHPairPlane u w
  let β := fun z : Vector r => hReferencePair
    ((σ*faceDot u z+FaceSmoother.normalDot (α 0) v-s.offsets (α 0))/s.bandwidth,
     (σ*faceDot w z+FaceSmoother.normalDot (α 1) v-s.offsets (α 1))/s.bandwidth)
  have hu : vectorNormSq u=1 := selectorFaceNormal_normSq A hunit _
  have hw : vectorNormSq w=1 := selectorFaceNormal_normSq A hunit _
  have hfg : α 0≠α 1 := by
    intro he
    have hd : faceDot u w=1 := by
      dsimp only [u,w]
      rw [he]
      simpa only [faceDot,vectorNormSq,pow_two] using hw
    rw [hd] at hρ
    norm_num at hρ
  have hβm : Measurable β := by unfold β hReferencePair faceDot; fun_prop
  have hβb (z : Vector r) : 0≤β z ∧ β z≤1 := ⟨hReferencePair_nonneg _,hReferencePair_le_one _⟩
  have he (g : Vector r) : β (P.mulVec g)=supplementalHPairReference s (α 0) (α 1) ((σ • A).mulVec g+v) := by
    dsimp only [β,P]
    rw [supplementalHPairPlane_first_coordinate u w g hu,
      supplementalHPairPlane_second_coordinate u w g hu hw hρ]
    simp only [supplementalHPairReference,FaceSmoother.faceScore,Matrix.smul_mulVec_assoc,normalDot_affine]
    rfl
  have hb (g) : selectorWeight s α ((σ • A).mulVec g+v)≤β (P.mulVec g) := by
    rw [he]
    exact selectorWeight_le_supplementalHPairReference s α hfg _
  have ht := supplementalH_selector_projected_reduction s (σ • A) v α P
    (supplementalHPairPlane_transpose u w) (supplementalHPairPlane_idempotent u w hu hw hρ) β hβm hβb hb
  simp only [supplementalHSelectorEntropy,he] at ht
  exact ht

end
end RectangleCLTArxivV1
