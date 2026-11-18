import RectangleCLTArxivV1.SupplementalHNonsimpleExample
import RectangleCLTArxivV1.SupplementalHSphericalPolygonCoverage

/-! Actual four-edge spherical balance at the nonsimple square-cone
vertex. Every incidence and polar-ray coverage fact is proved explicitly;
the final identity has no geometric completeness or analytic supplier. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 2000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)
attribute [local simp] Matrix.cons_val_two Matrix.cons_val_three

def nonsimpleSquareEdgeLeft : Fin 4 → Fin 4 := ![0,0,1,1]
def nonsimpleSquareEdgeRight : Fin 4 → Fin 4 := ![2,3,2,3]
def nonsimpleSquareConormalScale : ℝ := (Real.sqrt 3)⁻¹

theorem nonsimpleSquareConormalScale_pos : 0<nonsimpleSquareConormalScale :=
  inv_pos.mpr (Real.sqrt_pos.2 (by norm_num))

theorem nonsimpleSquareConormalScale_sq : nonsimpleSquareConormalScale^2=(1 : ℝ)/3 := by
  rw [nonsimpleSquareConormalScale,inv_pow,Real.sq_sqrt (by norm_num : (0 : ℝ)≤3)]
  norm_num

def nonsimpleSquareRawConormals : Fin 4 → Vector 3 :=
  ![![-1,-1,-1],![-1,1,-1],![1,-1,-1],![1,1,-1]]

def nonsimpleSquareInwardConormals (e : Fin 4) : E3 :=
  (WithLp.equiv 2 (Vector 3)).symm
    (nonsimpleSquareConormalScale • nonsimpleSquareRawConormals e)

theorem nonsimpleSquareInwardConormals_unit (e : Fin 4) :
    ‖nonsimpleSquareInwardConormals e‖=1 := by
  have hr : vectorNormSq (nonsimpleSquareRawConormals e)=3 := by
    fin_cases e <;> norm_num [nonsimpleSquareRawConormals,vectorNormSq,Fin.sum_univ_succ]
  have hs : vectorNormSq (nonsimpleSquareConormalScale • nonsimpleSquareRawConormals e)=1 := by
    calc
      _=nonsimpleSquareConormalScale^2*vectorNormSq (nonsimpleSquareRawConormals e) := by
        simp only [vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,Finset.mul_sum]
      _=1 := by rw [nonsimpleSquareConormalScale_sq,hr];norm_num
  have hsq : ‖nonsimpleSquareInwardConormals e‖^2=1 := by
    rw [←supplementalH_vectorNormSq_equiv]
    exact hs
  nlinarith [norm_nonneg (nonsimpleSquareInwardConormals e)]

theorem nonsimpleSquareEdge_distinct :
    ∀ e,nonsimpleSquareEdgeLeft e≠nonsimpleSquareEdgeRight e := by decide

theorem nonsimpleSquareEdge_pair_injective :
    Function.Injective (fun e =>
      ({nonsimpleSquareEdgeLeft e,nonsimpleSquareEdgeRight e} : Finset (Fin 4))) := by decide

theorem nonsimpleSquareInwardConormals_inner (e i : Fin 4) :
    ⟪nonsimpleSquareInwardConormals e,nonsimpleSquareEuclideanNormals i⟫_ℝ=
      if i=nonsimpleSquareEdgeLeft e ∨ i=nonsimpleSquareEdgeRight e then 0
      else 2*nonsimpleSquareScale*nonsimpleSquareConormalScale := by
  rw [real_inner_comm,nonsimpleSquareEuclideanNormals_inner]
  fin_cases e <;> fin_cases i <;>
    norm_num [Fin.ext_iff,Fin.coe_ofNat_eq_mod,Fin.val_natCast,
      nonsimpleSquareEdgeLeft,nonsimpleSquareEdgeRight,
      nonsimpleSquareInwardConormals,nonsimpleSquareRawConormals,nonsimpleSquareDefect] <;> ring

theorem nonsimpleSquareInwardConormals_zero :
    ∀ e,⟪nonsimpleSquareInwardConormals e,
        nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeLeft e)⟫_ℝ=0 ∧
      ⟪nonsimpleSquareInwardConormals e,
        nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeRight e)⟫_ℝ=0 := by
  intro e
  constructor <;> rw [nonsimpleSquareInwardConormals_inner] <;> simp

theorem nonsimpleSquareInwardConormals_strict :
    ∀ e i,i≠nonsimpleSquareEdgeLeft e → i≠nonsimpleSquareEdgeRight e →
      0<⟪nonsimpleSquareInwardConormals e,nonsimpleSquareEuclideanNormals i⟫_ℝ := by
  intro e i hleft hright
  rw [nonsimpleSquareInwardConormals_inner,if_neg (by simp [hleft,hright])]
  exact mul_pos (mul_pos (by norm_num : (0 : ℝ)<2) nonsimpleSquareScale_pos)
    nonsimpleSquareConormalScale_pos

theorem nonsimpleSquareEdge_sum_ne_zero :
    ∀ e,nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeLeft e)+
      nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeRight e)≠0 := by
  intro e hz
  have h := congrArg (fun x : E3 => x 2) hz
  have hs := nonsimpleSquareScale_pos
  fin_cases e <;>
    norm_num [nonsimpleSquareEdgeLeft,nonsimpleSquareEdgeRight,nonsimpleSquareEuclideanNormals,
      nonsimpleSquareNormals,nonsimpleSquareRawNormals] at h <;> linarith

theorem nonsimpleSquareEdge_sub_ne_zero :
    ∀ e,nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeLeft e)-
      nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeRight e)≠0 := by
  intro e hz
  have h := congrArg (fun x : E3 => x 0) hz
  have hs := nonsimpleSquareScale_pos
  fin_cases e <;>
    norm_num [nonsimpleSquareEdgeLeft,nonsimpleSquareEdgeRight,nonsimpleSquareEuclideanNormals,
      nonsimpleSquareNormals,nonsimpleSquareRawNormals] at h <;> linarith

def nonsimpleSquarePolarDefects (w : E3) : Vector 4 :=
  ![w 0-w 2,-w 0-w 2,w 1-w 2,-w 1-w 2]

theorem nonsimpleSquarePolarDefects_nonneg (w : E3)
    (hw : ∀ i,0≤⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ) :
    ∀ i,0≤nonsimpleSquarePolarDefects w i := by
  intro i
  have h := hw i
  rw [nonsimpleSquareEuclideanNormals_inner] at h
  exact (mul_le_mul_left nonsimpleSquareScale_pos).mp
    (by simpa only [mul_zero] using h)

theorem nonsimpleSquarePolarDefects_zero {w : E3} {i : Fin 4}
    (hi : ⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ=0) :
    nonsimpleSquarePolarDefects w i=0 := by
  rw [nonsimpleSquareEuclideanNormals_inner] at hi
  exact (mul_eq_zero.mp hi).resolve_left nonsimpleSquareScale_pos.ne'

theorem nonsimpleSquare_polar_third_nonpos (w : E3)
    (hw : ∀ i,0≤⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ) : w 2≤0 := by
  have h0 := nonsimpleSquarePolarDefects_nonneg w hw 0
  have h1 := nonsimpleSquarePolarDefects_nonneg w hw 1
  change 0≤w 0-w 2 at h0
  change 0≤-w 0-w 2 at h1
  linarith

theorem nonsimpleSquare_polar_third_zero (w : E3)
    (hw : ∀ i,0≤⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ) (hz : w 2=0) : w=0 := by
  have h0 := nonsimpleSquarePolarDefects_nonneg w hw 0
  have h1 := nonsimpleSquarePolarDefects_nonneg w hw 1
  have h2 := nonsimpleSquarePolarDefects_nonneg w hw 2
  have h3 := nonsimpleSquarePolarDefects_nonneg w hw 3
  change 0≤w 0-w 2 at h0
  change 0≤-w 0-w 2 at h1
  change 0≤w 1-w 2 at h2
  change 0≤-w 1-w 2 at h3
  apply PiLp.ext
  intro k
  fin_cases k
  · change w 0=0
    linarith
  · change w 1=0
    linarith
  · change w 2=0
    exact hz

/-- Opposite-axis zero pairs are impossible for a nonzero polar vector;
every remaining pair is one of the four actual adjacent pairs. -/
theorem nonsimpleSquare_polar_zero_pair_is_edge (w : E3) (hw0 : w≠0)
    (hw : ∀ i,0≤⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ)
    (i j : Fin 4) (hij : i≠j)
    (hi : nonsimpleSquarePolarDefects w i=0)
    (hj : nonsimpleSquarePolarDefects w j=0) :
    ∃ e,nonsimpleSquarePolarDefects w (nonsimpleSquareEdgeLeft e)=0 ∧
      nonsimpleSquarePolarDefects w (nonsimpleSquareEdgeRight e)=0 := by
  have hopposite01 (h0 : nonsimpleSquarePolarDefects w 0=0)
      (h1 : nonsimpleSquarePolarDefects w 1=0) : False := by
    apply hw0
    apply nonsimpleSquare_polar_third_zero w hw
    change w 0-w 2=0 at h0
    change -w 0-w 2=0 at h1
    linarith
  have hopposite23 (h2 : nonsimpleSquarePolarDefects w 2=0)
      (h3 : nonsimpleSquarePolarDefects w 3=0) : False := by
    apply hw0
    apply nonsimpleSquare_polar_third_zero w hw
    change w 1-w 2=0 at h2
    change -w 1-w 2=0 at h3
    linarith
  fin_cases i <;> fin_cases j <;> norm_num at hij
  · exact False.elim (hopposite01 hi hj)
  · exact ⟨0,hi,hj⟩
  · exact ⟨1,hi,hj⟩
  · exact False.elim (hopposite01 hj hi)
  · exact ⟨2,hi,hj⟩
  · exact ⟨3,hi,hj⟩
  · exact ⟨0,hj,hi⟩
  · exact ⟨2,hj,hi⟩
  · exact False.elim (hopposite23 hi hj)
  · exact ⟨1,hj,hi⟩
  · exact ⟨3,hj,hi⟩
  · exact False.elim (hopposite23 hj hi)

theorem nonsimpleSquare_polar_edge_multiple (w : E3) (e : Fin 4)
    (hl : nonsimpleSquarePolarDefects w (nonsimpleSquareEdgeLeft e)=0)
    (hr : nonsimpleSquarePolarDefects w (nonsimpleSquareEdgeRight e)=0) :
    w=(-w 2*Real.sqrt 3) • nonsimpleSquareInwardConormals e := by
  have hcoef : (-w 2*Real.sqrt 3)*nonsimpleSquareConormalScale= -w 2 := by
    rw [nonsimpleSquareConormalScale,mul_assoc,
      mul_inv_cancel₀ (Real.sqrt_pos.2 (by norm_num : (0 : ℝ)<3)).ne',mul_one]
  apply PiLp.ext
  intro k
  change w k=(-w 2*Real.sqrt 3)*(nonsimpleSquareConormalScale*nonsimpleSquareRawConormals e k)
  rw [←mul_assoc,hcoef]
  fin_cases e <;> fin_cases k <;>
    simp [nonsimpleSquareEdgeLeft,nonsimpleSquareEdgeRight,nonsimpleSquarePolarDefects,
      nonsimpleSquareRawConormals] at hl hr ⊢ <;> linarith

theorem nonsimpleSquare_nonzero_polar_incident_coverage :
    ∀ w : E3,w≠0 → (∀ i,0≤⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ) →
      (∃ i j : Fin 4,i≠j ∧ ⟪nonsimpleSquareEuclideanNormals i,w⟫_ℝ=0 ∧
        ⟪nonsimpleSquareEuclideanNormals j,w⟫_ℝ=0) →
      ∃ e : Fin 4,∃ t : ℝ,0≤t ∧ w=t • nonsimpleSquareInwardConormals e := by
  intro w hw0 hw hpair
  obtain ⟨i,j,hij,hi,hj⟩ := hpair
  obtain ⟨e,heleft,heright⟩ := nonsimpleSquare_polar_zero_pair_is_edge w hw0 hw i j hij
    (nonsimpleSquarePolarDefects_zero hi) (nonsimpleSquarePolarDefects_zero hj)
  refine ⟨e,-w 2*Real.sqrt 3,?_,nonsimpleSquare_polar_edge_multiple w e heleft heright⟩
  exact mul_nonneg (neg_nonneg.mpr (nonsimpleSquare_polar_third_nonpos w hw)) (Real.sqrt_nonneg _)

theorem nonsimpleSquare_normal_span_eq_top :
    Submodule.span ℝ (Set.range nonsimpleSquareEuclideanNormals)=⊤ := by
  simpa only [nonsimpleFaceNormalSpace,Finset.coe_univ,Set.image_univ] using
    nonsimpleSquare_normalSpace_eq_top

/-- Literal four-edge balance on the actual nonsimple square normal cone,
with every geometric completeness and incidence input proved internally. -/
theorem nonsimpleSquare_four_edge_spherical_balance :
    (∑ e,Real.arccos ⟪nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeLeft e),
        nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeRight e)⟫_ℝ •
      nonsimpleSquareInwardConormals e)=
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection
        (sphericalPolygonGeneratedCone nonsimpleSquareEuclideanNormals),
        ω.1 ∂(volume : Measure E3).toSphere := by
  obtain ⟨d,hd⟩ := nonsimpleSquare_euclidean_strictInterior
  exact sphericalPolygon_nonzero_incident_balance nonsimpleSquareEuclideanNormals
    nonsimpleSquareEdgeLeft nonsimpleSquareEdgeRight nonsimpleSquareInwardConormals
    nonsimpleSquare_normal_span_eq_top d hd nonsimpleSquareEuclideanNormals_unit
    nonsimpleSquareInwardConormals_unit nonsimpleSquareEdge_distinct nonsimpleSquareEdge_pair_injective
    nonsimpleSquareInwardConormals_zero nonsimpleSquareInwardConormals_strict
    nonsimpleSquareEdge_sum_ne_zero nonsimpleSquareEdge_sub_ne_zero
    nonsimpleSquare_nonzero_polar_incident_coverage

theorem nonsimpleSquare_four_edge_spherical_balance_norm_le :
    ‖∑ e,Real.arccos ⟪nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeLeft e),
        nonsimpleSquareEuclideanNormals (nonsimpleSquareEdgeRight e)⟫_ℝ •
      nonsimpleSquareInwardConormals e‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (sphericalPolygonGeneratedCone nonsimpleSquareEuclideanNormals)) := by
  rw [nonsimpleSquare_four_edge_spherical_balance,norm_smul,Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1
