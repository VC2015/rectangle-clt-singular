import RectangleCLTArxivV1.SupplementalHFourthTransportRidge
import RectangleCLTArxivV1.SupplementalHSecondTubes

/-! Actual positive ridge fibers, preserving separate second/fourth moments. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

/-- Gaussian normalization transports the actual two-normal fiber. -/
theorem positiveRidge_fiber_of_kernel {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (x : Vector r)
    (q : ℕ) (A C : ℝ)
    (hkernel : A*RectangleCLT.Companion.SignedSurface.gaussianKernel (fourthRidgeNormalPoint u b j l) ≤
      C*(∫ st in ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R x)),
        R (projectionEuclideanVector x+ridgeDisplacement (projectionEuclideanVector (u j))
          (projectionEuclideanVector (u l)) st)^q*
        RectangleCLT.Companion.SignedSurface.gaussianKernel (fourthRidgeNormalPoint u b j l+ridgeDisplacement
          (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l)) st)
        ∂(volume : Measure ℝ).prod volume)) :
    A*gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
      C*(∫ st in ridgeRectangle (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R x)),
        fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^q*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume) := by
  let U := projectionEuclideanVector (u j)
  let V := projectionEuclideanVector (u l)
  let e := bisector U V
  let f := differenceDirection U V
  let a := thresholdPairFirstLevel u b j l
  let c := thresholdPairSecondLevel u b j l
  let X := projectionEuclideanVector x
  have hU : ‖U‖=1 := thresholdEuclideanNormal_unit _ hu
  have hV : ‖V‖=1 := thresholdEuclideanNormal_unit _ hv
  have he : ‖e‖=1 := norm_bisector _ _ hp
  have hf : ‖f‖=1 := norm_differenceDirection _ _ hm
  have hef : ⟪e,f⟫_ℝ=0 := inner_bisector_differenceDirection _ _ (hU.trans hV.symm)
  have hpoint : fourthRidgeNormalPoint u b j l=a • e+c • f := by
    rw [fourthRidgeNormalPoint,thresholdPairBisector_euclidean,thresholdPairDifference_euclidean]
  have hnorm (s t : ℝ) : ‖s • e+t • f‖^2=s^2+t^2 := by
    rw [norm_add_sq_real]
    simp only [norm_smul,Real.norm_eq_abs,he,hf,mul_one,sq_abs,inner_smul_left,
      inner_smul_right,conj_trivial,hef,mul_zero,zero_mul,add_zero]
  let d := (Real.sqrt (2*Real.pi))⁻¹^2
  have hd : 0≤d := by dsimp [d]; positivity
  have hpdf (s t : ℝ) : gaussianPDFReal 0 1 s*gaussianPDFReal 0 1 t=d*RectangleCLT.Companion.SignedSurface.gaussianKernel (s • e+t • f) := by
    rw [RectangleCLT.Companion.SignedSurface.gaussianKernel,hnorm]
    simp only [gaussianPDFReal,NNReal.coe_one,mul_one,sub_zero,d]
    rw [mul_mul_mul_comm,← Real.exp_add]
    congr 1
    · exact (pow_two _).symm
    · congr 1
      ring
  have hint : (∫ st in ridgeRectangle U V (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^q*
        gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2) ∂(volume : Measure ℝ).prod volume)=
      d*(∫ st in ridgeRectangle U V (1/(4*R X)),
        R (X+ridgeDisplacement U V st)^q*RectangleCLT.Companion.SignedSurface.gaussianKernel (fourthRidgeNormalPoint u b j l+ridgeDisplacement U V st)
          ∂(volume : Measure ℝ).prod volume) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun st => by
      dsimp only
      have hplane : fourthRidgeNormalPoint u b j l+ridgeDisplacement U V st=(a+st.1) • e+(c+st.2) • f := by
        rw [hpoint]
        dsimp only [ridgeDisplacement,e,f]
        module
      rw [hplane]
      have hr : fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)=
          R (X+ridgeDisplacement U V st) := by
        congr 1
        ext k
        change (x k+st.1*e k)+st.2*f k=x k+(st.1*e k+st.2*f k)
        ring
      rw [hr,show R (X+ridgeDisplacement U V st)^q*gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2)=
        R (X+ridgeDisplacement U V st)^q*(gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2)) by ring,hpdf]
      ring)
  change _≤C*(∫ st in ridgeRectangle U V (1/(4*fourthTransportRadius R x)),
      fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^q*
        gaussianPDFReal 0 1 (a+st.1)*gaussianPDFReal 0 1 (c+st.2) ∂(volume : Measure ℝ).prod volume)
  rw [hint,show A *
    gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c=
    A *
      (gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c) by ring,hpdf]
  rw [← hpoint]
  convert mul_le_mul_of_nonneg_left hkernel hd using 1 <;> ring <;> rfl

theorem positiveRidge_angle_second_fiber {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (x : Vector r)
    (hz : ‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R x) :
    Real.arccos ⟪projectionEuclideanVector (u j),projectionEuclideanVector (u l)⟫_ℝ*
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
      (512*Real.pi*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle
        (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R x)),
        fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^2*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume) := by
  have hU := thresholdEuclideanNormal_unit _ hu
  have hV := thresholdEuclideanNormal_unit _ hv
  have hb : |⟪fourthRidgeNormalPoint u b j l,
      bisector (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))⟫_ℝ|≤
      R (projectionEuclideanVector x) := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_bisector _ _ hp,mul_one]
    exact hz
  have hc : |⟪fourthRidgeNormalPoint u b j l,
      differenceDirection (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))⟫_ℝ|≤
      R (projectionEuclideanVector x) := by
    apply (abs_real_inner_le_norm _ _).trans
    rw [norm_differenceDirection _ _ hm,mul_one]
    exact hz
  exact positiveRidge_fiber_of_kernel u b j l hu hv hp hm R x 2 _ _
    (adaptive_angle_ridge_second_bound R hRm hR hRadd (projectionEuclideanVector x)
      (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
      (fourthRidgeNormalPoint u b j l) hU hV hp hm hb hc)

theorem positiveRidge_angle_normSq_fourth_fiber {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hp : projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0)
    (hm : projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (x : Vector r)
    (hz : ‖fourthRidgeNormalPoint u b j l‖≤fourthTransportRadius R x) :
    (Real.arccos ⟪projectionEuclideanVector (u j),projectionEuclideanVector (u l)⟫_ℝ*
      ‖fourthRidgeNormalPoint u b j l‖^2)*
      gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
      gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l) ≤
      (2048*Real.pi*Real.exp ((3:ℝ)/2))*(∫ st in ridgeRectangle
        (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
        (1/(4*fourthTransportRadius R x)),
        fourthTransportRadius R (x+st.1 • thresholdPairBisector u j l+st.2 • thresholdPairDifference u j l)^4*
        gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l+st.1)*
        gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l+st.2) ∂(volume : Measure ℝ).prod volume) := by
  exact positiveRidge_fiber_of_kernel u b j l hu hv hp hm R x 4 _ _
    (adaptive_angle_ridge_normSq_fourth_bound R hRm hR hRadd (projectionEuclideanVector x)
      (projectionEuclideanVector (u j)) (projectionEuclideanVector (u l))
      (fourthRidgeNormalPoint u b j l) (thresholdEuclideanNormal_unit _ hu)
      (thresholdEuclideanNormal_unit _ hv) hp hm hz)

end
end RectangleCLTArxivV1
