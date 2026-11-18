import RectangleCLTArxivV1.SupplementalHTripleTransportFrame

/-! Genuine rank-three conical fourth-radius event transport. The vector
coefficient is the actual spherical integral of the actual cone. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set Metric RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def tripleConeEvent {m r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : EuclideanSpace ℝ (Fin 3)) (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (u : Fin m → Vector r) (b : Vector m) (s : Finset (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin 3))) : Set (Vector r) :=
  {g | (∀ k∈s,faceDot (u k) (tripleTransportSection L Z g)<b k) ∧
    tripleTransportCoordinate L g-Z∈C ∧
    ‖tripleTransportCoordinate L g-Z‖<1/(4*R (projectionEuclideanVector (tripleTransportSection L Z g))) ∧
    tripleTransportCoordinate L g-Z≠0}

theorem measurableSet_tripleConeEvent {m r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z : EuclideanSpace ℝ (Fin 3)) (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : Continuous R)
    (u : Fin m → Vector r) (b : Vector m) (s : Finset (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : MeasurableSet C) :
    MeasurableSet (tripleConeEvent L Z R u b s C) := by
  have hb : Measurable (tripleTransportSection L Z) :=
    (measurable_tripleTransportSection L).comp (measurable_const.prodMk measurable_id)
  have hd := (measurable_tripleTransportCoordinate L).sub_const Z
  have hr := hR.measurable.comp ((PiLp.continuous_equiv_symm 2 _).measurable.comp hb)
  unfold tripleConeEvent
  simp only [setOf_and,setOf_forall]
  exact (MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
    measurableSet_lt ((measurable_thresholdDot _).comp hb) measurable_const))).inter
    ((hC.preimage hd).inter ((measurableSet_lt hd.norm (measurable_const.div (measurable_const.mul hr))).inter
      (measurableSet_eq_fun hd measurable_const).compl))

theorem tripleConeEvent_section {m r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (Z y : EuclideanSpace ℝ (Fin 3)) (R : EuclideanSpace ℝ (Fin r) → ℝ)
    (u : Fin m → Vector r) (b : Vector m) (s : Finset (Fin m))
    (C : Set (EuclideanSpace ℝ (Fin 3))) (g : Vector r) :
    tripleTransportSection L (Z+y) g∈tripleConeEvent L Z R u b s C ↔
      (∀ k∈s,faceDot (u k) (tripleTransportSection L Z g)<b k) ∧
      y∈(C∩ball 0 (1/(4*R (projectionEuclideanVector (tripleTransportSection L Z g)))))\{0} := by
  simp only [tripleConeEvent,mem_setOf_eq,tripleTransportSection_comp,tripleTransportCoordinate_section,
    add_sub_cancel_left,mem_diff,mem_inter_iff,mem_ball,dist_zero_right,mem_singleton_iff]
  tauto

/-- The normalized true spherical coefficient is paid by the actual cone
fiber. Removing the zero displacement changes no ordinary volume integral. -/
theorem tripleCone_fiber_coefficient_bound {r : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin r))
    (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ,0<t → ∀ y : EuclideanSpace ℝ (Fin 3),t • y∈C ↔ y∈C)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (x : EuclideanSpace ℝ (Fin r))
    (Z : EuclideanSpace ℝ (Fin 3)) (hz : ‖Z‖≤R x) :
    |⟪Z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C,ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ| *
      tripleEuclideanDensity Z≤
    (6144*Real.exp ((3:ℝ)/2))*(∫ y in (C∩ball 0 (1/(4*R x)))\{0},
      R (x+L y)^4*tripleEuclideanDensity (Z+y)) := by
  have hf := adaptive_cone_spherical_vector_fourth_bound (volume : Measure (EuclideanSpace ℝ (Fin 3)))
    (by simp) C hC hcone L R hRm hR hRadd x Z hz
  let d := (Real.sqrt (2*Real.pi))⁻¹^3
  have hd : 0≤d := by dsimp [d]; positivity
  have hAE : ((C∩ball 0 (1/(4*R x)))\{0} : Set (EuclideanSpace ℝ (Fin 3)))=ᵐ[volume]
      (C∩ball 0 (1/(4*R x)) : Set (EuclideanSpace ℝ (Fin 3))) := by
    have hzero : ∀ᵐ y : EuclideanSpace ℝ (Fin 3) ∂volume,y≠0 := by simp [ae_iff]
    filter_upwards [hzero] with y hy
    apply propext
    change ((y∈C∩ball 0 (1/(4*R x))) ∧ y∉({0} : Set (EuclideanSpace ℝ (Fin 3)))) ↔
      y∈C∩ball 0 (1/(4*R x))
    simp [hy]
  rw [setIntegral_congr_set hAE]
  have he : (∫ y in C∩ball 0 (1/(4*R x)),R (x+L y)^4*tripleEuclideanDensity (Z+y))=
      d*(∫ y in C∩ball 0 (1/(4*R x)),R (x+L y)^4*RectangleCLT.Companion.SignedSurface.gaussianKernel (Z+y)) := by
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact ae_of_all _ (fun y => by dsimp only [tripleEuclideanDensity,d]; ring)
  rw [he]
  convert mul_le_mul_of_nonneg_left hf hd using 1 <;> dsimp only [tripleEuclideanDensity,d] <;> ring

/-- Actual conical rank-three Gaussian transport. Its left coefficient is
the true spherical vector integral; retained inequalities remain unchanged. -/
theorem tripleCone_spherical_coefficient_le_fourth_event {m n : ℕ}
    (L : EuclideanSpace ℝ (Fin 3) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (n+1)))
    (Z : EuclideanSpace ℝ (Fin 3)) (C : Set (EuclideanSpace ℝ (Fin 3))) (hC : MeasurableSet C)
    (hcone : ∀ t : ℝ,0<t → ∀ y : EuclideanSpace ℝ (Fin 3),t • y∈C ↔ y∈C)
    (R : EuclideanSpace ℝ (Fin (n+1)) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (u : Fin m → Vector (n+1)) (b : Vector m) (s : Finset (Fin m))
    (hz : ∀ g,‖Z‖≤R (projectionEuclideanVector (tripleTransportSection L Z g)))
    (hR4 : Integrable (fun g => R (projectionEuclideanVector g)^4) (standardGaussian (n+1))) :
    (|⟪Z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C,ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ| *
      tripleEuclideanDensity Z)*(standardGaussian (n+1)).real
        {g | ∀ k∈s,faceDot (u k) (tripleTransportSection L Z g)<b k}≤
      (6144*Real.exp ((3:ℝ)/2))*(∫ g,(tripleConeEvent L Z R u b s C).indicator
        (fun g => R (projectionEuclideanVector g)^4) g ∂standardGaussian (n+1)) := by
  let K := 6144*Real.exp ((3:ℝ)/2)
  have hK : 0≤K := by dsimp [K]; positivity
  let F := (tripleConeEvent L Z R u b s C).indicator (fun g => R (projectionEuclideanVector g)^4)
  have hmset := measurableSet_tripleConeEvent L Z R hRm u b s C hC
  have hF : Measurable F := ((hRm.comp (PiLp.continuous_equiv_symm 2 _)).measurable.pow_const 4).indicator hmset
  have hFi : Integrable F (standardGaussian (n+1)) := hR4.indicator hmset
  have hF0 (g) : 0≤F g := indicator_nonneg (fun _ _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g
  have hp := (tripleTransportSection_measurePreserving L).integrable_comp hF.aestronglyMeasurable |>.mpr hFi
  let V : Set (Vector (n+1)) := {g | ∀ k∈s,faceDot (u k) (tripleTransportSection L Z g)<b k}
  have hV : MeasurableSet V := by
    have hb : Measurable (tripleTransportSection L Z) :=
      (measurable_tripleTransportSection L).comp (measurable_const.prodMk measurable_id)
    unfold V
    simp only [setOf_forall]
    exact MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ =>
      measurableSet_lt ((measurable_thresholdDot _).comp hb) measurable_const))
  let d := |⟪Z,(2:ℝ) • ∫ ω in supplementalHSphericalSection C,ω.1 ∂(volume : Measure (EuclideanSpace ℝ (Fin 3))).toSphere⟫_ℝ| *
    tripleEuclideanDensity Z
  have hpoint : ∀ᵐ g ∂standardGaussian (n+1),V.indicator (fun _ => d) g≤
      K*(∫ z,F (tripleTransportSection L z g) ∂tripleEuclideanGaussian) := by
    filter_upwards [hp.prod_left_ae] with g hg
    by_cases hgv : g∈V
    · rw [indicator_of_mem hgv]
      have hf := tripleCone_fiber_coefficient_bound L C hC hcone R hRm hR hRadd
        (projectionEuclideanVector (tripleTransportSection L Z g)) Z (hz g)
      apply hf.trans
      apply mul_le_mul_of_nonneg_left _ hK
      apply tripleEuclideanGaussian_integral_dominates_translated_fiber
        (fun z => F (tripleTransportSection L z g))
        (fun y => R (projectionEuclideanVector (tripleTransportSection L Z g)+L y)^4)
        (hF.comp ((measurable_tripleTransportSection L).comp (measurable_id.prodMk measurable_const)))
        hg (fun _ => hF0 _) Z _ ((hC.inter measurableSet_ball).diff (measurableSet_singleton 0))
      intro y hy
      have hmem := (tripleConeEvent_section L Z y R u b s C g).mpr ⟨hgv,hy⟩
      dsimp only [F]
      rw [indicator_of_mem hmem,tripleTransportSection_add_normal]
    · rw [indicator_of_not_mem hgv]
      exact mul_nonneg hK (integral_nonneg (fun _ => hF0 _))
  have hh := integral_mono_ae ((integrable_const d).indicator hV) (hp.integral_prod_right.const_mul K) hpoint
  rw [integral_indicator_const _ hV,smul_eq_mul,mul_comm,integral_const_mul] at hh
  apply hh.trans_eq
  congr 1
  rw [← integral_prod_symm _ hp]
  exact integral_tripleTransportSection L F hF

end
end RectangleCLTArxivV1
