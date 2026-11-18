import RectangleCLTArxivV1.SupplementalHActualFacetSelection

/-! Short actual tubes of a selected exact facet presentation lie in the
outer layer of the original full family. This uses the genuine common
base and displacement, and makes no equality claim for expanded sets. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actualFacet_selectedTube_mem_originalOuterLayer {m q r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤b (e i)) ↔ ∀ k,faceDot (u k) y≤b k)
    (hu : ∀ k,vectorNormSq (u k)=1)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (active : Finset (Fin q))
    {g : Vector r} (hg : projectionEuclideanVector g∈adaptiveOutwardTube
      (fun i => projectionEuclideanVector (u (e i))) (fun i => b (e i)) R active) :
    g∈fourthOuterLayer u b R := by
  have he (x : EuclideanSpace ℝ (Fin r)) :
      (∀ i,⟪projectionEuclideanVector (u (e i)),x⟫_ℝ≤b (e i)) ↔
        ∀ k,⟪projectionEuclideanVector (u k),x⟫_ℝ≤b k := by
    have h := hequiv (fun i => x i)
    simpa only [faceDot_eq_euclidean_inner] using h
  obtain ⟨x,hx,c,hc,hd0,hd,hg⟩ := hg
  let d := coneDisplacement (fun i => projectionEuclideanVector (u (e i))) active c
  have hbase := (he x).mp hx.1
  have hwidth : ‖d‖≤1/R (x+d) := adaptive_displacement_le_reciprocal_radius R hR hRadd x d hd
  have hout : ¬∀ k,⟪projectionEuclideanVector (u k),x+d⟫_ℝ≤b k := by
    intro h
    exact outward_point_not_mem
      (coneDisplacement_isOutward (fun i => projectionEuclideanVector (u (e i)))
        (fun i => b (e i)) active hx c hc) hd0 ((he _).mpr h)
  have hexpand : ∀ k,⟪projectionEuclideanVector (u k),x+d⟫_ℝ≤b k+1/R (x+d) := by
    intro k
    rw [inner_add_right]
    apply add_le_add (hbase k)
    calc
      _≤|⟪projectionEuclideanVector (u k),d⟫_ℝ| := le_abs_self _
      _≤‖projectionEuclideanVector (u k)‖*‖d‖ := abs_real_inner_le_norm _ _
      _≤_ := by rw [thresholdEuclideanNormal_unit _ (hu k),one_mul]; exact hwidth
  change projectionEuclideanVector g=x+d at hg
  rw [← hg] at hexpand hout
  change (∀ k,faceDot (u k) g≤b k+1/fourthTransportRadius R g) ∧ ¬∀ k,faceDot (u k) g≤b k
  constructor
  · intro k
    have heq : faceDot (u k) g=⟪projectionEuclideanVector (u k),projectionEuclideanVector g⟫_ℝ :=
      faceDot_eq_euclidean_inner _ _
    rw [heq]
    exact hexpand k
  · intro h
    apply hout
    intro k
    have heq : faceDot (u k) g=⟪projectionEuclideanVector (u k),projectionEuclideanVector g⟫_ℝ :=
      faceDot_eq_euclidean_inner _ _
    simpa only [heq] using h k

theorem actualFacet_selectedStratumEvent_mem_originalOuterLayer {m q r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤b (e i)) ↔ ∀ k,faceDot (u k) y≤b k)
    (hu : ∀ k,vectorNormSq (u k)=1)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖) (a : Fin q × Fin q)
    {g : Vector r} (hg : g∈fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R a) :
    g∈fourthOuterLayer u b R :=
  actualFacet_selectedTube_mem_originalOuterLayer u b e hequiv hu R hR hRadd {a.1,a.2}
    (fourthStratumEvent_mem_tube _ _ R hR (fun i => hu (e i)) a hg)

theorem actualFacet_selectedEvent_indicator_sum_le_original {m q r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤b (e i)) ↔ ∀ k,faceDot (u k) y≤b k)
    (hu : ∀ k,vectorNormSq (u k)=1)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (P : Vector r → ℝ) (hP : ∀ g,0≤P g) (g : Vector r) :
    (∑ a : Fin q × Fin q,(fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R a).indicator P g)≤
      2*(fourthOuterLayer u b R).indicator P g := by
  classical
  by_cases hex : ∃ a,g∈fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R a
  · obtain ⟨a,ha⟩ := hex
    have horig := actualFacet_selectedStratumEvent_mem_originalOuterLayer u b e hequiv hu R hR hRadd a ha
    have hsel := fourthStratumEvent_mem_outerLayer (fun i => u (e i)) (fun i => b (e i)) R hR hRadd
      (fun i => hu (e i)) a ha
    simpa only [indicator_of_mem hsel,indicator_of_mem horig] using
      fourthStratumEvent_indicator_sum_le (fun i => u (e i)) (fun i => b (e i)) R hR hRadd
        (fun i => hu (e i)) P hP g
  · have hn a : g∉fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R a := fun h => hex ⟨a,h⟩
    simp only [indicator_of_not_mem (hn _),Finset.sum_const_zero]
    exact mul_nonneg (by norm_num) (indicator_nonneg (fun g _ => hP g) g)

theorem actualFacet_selectedEvent_integral_sum_le_original {m q r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤b (e i)) ↔ ∀ k,faceDot (u k) y≤b k)
    (hu : ∀ k,vectorNormSq (u k)=1)
    (R : EuclideanSpace ℝ (Fin r) → ℝ) (hRm : Continuous R) (hR : ∀ x,1≤R x)
    (hRadd : ∀ x d,R (x+d)≤R x+‖d‖)
    (hR4 : Integrable (fun g => fourthTransportRadius R g^4) (standardGaussian r)) :
    (∑ a : Fin q × Fin q,∫ g,
      (fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R a).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian r)≤
      2*(∫ g,(fourthOuterLayer u b R).indicator
        (fun g => fourthTransportRadius R g^4) g ∂standardGaussian r) := by
  classical
  have hi a := hR4.indicator (measurableSet_fourthStratumEvent (fun i => u (e i)) (fun i => b (e i)) R hRm a)
  rw [← integral_finset_sum Finset.univ (fun a _ => hi a),← integral_const_mul]
  exact integral_mono (integrable_finset_sum _ (fun a _ => hi a))
    ((hR4.indicator (measurableSet_fourthOuterLayer u b R hRm)).const_mul 2)
    (fun g => actualFacet_selectedEvent_indicator_sum_le_original u b e hequiv hu R hR hRadd _
      (fun _ => pow_nonneg (zero_le_one.trans (hR _)) 4) g)

end
end RectangleCLTArxivV1
