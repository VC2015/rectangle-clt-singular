import RectangleCLT.GlobalGaussianBoundary
import RectangleCLT.GaussianMaximum
import RectangleCLT.RectangleSmoothing

/-! Rectangle stability under an actual independent Gaussian perturbation.
The proof averages the deterministic boundary crossing estimate over the
Gaussian displacement. It uses the expected maximum, not a union tail. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators symmDiff

namespace RectangleCLT

noncomputable section

namespace FaceSmoother

theorem inside_symmDiff_shift_subset_boundary {p : ℕ} (s : FaceSmoother p)
    (v : Vector p) (hv : 0 < ‖v‖) :
    {x | s.Inside (x + v)} ∆ {x | s.Inside x} ⊆ s.boundaryLayer (2 * ‖v‖) := by
  intro x hx
  have hnormal (f : Face p) := abs_le.mp (abs_normalDot_le_of_norm_le f (le_refl ‖v‖))
  have hinside (y : Vector p) : s.Inside y ↔ y ∈ s.outerSet 0 := by
    simp only [Inside, faceScore, outerSet, mem_setOf_eq, add_zero]
    constructor <;> intro hy f hf <;> specialize hy f hf <;> linarith
  rcases Set.mem_symmDiff.mp hx with hx | hx
  · have hin := (hinside _).mp hx.1
    refine ⟨?_, ?_⟩
    · intro f hf
      have hb := hin f hf
      rw [normalDot_add] at hb
      have hn := hnormal f
      linarith
    · intro hinner
      apply hx.2
      apply (hinside _).mpr
      intro f hf
      have hb := hinner f hf
      linarith
  · have hin := (hinside _).mp hx.1
    refine ⟨?_, ?_⟩
    · intro f hf
      have hb := hin f hf
      linarith
    · intro hinner
      apply hx.2
      apply (hinside _).mpr
      intro f hf
      rw [normalDot_add]
      have hb := hinner f hf
      have hn := hnormal f
      linarith

theorem probability_shift_le_of_boundary {p : ℕ} (s : FaceSmoother p)
    (ρ : Measure (Vector p)) [IsProbabilityMeasure ρ] {K δ q : ℝ}
    (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hq : 0 ≤ q)
    (hboundary : ∀ d : ℝ, 0 < d →
      ρ.real (s.boundaryLayer d) ≤ K * (d + δ) * q) (v : Vector p) :
    |ρ.real {x | s.Inside (x + v)} - ρ.real {x | s.Inside x}| ≤
      K * (2 * ‖v‖ + δ) * q := by
  by_cases hv : v = 0
  · subst v
    simp only [add_zero, norm_zero, mul_zero, zero_add, sub_self, abs_zero]
    positivity
  have hvnorm : 0 < ‖v‖ := norm_pos_iff.mpr hv
  exact (abs_measureReal_sub_le_measureReal_symmDiff
    (s.measurableSet_Inside.preimage (measurable_id.add_const v)).nullMeasurableSet
    s.measurableSet_Inside.nullMeasurableSet).trans
      ((measureReal_mono (s.inside_symmDiff_shift_subset_boundary v hvnorm)).trans
        (hboundary _ (by positivity)))

end FaceSmoother

/-- A uniform boundary estimate gives a dimension-sharp bound for the
actual independent Gaussian perturbation. This is the common probability
bridge instantiated below with proved bounded and Gaussian concentration. -/
theorem gaussian_noise_stability_of_boundary {p : ℕ} (hp : 1 ≤ p)
    (ρ : Measure (Vector p)) [IsProbabilityMeasure ρ] {δ K ε : ℝ}
    (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hboundary : ∀ (s : FaceSmoother p) (d : ℝ), 0 < d →
      ρ.real (s.boundaryLayer d) ≤ K * (d + δ) * Real.sqrt (dimensionLog p))
    (R : Rect p) :
    |ρ.real R.carrier - (ρ.prod (standardGaussian p)).real
      {z | z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| ≤
        4 * K * (Real.sqrt ε * dimensionLog p + δ * Real.sqrt (dimensionLog p)) := by
  let q := Real.sqrt (dimensionLog p)
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hq2 : q * q = dimensionLog p := Real.mul_self_sqrt hL
  let ν := standardGaussian p
  have hId : gaussianLaw (1 : Matrix (Fin p) (Fin p) ℝ) = ν := by
    have hmul : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec = id := by
      funext x
      exact Matrix.one_mulVec x
    simp only [gaussianLaw, hmul, Measure.map_id, ν]
  let T : Vector p × Vector p → Vector p := fun z => z.1 + Real.sqrt ε • z.2
  have hT : Measurable T := measurable_fst.add (measurable_const.smul measurable_snd)
  let σ := (ρ.prod ν).map T
  letI : IsProbabilityMeasure σ := isProbabilityMeasure_map hT.aemeasurable
  have hσ (S : Rect p) : σ.real S.carrier =
      (ρ.prod ν).real {z | T z ∈ S.carrier} := by
    simp only [σ, Measure.real, Measure.map_apply hT S.measurableSet_carrier]
    rfl
  have hboxes (lo hi : Vector p) :
      |ρ.real (Rect.closedBox lo hi).carrier - σ.real (Rect.closedBox lo hi).carrier| ≤
        4 * K * (Real.sqrt ε * dimensionLog p + δ * q) := by
    let s := FaceSmoother.closedBox lo hi 1 (by norm_num)
    let E : Set (Vector p × Vector p) := {z | s.Inside (T z)}
    have hE : MeasurableSet E := s.measurableSet_Inside.preimage hT
    have hInd : Integrable (E.indicator (fun _ => (1 : ℝ))) (ρ.prod ν) :=
      (integrable_const (1 : ℝ)).indicator hE
    let f : Vector p → ℝ := fun z => ρ.real {x | s.Inside (x + Real.sqrt ε • z)}
    have hsection : (fun z => ∫ x, E.indicator (fun _ => (1 : ℝ)) (x,z) ∂ρ) = f := by
      funext z
      have hs : MeasurableSet {x : Vector p | s.Inside (x + Real.sqrt ε • z)} :=
        s.measurableSet_Inside.preimage (measurable_id.add_const (Real.sqrt ε • z))
      change (∫ x, {x | s.Inside (x + Real.sqrt ε • z)}.indicator
        (fun _ => (1 : ℝ)) x ∂ρ) = _
      rw [integral_indicator_const (1 : ℝ) hs, smul_eq_mul, mul_one]
    have hf : Integrable f ν := by
      rw [← hsection]
      exact hInd.integral_prod_right
    have hprob : (ρ.prod ν).real E = ∫ z, f z ∂ν := by
      calc
        _ = ∫ z, E.indicator (fun _ => (1 : ℝ)) z ∂ρ.prod ν := by
          rw [integral_indicator_const (1 : ℝ) hE, smul_eq_mul, mul_one]
        _ = _ := by rw [integral_prod_symm _ hInd, hsection]
    have hinside : {x | s.Inside x} = (Rect.closedBox lo hi).carrier := by
      ext x
      exact FaceSmoother.closedBox_Inside lo hi 1 (by norm_num) x
    have hσbox : σ.real (Rect.closedBox lo hi).carrier = (ρ.prod ν).real E := by
      rw [hσ]
      congr 1
      ext z
      exact (FaceSmoother.closedBox_Inside lo hi 1 (by norm_num) (T z)).symm
    have hpoint (z : Vector p) :
        |f z - ρ.real (s.Inside)| ≤ K * (2 * Real.sqrt ε * ‖z‖ + δ) * q := by
      have hb := s.probability_shift_le_of_boundary ρ hK hδ hq
        (hboundary s) (Real.sqrt ε • z)
      simpa only [f, norm_smul, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg ε),
        mul_assoc] using hb
    have hnorm : Integrable (fun z : Vector p => ‖z‖) ν := by
      rw [← hId]
      exact gaussianLaw_integrable_norm (1 : Matrix (Fin p) (Fin p) ℝ)
    have hmajor : Integrable (fun z : Vector p => K * (2 * Real.sqrt ε * ‖z‖ + δ) * q) ν :=
      (((hnorm.const_mul _).add (integrable_const _)).const_mul _).mul_const _
    have habs : |(∫ z, f z ∂ν) - ρ.real (s.Inside)| ≤
        ∫ z, K * (2 * Real.sqrt ε * ‖z‖ + δ) * q ∂ν := by
      have hconst : (∫ _z : Vector p, ρ.real (s.Inside) ∂ν) = ρ.real (s.Inside) := by simp
      rw [← hconst]
      rw [← integral_sub hf (integrable_const _)]
      exact abs_integral_le_integral_abs.trans
        (integral_mono (hf.sub (integrable_const _)).abs hmajor hpoint)
    have hmean : (∫ z : Vector p, ‖z‖ ∂ν) ≤ 2 * q := by
      rw [← hId]
      exact gaussianLaw_integral_norm_le hp
        (1 : Matrix (Fin p) (Fin p) ℝ) (by intro j; simp)
    have hcalc : (∫ z, K * (2 * Real.sqrt ε * ‖z‖ + δ) * q ∂ν) ≤
        4 * K * (Real.sqrt ε * dimensionLog p + δ * q) := by
      rw [integral_mul_const, integral_const_mul,
        integral_add (hnorm.const_mul _) (integrable_const _), integral_const_mul]
      simp only [integral_const, measureReal_univ_eq_one, one_smul]
      have hb := mul_le_mul_of_nonneg_left hmean (by positivity : 0 ≤ 2 * Real.sqrt ε)
      have hb' := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
        (add_le_add_right hb δ) hK) hq
      have heq : K * (2 * Real.sqrt ε * (2 * q) + δ) * q =
          4 * K * (Real.sqrt ε * dimensionLog p + δ * q) - 3 * K * δ * q := by
        rw [← hq2]
        ring
      rw [heq] at hb'
      have hpos : 0 ≤ 3 * K * δ * q := by positivity
      linarith only [hb', hpos]
    rw [hσbox, hprob, ← hinside, abs_sub_comm]
    exact habs.trans hcalc
  have hh := rectangle_abs_probability_le_of_closedBox hp ρ σ hboxes R
  simpa only [hσ, T, q, ν] using hh

/-- The probability bridge on the original sample space, for any actual
measurable vector whose translated boundary estimate has been proved. -/
theorem gaussian_noise_stability_map {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p) (hW : Measurable W)
    (hp : 1 ≤ p) {δ K ε : ℝ} (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hε : 0 ≤ ε)
    (hboundary : ∀ (s : FaceSmoother p) (d : ℝ), 0 < d →
      μ.real {ω | W ω ∈ s.boundaryLayer d} ≤
        K * (d + δ) * Real.sqrt (dimensionLog p)) (R : Rect p) :
    |μ.real {ω | W ω ∈ R.carrier} - (μ.prod (standardGaussian p)).real
      {z | W z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| ≤
        4 * K * (Real.sqrt ε * dimensionLog p + δ * Real.sqrt (dimensionLog p)) := by
  letI : IsProbabilityMeasure (μ.map W) := isProbabilityMeasure_map hW.aemeasurable
  have hbl (s : FaceSmoother p) (d : ℝ) (hd : 0 < d) :
      (μ.map W).real (s.boundaryLayer d) ≤ K * (d + δ) * Real.sqrt (dimensionLog p) := by
    simpa only [Measure.real, Measure.map_apply hW (s.measurableSet_boundaryLayer d),
      Set.preimage_setOf_eq] using hboundary s d hd
  have hb := gaussian_noise_stability_of_boundary hp (μ.map W) hδ hK hε hbl R
  have hprod : (μ.map W).prod (standardGaussian p) =
      (μ.prod (standardGaussian p)).map (Prod.map W id) := by
    simpa only [Measure.map_id] using
      (Measure.map_prod_map μ (standardGaussian p) hW measurable_id)
  have hs : MeasurableSet {z : Vector p × Vector p |
      z.1 + Real.sqrt ε • z.2 ∈ R.carrier} :=
    R.measurableSet_carrier.preimage
      (measurable_fst.add (measurable_const.smul measurable_snd))
  rw [hprod] at hb
  simpa only [Measure.real, Measure.map_apply hW R.measurableSet_carrier,
    Measure.map_apply (hW.prodMap measurable_id) hs, Set.preimage_setOf_eq,
    Prod.map_apply, id_eq] using hb

/-- Bounded independent observations are stable under actual independent
Gaussian noise. Unit coordinate variances suffice; the covariance may
have zero full eigenvalue and zero pair, triple, or quadruple eigenvalues. -/
theorem bounded_gaussian_noise_stability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p) {δ ε : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (hp : 1 ≤ p)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = 1) (hε : 0 ≤ ε) (R : Rect p) :
    |μ.real {ω | sumVector ξ ω ∈ R.carrier} - (μ.prod (standardGaussian p)).real
      {z | sumVector ξ z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| ≤
        (4 * 1073741824) *
          (Real.sqrt ε * dimensionLog p + δ * Real.sqrt (dimensionLog p)) := by
  apply gaussian_noise_stability_map μ (sumVector ξ) h.measurable_sum hp
    h.delta_nonneg (by norm_num) hε
  intro s d hd
  simpa only [add_zero, div_one] using h.boundary_probability_le hp
    (by norm_num : (0 : ℝ) < 1) hdiag s 0 hd

/-- The same actual perturbation estimate for a possibly singular
unit-diagonal Gaussian law has no observation-envelope term. -/
theorem gaussianLaw_gaussian_noise_stability {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (R : Rect p) :
    |(gaussianLaw A).real R.carrier - ((gaussianLaw A).prod (standardGaussian p)).real
      {z | z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| ≤
        (4 * 1073741824) * Real.sqrt ε * dimensionLog p := by
  have hb := gaussian_noise_stability_of_boundary hp (gaussianLaw A)
    (δ := 0) (K := 1073741824) (by norm_num) (by norm_num) hε (by
      intro s d hd
      simpa only [add_zero] using s.gaussian_boundary_probability_le_of_unit_variance
        hp A hdiag 0 hd) R
  simpa only [zero_mul, add_zero, mul_assoc] using hb

/-- Gaussian noise stability expressed using two genuine independent
standard Gaussian vectors and the stated covariance factor. -/
theorem gaussian_gaussian_noise_stability {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    {ε : ℝ} (hε : 0 ≤ ε) (R : Rect p) :
    |(standardGaussian p).real {z | A.mulVec z ∈ R.carrier} -
      ((standardGaussian p).prod (standardGaussian p)).real
        {z | A.mulVec z.1 + Real.sqrt ε • z.2 ∈ R.carrier}| ≤
        (4 * 1073741824) * Real.sqrt ε * dimensionLog p := by
  have hb := gaussian_noise_stability_map (standardGaussian p) A.mulVec
    (measurable_mulVec A) hp (δ := 0) (K := 1073741824)
    (by norm_num) (by norm_num) hε (by
      intro s d hd
      have hh := s.gaussian_boundary_probability_le_of_unit_variance hp A hdiag 0 hd
      simpa only [add_zero, gaussianLaw, Measure.real, Set.setOf_mem_eq,
        Measure.map_apply (measurable_mulVec A) (s.measurableSet_boundaryLayer d),
        Set.preimage_setOf_eq] using hh) R
  simpa only [zero_mul, add_zero, mul_assoc] using hb

end

end RectangleCLT
