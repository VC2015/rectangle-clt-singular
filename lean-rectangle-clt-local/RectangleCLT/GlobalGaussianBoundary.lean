import RectangleCLT.GaussianComponentClosureCoupling
import RectangleCLT.GaussianComponentClosureLimits
import RectangleCLT.ConcentrationFinal
import RectangleCLT.ConcentrationShift
import RectangleCLT.SmootherStability

/-! Gaussian rectangle boundary concentration from actual bounded
approximations. Exact covariance restoration permits the already proved
bounded concentration theorem to pass to a Gaussian limit, including
singular full covariance. No correlation gap or Gaussian CLT is assumed. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.FaceSmoother

noncomputable section

variable {p : ℕ} (s : FaceSmoother p)

theorem boundaryLayer_of_norm_coupling (W V r : Vector p) {d ε : ℝ}
    (hclose : ‖W - V‖ ≤ ε) (hW : W + r ∈ s.boundaryLayer d) :
    V + r ∈ s.boundaryLayer (d + ε) := by
  have hnormal (f : Face p) := abs_le.mp (abs_normalDot_le_of_norm_le f hclose)
  have hlinear (f : Face p) :
      normalDot f (W + r) = normalDot f (V + r) + normalDot f (W - V) := by
    have heq : W + r = (V + r) + (W - V) := by
      ext j
      simp only [Pi.add_apply, Pi.sub_apply]
      ring
    rw [heq, normalDot_add]
  refine ⟨?_, ?_⟩
  · intro f hf
    have hb := hW.1 f hf
    have hn := hnormal f
    rw [hlinear] at hb
    linarith
  · intro hinner
    apply hW.2
    intro f hf
    have hb := hinner f hf
    have hn := hnormal f
    rw [hlinear]
    linarith

theorem boundary_probability_le_of_norm_coupling
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (W V : Ω → Vector p) (r : Vector p) (d ε : ℝ) :
    μ.real {ω | W ω + r ∈ s.boundaryLayer d} ≤
      μ.real {ω | V ω + r ∈ s.boundaryLayer (d + ε)} +
        μ.real {ω | ε < ‖W ω - V ω‖} := by
  have hsub : {ω | W ω + r ∈ s.boundaryLayer d} ⊆
      {ω | V ω + r ∈ s.boundaryLayer (d + ε)} ∪
        {ω | ε < ‖W ω - V ω‖} := by
    intro ω hω
    by_cases hbad : ε < ‖W ω - V ω‖
    · exact Or.inr hbad
    · exact Or.inl (s.boundaryLayer_of_norm_coupling (W ω) (V ω) r
        (le_of_not_gt hbad) hω)
  exact (measureReal_mono hsub).trans (measureReal_union_le _ _)

/-- A singular centered Gaussian with common positive coordinate variance has the
usual rectangle boundary bound. The constant comes from the proved
bounded-sum concentration theorem and is universal. -/
theorem gaussian_boundary_probability_le_of_variance
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, (A * A.transpose) j j = v)
    (r : Vector p) {d : ℝ} (hd : 0 < d) :
    (gaussianLaw A).real {z | z + r ∈ s.boundaryLayer d} ≤
      1073741824 * d * Real.sqrt (dimensionLog p / v) := by
  let μ : Measure Unit := Measure.dirac ()
  let ξ : Fin 0 → Unit → Vector p := fun i => Fin.elim0 i
  have hξ : BoundedIndependentHypotheses μ ξ 0 := by
    refine ⟨(fun i => Fin.elim0 i), iIndepFun.of_subsingleton,
      (fun i => Fin.elim0 i), (fun i => Fin.elim0 i), le_rfl⟩
  have hξcov : covariance μ (sumVector ξ) = 0 := by
    ext j k
    simp [covariance, sumVector]
  let M := gaussianComponentFourthMoment A
  let e : ℕ → ℝ := fun k => p * Real.sqrt (M / (k : ℝ) ^ 4)
  let b : ℕ → ℝ := gaussianComponentEnvelopeUpper 0 M
  let q : ℕ → ℝ := fun k => M / (k : ℝ) ^ 2
  have hfinite (k : ℕ) (hk : 1 ≤ k) :
      (gaussianLaw A).real {z | z + r ∈ s.boundaryLayer d} ≤
        1073741824 * (d + e k + b k) * Real.sqrt (dimensionLog p / v) + q k := by
    have hk0 : k ≠ 0 := by omega
    let νraw := Measure.pi (gaussianComponentRawMarginal μ ξ A k)
    let ν := Measure.pi (gaussianComponentRestoredMarginal μ ξ A k)
    let η := gaussianComponentRestoredArray (p := p) (n := 0) k
    let W := gaussianComponentRawOriginalSum (p := p) (n := 0) k
    let V := gaussianComponentRawRestoredSum (p := p) (n := 0) k
    letI (i : Fin 0 ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
        IsProbabilityMeasure (gaussianComponentRawMarginal μ ξ A k i) :=
      gaussianComponentRawMarginal_isProbability μ ξ hξ.measurable A k i
    letI (i : Fin 0 ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
        IsProbabilityMeasure (gaussianComponentRestoredMarginal μ ξ A k i) :=
      gaussianComponentRestoredMarginal_isProbability μ ξ hξ.measurable A k i
    have hη := gaussianComponentRestoredArray_boundedIndependent μ ξ hξ hp A hk0
    have hηdiag : ∀ j, covariance ν (sumVector η) j j = v := by
      rw [gaussianComponentRestoredArray_covariance μ ξ hξ hp A hk0, hξcov, zero_add]
      exact hdiag
    have he0 : 0 ≤ e k := mul_nonneg (Nat.cast_nonneg _) (Real.sqrt_nonneg _)
    have hbase := hη.boundary_probability_le hp hv
      hηdiag s r (by linarith : 0 < d + e k)
    have hbase' : ν.real {z | sumVector η z + r ∈ s.boundaryLayer (d + e k)} ≤
        1073741824 * (d + e k + b k) * Real.sqrt (dimensionLog p / v) := by
      simpa only [b, gaussianComponentEnvelopeUpper, M,
        gaussianComponentRestorationError] using hbase
    have hWlaw : νraw.map W = gaussianLaw A := by
      rw [gaussianComponentRawOriginalSum_law μ ξ hξ.measurable hξ.independent A hk0]
      have hzero : μ.map (sumVector ξ) = Measure.dirac (0 : Vector p) := by
        have heq : sumVector ξ = fun _ : Unit => (0 : Vector p) := by
          funext ω
          simp [sumVector]
        rw [heq]
        simp
      rw [hzero, Measure.dirac_prod]
      rw [Measure.map_map (measurable_fst.add measurable_snd)
        (show Measurable (Prod.mk (0 : Vector p) : Vector p → Vector p × Vector p)
          from measurable_const.prodMk measurable_id)]
      simp only [Function.comp_def, zero_add, Measure.map_id]
      exact Measure.map_id
    have hVlaw : νraw.map V = ν.map (sumVector η) :=
      gaussianComponentRawRestoredSum_law μ ξ hξ.measurable A k
    have hWprob : νraw.real {z | W z + r ∈ s.boundaryLayer d} =
        (gaussianLaw A).real {z | z + r ∈ s.boundaryLayer d} := by
      rw [← s.boundary_probability_map νraw W (measurable_gaussianComponentRawOriginalSum k), hWlaw]
    have hVprob : νraw.real {z | V z + r ∈ s.boundaryLayer (d + e k)} =
        ν.real {z | sumVector η z + r ∈ s.boundaryLayer (d + e k)} := by
      rw [← s.boundary_probability_map νraw V (measurable_gaussianComponentRawRestoredSum k),
        hVlaw, s.boundary_probability_map ν (sumVector η) (by
          change Measurable (sumVector (gaussianComponentRestoredArray (p := p) (n := 0) k))
          unfold sumVector gaussianComponentRestoredArray
          exact Finset.measurable_sum _ fun _ _ => measurable_pi_apply _)]
    have hcouple := s.boundary_probability_le_of_norm_coupling νraw W V r d (e k)
    rw [hWprob, hVprob] at hcouple
    have hbad : νraw.real {z | e k < ‖W z - V z‖} ≤ q k := by
      simpa only [e, q, M, gaussianComponentRestorationError] using
        gaussianComponentRaw_norm_coupling μ ξ hξ.measurable hp A hk0
    exact hcouple.trans (add_le_add hbase' hbad)
  have helim : Tendsto e atTop (𝓝 0) := by
    have hh := ((gaussianComponent_const_div_pow_tendsto_zero M
      (by decide : 0 < 4)).sqrt).const_mul (p : ℝ)
    simpa only [e, Real.sqrt_zero, mul_zero] using hh
  have hblim : Tendsto b atTop (𝓝 0) :=
    gaussianComponentEnvelopeUpper_tendsto 0 M le_rfl
  have hqlim : Tendsto q atTop (𝓝 0) :=
    gaussianComponent_const_div_pow_tendsto_zero M (by decide : 0 < 2)
  have hlim := ((((tendsto_const_nhds (x := d)).add helim).add hblim).const_mul
    (1073741824 : ℝ)).mul_const (Real.sqrt (dimensionLog p / v))
  have heventual : ∀ᶠ k : ℕ in atTop,
      (gaussianLaw A).real {z | z + r ∈ s.boundaryLayer d} ≤
        1073741824 * (d + e k + b k) * Real.sqrt (dimensionLog p / v) + q k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact hfinite k hk
  simpa only [add_zero] using ge_of_tendsto (hlim.add hqlim) heventual

theorem gaussian_boundary_probability_le
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (r : Vector p) {d : ℝ} (hd : 0 < d) :
    (gaussianLaw A).real {z | z + r ∈ s.boundaryLayer d} ≤
      1073741824 * d * Real.sqrt (dimensionLog p) := by
  simpa only [div_one] using s.gaussian_boundary_probability_le_of_variance hp A
    (by norm_num : (0 : ℝ) < 1) hdiag r hd

/-- The same Gaussian boundary cap holds after adding an arbitrary
independent measurable vector. No moments of the extra shift are needed. -/
theorem gaussian_independent_shift_boundary_probability_le_of_variance
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (V : Ω → Vector p) (hV : Measurable V)
    (hp : 1 ≤ p) (A : Matrix (Fin p) (Fin p) ℝ)
    {v : ℝ} (hv : 0 < v) (hdiag : ∀ j, (A * A.transpose) j j = v)
    (r : Vector p) {d : ℝ} (hd : 0 < d) :
    ((gaussianLaw A).prod μ).real
        {z | z.1 + V z.2 + r ∈ s.boundaryLayer d} ≤
      1073741824 * d * Real.sqrt (dimensionLog p / v) := by
  have hh := s.boundary_probability_independent_shift_le (gaussianLaw A) μ
    id measurable_id (fun ω => V ω + r) (hV.add_const r) d
    (1073741824 * d * Real.sqrt (dimensionLog p / v))
    (fun a => s.gaussian_boundary_probability_le_of_variance hp A hv hdiag a hd)
  simpa only [id_eq, add_assoc] using hh

end

end RectangleCLT.FaceSmoother
