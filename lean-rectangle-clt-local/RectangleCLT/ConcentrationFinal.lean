import RectangleCLT.RectangleConcentration
import RectangleCLT.BoundedMaximumScaling

/-! Rectangle boundary concentration deduced from the proved Kane coupling,
conditional crossing estimate, fourth moments, and Markov's inequality. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.BoundedIndependentHypotheses

/-- Rectangle boundary concentration, uniformly over fixed translations.
The universal constant is explicit and deliberately not optimized. -/
theorem boundary_probability_le
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ]
    {ξ : Fin n → Ω → Vector p} {η v d : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (r : Vector p) (hd : 0 < d) :
    μ.real {ω | sumVector ξ ω + r ∈ s.boundaryLayer d} ≤
      1073741824 * (d + η) * Real.sqrt (dimensionLog p / v) := by
  let L := dimensionLog p
  let q := Real.sqrt L
  let w := Real.sqrt v
  let u := d + η
  let t := 2048 * u / w
  have hL : 1 ≤ L := log_exp_mul_nat_ge_one hp
  have hq : 0 < q := Real.sqrt_pos.mpr (by linarith)
  have hq1 : 1 ≤ q := by
    have hh := Real.sqrt_le_sqrt hL
    simpa only [Real.sqrt_one] using hh
  have hw : 0 < w := Real.sqrt_pos.mpr hv
  have hu : 0 < u := add_pos_of_pos_of_nonneg hd h.delta_nonneg
  have ht : 0 < t := div_pos (mul_pos (by norm_num) hu) hw
  have hw2 : w ^ 2 = v := Real.sq_sqrt hv.le
  have hq2 : q ^ 2 = L := Real.sq_sqrt (by linarith)
  have htw : t * w = 2048 * u := by dsimp [t]; field_simp
  have hrate : (d + η) * Real.sqrt (dimensionLog p / v) = u * q / w := by
    rw [Real.sqrt_div (by linarith : 0 ≤ dimensionLog p)]
    dsimp [u, q, w, L]
    ring
  rw [show 1073741824 * (d + η) * Real.sqrt (dimensionLog p / v) =
    1073741824 * ((d + η) * Real.sqrt (dimensionLog p / v)) by ring, hrate]
  have htq : t * q = 2048 * (u * q / w) := by dsimp [t]; ring
  by_cases hbig : 1 ≤ t * q
  · have hprob : μ.real {ω | sumVector ξ ω + r ∈ s.boundaryLayer d} ≤ 1 := by
      simpa only [measureReal_univ_eq_one] using
        (measureReal_mono (μ := μ)
          (Set.subset_univ {ω | sumVector ξ ω + r ∈ s.boundaryLayer d}))
    have hR : 0 ≤ u * q / w := le_of_lt (div_pos (mul_pos hu hq) hw)
    linarith
  have hsmall : t * q < 1 := lt_of_not_ge hbig
  have ht1 : t < 1 := (le_mul_of_one_le_right ht.le hq1).trans_lt hsmall
  let θ := t ^ 2
  let M := 4 * u / θ
  have hθ : 0 < θ := sq_pos_of_pos ht
  have hθone : θ ≤ 1 := by dsimp [θ]; nlinarith
  have hM : 0 < M := div_pos (mul_pos (by norm_num) hu) hθ
  have hθM : θ * M = 4 * u := by dsimp [M]; field_simp
  have hsqrtv : Real.sqrt (θ * v) = t * w := by
    rw [Real.sqrt_mul hθ.le]
    simp only [θ, Real.sqrt_sq ht.le]
    rfl
  have hsqrtL : Real.sqrt (θ * dimensionLog p) = t * q := by
    rw [Real.sqrt_mul hθ.le]
    simp only [θ, Real.sqrt_sq ht.le]
    rfl
  have hscale : η ≤ Real.sqrt (θ * v) := by
    rw [hsqrtv, htw]
    dsimp [u]
    linarith [h.delta_nonneg]
  have hgap : 2 * d + θ * M < Real.sqrt (θ * v) / 256 := by
    rw [hθM, hsqrtv, htw]
    dsimp [u]
    linarith [h.delta_nonneg]
  have hsecond (j : Fin p) : (∑ i, ∫ ω, (ξ i ω j) ^ 2 ∂μ) = v := by
    simpa only [pow_two] using (h.covariance_sum j j).symm.trans (hdiag j)
  have hb := s.boundary_probability_le_noise_add_tail μ ξ h.measurable h.independent r hp
    θ hθ hθone h.delta_nonneg hv h.abs_coordinate_le h.centered hsecond hscale hgap
  rw [hsqrtL] at hb
  have hηq : η * q ≤ w := by
    have huu : η ≤ u := by dsimp [u]; linarith
    have hh : 2048 * u * q < w := by
      have hh := (div_lt_one hw).mp (show (2048 * u * q) / w < 1 by
        simpa only [t, div_mul_eq_mul_div] using hsmall)
      exact hh
    have huq : 0 ≤ u * q := (mul_pos hu hq).le
    nlinarith [mul_le_mul_of_nonneg_right huu hq.le]
  have hmax : 2 * w * q + 2 * η * L ≤ 4 * w * q := by
    nlinarith [mul_le_mul_of_nonneg_right hηq hq.le]
  have htail := h.norm_sum_tail_le_of_variance hp hv hdiag hM
  have htail' : μ.real {ω | M < ‖sumVector ξ ω‖} ≤ 2048 * (t * q) := by
    apply htail.trans
    apply (div_le_iff₀ hM).mpr
    change 2 * w * q + 2 * η * L ≤ 2048 * (t * q) * M
    have heq : 2048 * (t * q) * M = 4 * w * q := by
      dsimp [M, θ]
      have hu_eq : u = t * w / 2048 := by
        apply (eq_div_iff (by norm_num : (2048 : ℝ) ≠ 0)).mpr
        linarith only [htw]
      rw [hu_eq]
      field_simp [ht.ne']
      ring
    rw [heq]
    exact hmax
  have hR : 0 ≤ u * q / w := le_of_lt (div_pos (mul_pos hu hq) hw)
  rw [htq] at hb htail'
  linarith

end RectangleCLT.BoundedIndependentHypotheses
