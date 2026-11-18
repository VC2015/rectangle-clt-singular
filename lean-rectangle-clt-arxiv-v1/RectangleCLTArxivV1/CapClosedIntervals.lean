import RectangleCLTArxivV1.CapVarianceNormalization

/-! The zero-width endpoint of the actual projection concentration theorem. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
noncomputable section

theorem cap_one_projection_zero_width
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2}
    (hdata : BoundedIndependentHypotheses μ X 0)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c : ℝ} (hc : 0 < c)
    (hvar : c ≤ capMixedCovariance μ X A 0 0) (x : ℝ) :
    (μ.prod (standardGaussian r)).real {z | |capMixedValue X A z 0-x| ≤ 0} = 0 := by
  apply le_antisymm _ ENNReal.toReal_nonneg
  apply le_of_forall_pos_le_add
  intro ε hε
  let K := 8*capVarianceScale c*Real.sqrt (Real.pi/capGaussianExponent)
  have hs : 0 < Real.sqrt (Real.pi/capGaussianExponent) :=
    Real.sqrt_pos.mpr (div_pos Real.pi_pos capGaussianExponent_pos)
  have hK : 0 < K := by dsimp [K]; exact mul_pos (mul_pos (by norm_num) (capVarianceScale_pos hc)) hs
  have hw : 0 < ε/K := div_pos hε hK
  have hp := cap_one_projection_small_interval_of_lower_variance hdata A hc hvar hw hw.le x
  have hsub : {z | |capMixedValue X A z 0-x| ≤ 0} ⊆ {z | |capMixedValue X A z 0-x| ≤ ε/K} :=
    fun z hz => hz.trans hw.le
  have he : 8*capVarianceScale c*(ε/K)*Real.sqrt (Real.pi/capGaussianExponent) = ε := by
    calc
      _ = K*(ε/K) := by dsimp only [K]; ring
      _ = ε := by field_simp only [hK.ne']; ring
  exact (measureReal_mono hsub).trans (hp.trans_eq (by rw [he,zero_add]))

/-- Positive lower variance gives the interval bound also at width zero. -/
theorem cap_one_projection_small_interval_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c h : ℝ} (hc : 0 < c)
    (hvar : c ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 ≤ h) (hband : δ ≤ h) (x : ℝ) :
    (μ.prod (standardGaussian r)).real {z | |capMixedValue X A z 0-x| ≤ h} ≤
      8*capVarianceScale c*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  rcases eq_or_lt_of_le hh with he | hp
  · have hδ : δ = 0 := le_antisymm (by linarith) hdata.delta_nonneg
    subst h
    subst δ
    rw [cap_one_projection_zero_width hdata A hc hvar x]
    simp
  · exact cap_one_projection_small_interval_of_lower_variance hdata A hc hvar hp hband x

/-- The two-face estimate also includes width zero. Parallel faces remain
excluded exactly by the positive-angle premise. -/
theorem cap_two_projection_small_box_nonneg
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {c v ρ h : ℝ} (hc : 0 < c)
    (hv : c ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 ≤ h) (hband : 2*δ ≤ h) (x y : ℝ) :
    (μ.prod (standardGaussian r)).real {z |
      |capMixedValue X A z 0-x| ≤ h ∧ |capMixedValue X A z 1-y| ≤ h} ≤
      16*Real.pi^3*(capVarianceScale c)^2*h^2/Real.sqrt (1-ρ^2) := by
  rcases eq_or_lt_of_le hh with he | hp
  · have hδ : δ = 0 := le_antisymm (by linarith) hdata.delta_nonneg
    subst h
    subst δ
    have hvar : c ≤ capMixedCovariance μ X A 0 0 := by rw [hcov]; simpa using hv
    have heq := cap_one_projection_zero_width hdata A hc hvar x
    have hle := measureReal_mono (μ := μ.prod (standardGaussian r))
      (show {z | |capMixedValue X A z 0-x| ≤ 0 ∧ |capMixedValue X A z 1-y| ≤ 0} ⊆
        {z | |capMixedValue X A z 0-x| ≤ 0} from fun z hz => hz.1)
    rw [heq] at hle
    simpa using hle
  · exact cap_two_projection_small_box_of_lower_variance hdata A hc hv hρ hcov hp hband x y

end
end RectangleCLTArxivV1
