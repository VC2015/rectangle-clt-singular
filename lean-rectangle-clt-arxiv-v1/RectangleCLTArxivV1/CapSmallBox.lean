import RectangleCLTArxivV1.CapFrequencyBox

/-! The actual two-projection small-box estimate in Supplemental G.2.
The Fourier calculation is performed in the original two projections;
completing the Gaussian quadratic form is the equivalent linear-coordinate
calculation that displays the inverse angle. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT
open scoped BigOperators ComplexConjugate
noncomputable section

theorem cap_pair_quadratic_nonneg {ρ : ℝ} (hρ : ρ^2 < 1) (t : ℝ × ℝ) :
    0 ≤ t.1^2+2*ρ*t.1*t.2+t.2^2 := by
  have hp := mul_nonneg (show 0 ≤ 1-ρ^2 by linarith) (sq_nonneg t.1)
  nlinarith [sq_nonneg (t.2+ρ*t.1)]

/-- G.2 for actual bounded independent two-coordinate observations plus
an independent rectangular Gaussian image. Only the actual projected
covariance matrix occurs among the premises. -/
theorem cap_two_projection_small_box
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {v ρ h : ℝ}
    (hv : (1/2 : ℝ) ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 < h) (hband : 2*δ ≤ h) (x y : ℝ) :
    (μ.prod (standardGaussian r)).real {z |
      |capMixedValue X A z 0-x| ≤ h ∧ |capMixedValue X A z 1-y| ≤ h} ≤
        16*Real.pi^3*h^2/Real.sqrt (1-ρ^2) := by
  let V := capMixedValue X A
  let B := capFrequencySquare h
  let ν := ProbabilityTheory.cond volume B
  letI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (capFrequencySquare_volume_ne_zero hh) (capFrequencySquare_volume_ne_top hh)
  let χ : (ℝ × ℝ) × (Ω × Vector r) → ℂ :=
    fun z => unitPhase (capPairPhase x y z.1 (V z.2))
  let S : Set (Ω × Vector r) := {z | |V z 0-x| ≤ h ∧ |V z 1-y| ≤ h}
  have hVm : Measurable V :=
    (hdata.measurable_sum.comp measurable_fst).add
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)
  have hY0 := (measurable_pi_apply (0 : Fin 2)).comp hVm
  have hY1 := (measurable_pi_apply (1 : Fin 2)).comp hVm
  have hS : MeasurableSet S :=
    (measurableSet_le (hY0.sub_const x).abs measurable_const).inter
      (measurableSet_le (hY1.sub_const y).abs measurable_const)
  have hphase : Measurable (fun z : (ℝ × ℝ) × (Ω × Vector r) =>
      capPairPhase x y z.1 (V z.2)) := by
    unfold capPairPhase
    exact ((measurable_fst.comp measurable_fst).mul
      (((measurable_pi_apply (0 : Fin 2)).comp (hVm.comp measurable_snd)).sub_const x)).add
      ((measurable_snd.comp measurable_fst).mul
        (((measurable_pi_apply (1 : Fin 2)).comp (hVm.comp measurable_snd)).sub_const y))
  have hχ : Measurable χ := by
    dsimp only [χ,unitPhase]
    exact ((Complex.continuous_ofReal.measurable.comp hphase).mul_const Complex.I).cexp
  have hχb (z : (ℝ × ℝ) × (Ω × Vector r)) : ‖χ z‖ ≤ 1 := by
    dsimp only [χ]
    exact (norm_unitPhase _).le
  have hpos : ∀ z ∈ S, (1/2 : ℝ) ≤ (frequencyKernel ν χ z).re := by
    intro z hz
    change |V z 0-x| ≤ h ∧ |V z 1-y| ≤ h at hz
    apply realPhaseAverage_re_ge_half ν (fun t => capPairPhase x y t (V z))
      (by unfold capPairPhase; fun_prop)
    filter_upwards [ProbabilityTheory.ae_cond_mem (measurableSet_capFrequencySquare h)] with t ht
    exact abs_capPairPhase_le_one hh x y ht (V z) hz.1 hz.2
  have hdecay : ∀ s ∈ B, ∀ t ∈ B,
      ‖∫ z, χ (s,z)*conj (χ (t,z)) ∂μ.prod (standardGaussian r)‖ ≤ capPairMajorant ρ (s-t) := by
    intro s hs t ht
    let w := capPairWeight (s-t)
    have hhalf : ∀ i, ∀ᵐ ω ∂μ, |dotProduct w (X i ω)| ≤ 1/2 := by
      intro i
      filter_upwards [hdata.abs_coordinate_le i 0,hdata.abs_coordinate_le i 1] with ω h0 h1
      exact abs_capPairWeight_projection_le_half hh hdata.delta_nonneg hband hs ht (X i ω) h0 h1
    have hCF := norm_integral_unitPhase_mixed_le hdata A w hhalf
    have heq : ‖∫ z, χ (s,z)*conj (χ (t,z)) ∂μ.prod (standardGaussian r)‖ =
        ‖∫ z, unitPhase (dotProduct w (V z)) ∂μ.prod (standardGaussian r)‖ := by
      calc
        _ = ‖∫ z, unitPhase (dotProduct w (V z)-((s.1-t.1)*x+(s.2-t.2)*y))
            ∂μ.prod (standardGaussian r)‖ := by
          apply congrArg norm
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by
            dsimp only [χ]
            rw [← unitPhase_sub]
            congr 1
            simp only [capPairPhase,w,capPairWeight,dotProduct,Fin.sum_univ_two,
              Matrix.cons_val_zero,Matrix.cons_val_one,Prod.fst_sub,Prod.snd_sub]
            ring)
        _ = _ := norm_integral_unitPhase_sub_const _ _ _
    rw [heq]
    apply hCF.trans
    change Real.exp (-(2/Real.pi^2)*matrixQuadratic (capMixedCovariance μ X A) (capPairWeight (s-t))) ≤ _
    rw [cap_pair_matrixQuadratic hcov]
    unfold capPairMajorant
    apply Real.exp_le_exp.mpr
    have hq := cap_pair_quadratic_nonneg hρ (s-t)
    have hm := mul_le_mul_of_nonneg_right hv hq
    calc
      _ ≤ -(2/Real.pi^2)*((1/2)*( (s-t).1^2+2*ρ*(s-t).1*(s-t).2+(s-t).2^2)) :=
        mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (by positivity))
      _ = _ := by unfold capGaussianExponent; ring
  have hprob := probability_le_uniform_frequency_integral (volume : Measure (ℝ × ℝ))
    (μ.prod (standardGaussian r)) B (measurableSet_capFrequencySquare h)
    (capFrequencySquare_volume_ne_zero hh) (capFrequencySquare_volume_ne_top hh)
    χ hχ hχb (capPairMajorant ρ) (integrable_capPairMajorant hρ)
    (by unfold capPairMajorant; fun_prop) (capPairMajorant_nonneg ρ) (capPairMajorant_le_one hρ)
    S hS hpos hdecay
  have hvol : (volume B).toReal = 4*(capFrequencyRadius h)^2 := by
    rw [show B = capFrequencySquare h from rfl,volume_capFrequencySquare hh,
      ENNReal.toReal_ofReal (by positivity)]
  rw [integral_capPairMajorant_pi hρ,hvol] at hprob
  apply hprob.trans_eq
  unfold capFrequencyRadius
  have hν := (Real.sqrt_pos.mpr (show 0 < 1-ρ^2 by linarith)).ne'
  field_simp [hh.ne',hν]
  ring

/-- The one-projection counterpart of the same compact-frequency argument. -/
theorem cap_one_projection_small_interval
    {Ω : Type*} [MeasurableSpace Ω] {r n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {h : ℝ}
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 < h) (hband : δ ≤ h) (x : ℝ) :
    (μ.prod (standardGaussian r)).real {z | |capMixedValue X A z 0-x| ≤ h} ≤
      8*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  let V := capMixedValue X A
  let B := capFrequencyInterval h
  let ν := ProbabilityTheory.cond volume B
  letI : IsProbabilityMeasure ν := ProbabilityTheory.cond_isProbabilityMeasure_of_finite
    (capFrequencyInterval_volume_ne_zero hh) (capFrequencyInterval_volume_ne_top hh)
  let χ : ℝ × (Ω × Vector r) → ℂ := fun z => unitPhase (z.1*(V z.2 0-x))
  let S : Set (Ω × Vector r) := {z | |V z 0-x| ≤ h}
  have hVm : Measurable V :=
    (hdata.measurable_sum.comp measurable_fst).add
      ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd)
  have hY := (measurable_pi_apply (0 : Fin 2)).comp hVm
  have hS : MeasurableSet S := measurableSet_le (hY.sub_const x).abs measurable_const
  have hphase : Measurable (fun z : ℝ × (Ω × Vector r) => z.1*(V z.2 0-x)) :=
    measurable_fst.mul ((hY.comp measurable_snd).sub_const x)
  have hχ : Measurable χ := by
    dsimp only [χ,unitPhase]
    exact ((Complex.continuous_ofReal.measurable.comp hphase).mul_const Complex.I).cexp
  have hχb (z : ℝ × (Ω × Vector r)) : ‖χ z‖ ≤ 1 := by dsimp only [χ]; exact (norm_unitPhase _).le
  have ha := (capFrequencyRadius_pos hh).le
  have hpos : ∀ z ∈ S, (1/2 : ℝ) ≤ (frequencyKernel ν χ z).re := by
    intro z hz
    change |V z 0-x| ≤ h at hz
    apply realPhaseAverage_re_ge_half ν (fun t => t*(V z 0-x)) (by fun_prop)
    filter_upwards [ProbabilityTheory.ae_cond_mem (show MeasurableSet B from measurableSet_Icc)] with t ht
    have ht' : |t| ≤ capFrequencyRadius h := abs_le.mpr ht
    rw [abs_mul]
    have hm := mul_le_mul ht' hz (abs_nonneg _) ha
    have he : capFrequencyRadius h*h = 1/4 := by unfold capFrequencyRadius; field_simp; ring
    nlinarith
  have hdecay : ∀ s ∈ B, ∀ t ∈ B,
      ‖∫ z, χ (s,z)*conj (χ (t,z)) ∂μ.prod (standardGaussian r)‖ ≤ capSingleMajorant (s-t) := by
    intro s hs t ht
    have hfreq : |s-t| ≤ 2*capFrequencyRadius h :=
      (abs_sub _ _).trans (by linarith [abs_le.mpr hs,abs_le.mpr ht])
    let w : Vector 2 := ![s-t,0]
    have hdot (v : Vector 2) : dotProduct w v = (s-t)*v 0 := by simp [dotProduct,w,Fin.sum_univ_two]
    have hhalf : ∀ i, ∀ᵐ ω ∂μ, |dotProduct w (X i ω)| ≤ 1/2 := by
      intro i
      filter_upwards [hdata.abs_coordinate_le i 0] with ω h0
      rw [hdot,abs_mul]
      have hm := mul_le_mul hfreq h0 (abs_nonneg _) (by positivity : 0 ≤ 2*capFrequencyRadius h)
      have he : 2*capFrequencyRadius h*δ = δ/(2*h) := by unfold capFrequencyRadius; field_simp; ring
      have hd : δ/(2*h) ≤ 1/2 := (div_le_iff₀ (by positivity : 0 < 2*h)).mpr (by linarith)
      nlinarith
    have hCF := norm_integral_unitPhase_mixed_le hdata A w hhalf
    have heq : ‖∫ z, χ (s,z)*conj (χ (t,z)) ∂μ.prod (standardGaussian r)‖ =
        ‖∫ z, unitPhase (dotProduct w (V z)) ∂μ.prod (standardGaussian r)‖ := by
      calc
        _ = ‖∫ z, unitPhase (dotProduct w (V z)-(s-t)*x) ∂μ.prod (standardGaussian r)‖ := by
          apply congrArg norm
          apply integral_congr_ae
          exact ae_of_all _ (fun z => by
            dsimp only [χ]
            rw [← unitPhase_sub]
            congr 1
            rw [hdot]
            ring)
        _ = _ := norm_integral_unitPhase_sub_const _ _ _
    rw [heq]
    apply hCF.trans
    have hquad : matrixQuadratic (capMixedCovariance μ X A) w =
        capMixedCovariance μ X A 0 0*(s-t)^2 := by
      simp only [matrixQuadratic,w,Fin.sum_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,mul_zero,zero_mul,add_zero,zero_add]
      ring
    rw [hquad]
    unfold capSingleMajorant
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_right hvar (sq_nonneg (s-t))
    calc
      _ ≤ -(2/Real.pi^2)*((1/2)*(s-t)^2) := mul_le_mul_of_nonpos_left hm (neg_nonpos.mpr (by positivity))
      _ = _ := by unfold capGaussianExponent; ring
  have hprob := probability_le_uniform_frequency_integral (volume : Measure ℝ)
    (μ.prod (standardGaussian r)) B (show MeasurableSet B from measurableSet_Icc)
    (capFrequencyInterval_volume_ne_zero hh) (capFrequencyInterval_volume_ne_top hh)
    χ hχ hχb capSingleMajorant integrable_capSingleMajorant
    (by unfold capSingleMajorant; fun_prop) capSingleMajorant_nonneg capSingleMajorant_le_one
    S hS hpos hdecay
  have hvol : (volume B).toReal = 2*capFrequencyRadius h := by
    rw [show B = capFrequencyInterval h from rfl,volume_capFrequencyInterval hh,
      ENNReal.toReal_ofReal (by positivity)]
  rw [integral_capSingleMajorant,hvol] at hprob
  apply hprob.trans_eq
  unfold capFrequencyRadius
  field_simp [hh.ne']
  ring

end
end RectangleCLTArxivV1
