import RectangleCLTCompanion.RademacherCriticalScale
import RectangleCLTCompanion.LowerEsscherTailLimit
import RectangleCLTCompanion.WeightedGaussianTailLimits
import RectangleCLTCompanion.LowerMaxCDFProduct

/-! # The actual critical Rademacher moderate tail

The Esscher identity and the checked scalar Berry--Esseen theorem give the
relative tail limit directly, including the lattice distribution.
-/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology

namespace RectangleCLT.Companion

noncomputable section

lemma lowerCoordinateCDF_strict_tail (B : ℝ) (n : ℕ) (x : ℝ) :
    (lowerScalarArrayLaw B n).real {z | x < lowerScalarNormalizedSum z} =
      1-lowerCoordinateCDF B n x := by
  have hs : MeasurableSet {z : Fin n → ℝ | lowerScalarNormalizedSum z ≤ x} := by
    apply measurableSet_le _ measurable_const
    unfold lowerScalarNormalizedSum
    fun_prop
  have hc : {z : Fin n → ℝ | x < lowerScalarNormalizedSum z} =
      {z | lowerScalarNormalizedSum z ≤ x}ᶜ := by ext z; simp
  rw [hc, measureReal_compl hs]
  simp only [measureReal_univ_eq_one, lowerCoordinateCDF]

lemma tendsto_rademacherCritical_tail_ratio {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (1-lowerCoordinateCDF 1 n (normalMaxThreshold (p n))) /
      standardNormalUpperTail (normalMaxThreshold (p n)))
      atTop (𝓝 (Real.exp (-a^2/3))) := by
  have hx := tendsto_normalMaxThreshold_atTop.comp (criticalDimension_tendsto ha hcrit)
  have hs : Tendsto (fun n => lowerTiltedTailParameter 1 (rademacherCriticalTilt p n) n)
      atTop atTop := by
    convert tendsto_rademacherCriticalScale_atTop ha hcrit using 1
    funext n
    unfold lowerTiltedTailParameter rademacherCriticalScale
    ring
  have hsx : Tendsto (fun n => lowerTiltedTailParameter 1 (rademacherCriticalTilt p n) n /
      normalMaxThreshold (p n)) atTop (𝓝 1) := by
    simpa only [lowerTiltedTailParameter, rademacherCriticalScale, mul_assoc] using
      tendsto_rademacherCriticalScale_div_threshold ha hcrit
  have hJ := tendsto_normalWeightedTail_ratio hs hx hsx
  have ht : ∀ᶠ n in atTop, 0 < rademacherCriticalTilt p n := by
    filter_upwards [rademacherCriticalU_eventually_mem ha hcrit] with n hn
    exact rademacherTiltParameter_pos hn
  have hsmall : Tendsto (fun n => (1 : ℝ) * rademacherCriticalTilt p n) atTop (𝓝 0) := by
    simpa only [one_mul] using tendsto_rademacherCriticalTilt ha hcrit
  have hκ : Tendsto (fun n : ℕ => (n : ℝ)*cgf id (lowerTwoPointLaw 1) (rademacherCriticalTilt p n) -
      rademacherCriticalTilt p n * ((n : ℝ)*lowerTiltMean 1 (rademacherCriticalTilt p n)) +
      (normalMaxThreshold (p n))^2/2) atTop (𝓝 (-a^2/3)) := by
    apply (tendsto_rademacherCritical_exponent ha hcrit).congr'
    filter_upwards [rademacherCriticalU_eventually_mem ha hcrit] with n hn
    have hu : rademacherCriticalU p n ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hn.1], hn.2⟩
    have he := rademacher_esscher_exponent hu
    have hm := lowerTiltMean_rademacher hu
    change (normalMaxThreshold (p n))^2/2 - (n : ℝ)*rademacherRateFunction (rademacherCriticalU p n) = _
    unfold cgf
    change _ = (n : ℝ)*Real.log (mgf id (lowerTwoPointLaw 1) (rademacherTiltParameter (rademacherCriticalU p n))) -
      rademacherTiltParameter (rademacherCriticalU p n) * ((n : ℝ)*lowerTiltMean 1 (rademacherTiltParameter (rademacherCriticalU p n))) + _
    rw [hm]
    nlinarith [he]
  have hh := lower_esscher_relative_tail_tendsto (B := fun _ => 1)
    (t := rademacherCriticalTilt p) (x := fun n => normalMaxThreshold (p n)) (N := id)
    (Eventually.of_forall (fun _ => le_rfl)) (eventually_ge_atTop 1) ht
    (hs.eventually (eventually_ge_atTop 1)) hsmall hκ hJ
  apply hh.congr'
  filter_upwards [rademacherCriticalU_eventually_mem ha hcrit, eventually_ge_atTop 1] with n hu hn
  have hmem : rademacherCriticalU p n ∈ Ioo (-1 : ℝ) 1 := ⟨by linarith [hu.1], hu.2⟩
  have hmean := lowerTiltMean_rademacher hmem
  have hspos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 (by exact_mod_cast hn)
  have hmean' : (n : ℝ)*lowerTiltMean 1 (rademacherCriticalTilt p n) =
      normalMaxThreshold (p n) * Real.sqrt n := by
    rw [show rademacherCriticalTilt p n = rademacherTiltParameter (rademacherCriticalU p n) from rfl, hmean]
    unfold rademacherCriticalU
    field_simp
    nlinarith [congrArg (fun v : ℝ => normalMaxThreshold (p n)*v)
      (Real.sq_sqrt (Nat.cast_nonneg n))]
  have hevent : {z : Fin n → ℝ | (n : ℝ)*lowerTiltMean 1 (rademacherCriticalTilt p n) < lowerScalarSum z} =
      {z | normalMaxThreshold (p n) < lowerScalarNormalizedSum z} := by
    ext z
    rw [mem_setOf_eq, mem_setOf_eq, hmean']
    unfold lowerScalarNormalizedSum lowerScalarSum
    exact (lt_div_iff₀ hspos).symm
  change (lowerScalarArrayLaw 1 n).real _ / _ = _
  simp only [id_eq]
  rw [hevent, lowerCoordinateCDF_strict_tail]

lemma tendsto_rademacherCritical_tail_count {p : ℕ → ℕ} {a : ℝ} (ha : 0 < a)
    (hcrit : Tendsto (fun n : ℕ => Real.log (p n : ℝ) / Real.sqrt n) atTop (𝓝 a)) :
    Tendsto (fun n : ℕ => (p n : ℝ)*(1-lowerCoordinateCDF 1 n (normalMaxThreshold (p n))))
      atTop (𝓝 (Real.exp (-a^2/3))) := by
  have htail := tendsto_rademacherCritical_tail_ratio ha hcrit
  have hnormal := tendsto_mul_standardNormalUpperTail_normalMaxThreshold.comp (criticalDimension_tendsto ha hcrit)
  have hh := htail.mul hnormal
  simp only [mul_one] at hh
  apply hh.congr
  intro n
  simp only [Function.comp_def]
  field_simp [(standardNormalUpperTail_pos (normalMaxThreshold (p n))).ne']
  <;> ring

end

end RectangleCLT.Companion
