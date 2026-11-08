import RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section
local instance (n : ℕ) : NeZero (n + 2) := ⟨by omega⟩

def normalizedGaussianMaximum (n : ℕ) (z : Vector (n + 2)) : ℝ :=
  finiteMaximum z / Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ))

theorem measurable_normalizedGaussianMaximum (n : ℕ) :
    Measurable (normalizedGaussianMaximum n) :=
  (measurable_finiteMaximum (fun j (z : Vector (n + 2)) => z j)
    (fun j => measurable_pi_apply j)).div_const _

/-- Concentration in probability of the actual normalized maxima. The
sample-space dimension varies with the index; the probabilities are always
computed under the corresponding genuine finite product Gaussian law. -/
theorem normalizedGaussianMaximum_tendsto_in_probability {ε : ℝ} (hε : 0 < ε) :
    Tendsto (fun n : ℕ => (standardGaussian (n + 2)).real
      {z | ε < |normalizedGaussianMaximum n z - 1|}) atTop (𝓝 0) := by
  let δ := min (ε / 4) (1 / 4 : ℝ)
  have hδ : 0 < δ := lt_min (by positivity) (by norm_num)
  have hδquarter : δ ≤ (1 / 4 : ℝ) := min_le_right _ _
  have hεδ : 4 * δ ≤ ε := by have h := min_le_left (ε / 4) (1 / 4 : ℝ); dsimp [δ]; linarith
  have hshift : Tendsto (fun n : ℕ => n + 2) atTop atTop :=
    tendsto_atTop_mono (fun n => by change n ≤ n + 2; omega) tendsto_id
  have hratio := tendsto_printedNormalMaxThreshold_div_sqrt_two_log.comp hshift
  have hnear : ∀ᶠ n : ℕ in atTop,
      1 - δ ≤ printedNormalMaxThreshold (n + 2) / Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ)) ∧
      printedNormalMaxThreshold (n + 2) / Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ)) ≤ 1 + δ := by
    filter_upwards [hratio.eventually (eventually_gt_nhds (by linarith : 1 - δ < (1 : ℝ))),
      hratio.eventually (eventually_lt_nhds (by linarith : (1 : ℝ) < 1 + δ))] with n hnlo hnhi
    exact ⟨hnlo.le, hnhi.le⟩
  have hbelow := (tendsto_normalMaximumCDF_below_printed_threshold
    (by linarith : 0 < 1 - δ) (by linarith : 1 - δ < 1)).comp hshift
  have habove := (tendsto_normalMaximumCDF_tail_above_printed_threshold
    (by linarith : 1 < 1 + δ)).comp hshift
  have hsum : Tendsto (fun n : ℕ => normalMaximumCDF (n + 2) ((1 - δ) * printedNormalMaxThreshold (n + 2)) +
      (1 - normalMaximumCDF (n + 2) ((1 + δ) * printedNormalMaxThreshold (n + 2)))) atTop (𝓝 0) := by
    simpa only [zero_add] using hbelow.add habove
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
  · exact Eventually.of_forall (fun _ => measureReal_nonneg)
  · filter_upwards [hnear] with n hn
    let s := Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ))
    let u := printedNormalMaxThreshold (n + 2)
    have hs : 0 < s := Real.sqrt_pos.mpr (mul_pos (by norm_num)
      (Real.log_pos (by exact_mod_cast (show 1 < n + 2 by omega))))
    have hsub : {z : Vector (n + 2) | ε < |normalizedGaussianMaximum n z - 1|} ⊆
        {z | finiteMaximum z ≤ (1 - δ) * u} ∪ {z | (1 + δ) * u < finiteMaximum z} := by
      intro z hz
      change finiteMaximum z ≤ (1 - δ) * u ∨ (1 + δ) * u < finiteMaximum z
      by_contra hnot
      have hno := not_or.mp hnot
      have hlo : (1 - δ) * u ≤ finiteMaximum z := (lt_of_not_ge hno.1).le
      have hhi : finiteMaximum z ≤ (1 + δ) * u := le_of_not_gt hno.2
      have hl : (1 - δ) * (u / s) ≤ normalizedGaussianMaximum n z := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hlo hs.le
      have hh : normalizedGaussianMaximum n z ≤ (1 + δ) * (u / s) := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right hhi hs.le
      have hlr := mul_le_mul_of_nonneg_left hn.1 (by linarith : 0 ≤ 1 - δ)
      have hur := mul_le_mul_of_nonneg_left hn.2 (by linarith : 0 ≤ 1 + δ)
      have hd2 : δ ^ 2 ≤ δ := by nlinarith
      have he : |normalizedGaussianMaximum n z - 1| ≤ ε := abs_le.mpr
        ⟨by change (1 - δ) * (1 - δ) ≤ (1 - δ) * (u / s) at hlr; nlinarith,
         by change (1 + δ) * (u / s) ≤ (1 + δ) * (1 + δ) at hur; nlinarith⟩
      exact not_lt_of_ge he hz
    have hp := (measureReal_mono (μ := standardGaussian (n + 2)) hsub).trans (measureReal_union_le _ _)
    rw [finiteGaussianMaximum_cdf, finiteGaussianMaximum_tail] at hp
    exact hp

/-- The normalized maxima are uniformly bounded in L2 by integration of
the printed union tail. -/
theorem integral_normalizedGaussianMaximum_sq_le (n : ℕ) :
    (∫ z, normalizedGaussianMaximum n z ^ 2 ∂standardGaussian (n + 2)) ≤ 6 := by
  let m := n + 2
  have hm : 2 ≤ m := by omega
  have hlog : 0 < Real.log (m : ℝ) := Real.log_pos (by exact_mod_cast hm)
  have hs : Real.sqrt (2 * Real.log (m : ℝ)) ^ 2 = 2 * Real.log (m : ℝ) := Real.sq_sqrt (by positivity)
  have hb := integral_gaussian_norm_sq_le_four_dimensionLog (by omega : 1 ≤ m)
  have hmax : (∫ z : Vector m, finiteMaximum z ^ 2 ∂standardGaussian m) ≤
      4 * dimensionLog m := by
    apply (integral_mono (integrable_finiteGaussianMaximum_sq_direct m)
      (integrable_gaussian_norm_sq_direct m) (fun z => by
        rw [← sq_abs (finiteMaximum z)]
        exact pow_le_pow_left₀ (abs_nonneg _) (abs_finiteMaximum_le_norm z) 2)).trans hb
  have hlog2 : (1 : ℝ) / 2 ≤ Real.log (m : ℝ) := by
    have h := Real.log_le_log (by norm_num : (0 : ℝ) < 2) (show (2 : ℝ) ≤ m by exact_mod_cast hm)
    have hl := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at hl
    linarith
  change (∫ z : Vector m, (finiteMaximum z / Real.sqrt (2 * Real.log (m : ℝ))) ^ 2 ∂standardGaussian m) ≤ _
  simp_rw [div_pow, hs]
  rw [integral_div]
  apply (div_le_iff₀ (by positivity : 0 < 2 * Real.log (m : ℝ))).mpr
  have hdim : dimensionLog m = 1 + Real.log (m : ℝ) := by
    unfold dimensionLog
    rw [Real.log_mul (Real.exp_pos 1).ne' (by positivity : (m : ℝ) ≠ 0), Real.log_exp]
  rw [hdim] at hmax
  linarith

theorem integrable_normalizedGaussianMaximum (n : ℕ) :
    Integrable (normalizedGaussianMaximum n) (standardGaussian (n + 2)) :=
  (integrable_finiteGaussianMaximum_direct (n + 2)).div_const _

theorem integrable_normalizedGaussianMaximum_sq (n : ℕ) :
    Integrable (fun z => normalizedGaussianMaximum n z ^ 2) (standardGaussian (n + 2)) := by
  simpa only [normalizedGaussianMaximum, div_pow] using
    (integrable_finiteGaussianMaximum_sq_direct (n + 2)).div_const
      (Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ)) ^ 2)

/-- Quantitative uniform integrability of the laws of the normalized
maxima. Since the underlying product dimensions vary, it is expressed by
the identical expectation-tail criterion on each actual probability space. -/
theorem normalizedGaussianMaximum_uniform_tail {K : ℝ} (hK : 0 < K) (n : ℕ) :
    (∫ z, ({z | K < |normalizedGaussianMaximum n z|}).indicator
      (fun z => |normalizedGaussianMaximum n z|) z ∂standardGaussian (n + 2)) ≤ 6 / K := by
  have hset : MeasurableSet {z | K < |normalizedGaussianMaximum n z|} :=
    measurableSet_lt measurable_const (measurable_normalizedGaussianMaximum n).abs
  have hpoint (z : Vector (n + 2)) :
      ({z | K < |normalizedGaussianMaximum n z|}).indicator
        (fun z => |normalizedGaussianMaximum n z|) z ≤ normalizedGaussianMaximum n z ^ 2 / K := by
    by_cases hz : K < |normalizedGaussianMaximum n z|
    · rw [Set.indicator_of_mem (show z ∈ {z | K < |normalizedGaussianMaximum n z|} from hz)]
      apply (le_div_iff₀ hK).mpr
      nlinarith [sq_abs (normalizedGaussianMaximum n z)]
    · rw [Set.indicator_of_not_mem (show z ∉ {z | K < |normalizedGaussianMaximum n z|} from hz)]
      positivity
  have hi := integral_mono ((integrable_normalizedGaussianMaximum n).abs.indicator hset)
    ((integrable_normalizedGaussianMaximum_sq n).div_const K) hpoint
  rw [integral_div] at hi
  exact hi.trans (div_le_div_of_nonneg_right (integral_normalizedGaussianMaximum_sq_le n) hK.le)

theorem normalizedGaussianMaximum_uniform_integrability :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧ ∀ n : ℕ,
      (∫ z, ({z | K < |normalizedGaussianMaximum n z|}).indicator
        (fun z => |normalizedGaussianMaximum n z|) z ∂standardGaussian (n + 2)) ≤ ε := by
  intro ε hε
  refine ⟨6 / ε, by positivity, fun n => ?_⟩
  have h := normalizedGaussianMaximum_uniform_tail (by positivity : 0 < 6 / ε) n
  have he : (6 : ℝ) / (6 / ε) = ε := by field_simp
  exact h.trans_eq he


/-- The elementary truncation estimate in the uniform-integrability proof
of convergence of means. The small deviation, bounded part and uniformly
small expectation tail are all kept as separate terms. -/
theorem normalizedGaussianMaximum_L1_error_bound (n : ℕ) {η K : ℝ}
    (hη : 0 ≤ η) (hK : 1 ≤ K) :
    (∫ z, |normalizedGaussianMaximum n z - 1| ∂standardGaussian (n + 2)) ≤
      η + (K + 1) * (standardGaussian (n + 2)).real
        {z | η < |normalizedGaussianMaximum n z - 1|} + 12 / K := by
  let R := normalizedGaussianMaximum n
  let A := {z : Vector (n + 2) | η < |R z - 1|}
  let B := {z : Vector (n + 2) | K < |R z|}
  have hA : MeasurableSet A := measurableSet_lt measurable_const
    (((measurable_normalizedGaussianMaximum n).sub_const 1).abs)
  have hB : MeasurableSet B := measurableSet_lt measurable_const
    (measurable_normalizedGaussianMaximum n).abs
  have hi := integrable_normalizedGaussianMaximum n
  have hiA := (integrable_const (K + 1)).indicator hA (μ := standardGaussian (n + 2))
  have hiB := hi.abs.indicator hB
  have hp (z : Vector (n + 2)) : |R z - 1| ≤
      η + A.indicator (fun _ => K + 1) z + 2 * B.indicator (fun z => |R z|) z := by
    by_cases hzB : z ∈ B
    · rw [Set.indicator_of_mem hzB]
      have hbig : K < |R z| := hzB
      have hA0 : 0 ≤ A.indicator (fun _ => K + 1) z :=
        Set.indicator_nonneg (fun _ _ => by linarith) z
      have he := abs_sub (R z) 1
      norm_num only [abs_one] at he
      linarith
    · rw [Set.indicator_of_not_mem hzB, mul_zero, add_zero]
      have hsmall : |R z| ≤ K := le_of_not_gt hzB
      by_cases hzA : z ∈ A
      · rw [Set.indicator_of_mem hzA]
        have he := abs_sub (R z) 1
        norm_num only [abs_one] at he
        linarith
      · rw [Set.indicator_of_not_mem hzA]
        have hclose : |R z - 1| ≤ η := le_of_not_gt hzA
        simpa only [add_zero] using hclose
  have hb := integral_mono (hi.sub (integrable_const 1)).abs
    (((integrable_const η).add hiA).add (hiB.const_mul 2)) hp
  have he1 := integral_add ((integrable_const η).add hiA) (hiB.const_mul 2)
  have he2 := integral_add (integrable_const η) hiA
  simp only [Pi.add_apply] at he1 he2
  simp only [Pi.add_apply, Pi.sub_apply] at hb
  rw [he1, he2, integral_const_mul, integral_indicator_const (K + 1) hA,
    integral_const] at hb
  simp only [measureReal_univ_eq_one, one_smul, smul_eq_mul] at hb
  have ht := normalizedGaussianMaximum_uniform_tail
    (lt_of_lt_of_le zero_lt_one hK) n
  change (∫ z, B.indicator (fun z => |R z|) z ∂standardGaussian (n + 2)) ≤ 6 / K at ht
  have hm := mul_le_mul_of_nonneg_left ht (by norm_num : (0 : ℝ) ≤ 2)
  change (∫ z, |R z - 1| ∂standardGaussian (n + 2)) ≤ _
  dsimp only [R, A, B] at hb hm ⊢
  rw [show (2 : ℝ) * (6 / K) = 12 / K by ring] at hm
  exact hb.trans (by linarith)

/-- Convergence in probability and the proved uniform expectation tails
imply L1 convergence. This is the printed uniform-integrability route. -/
theorem normalizedGaussianMaximum_tendsto_L1 :
    Tendsto (fun n : ℕ => ∫ z, |normalizedGaussianMaximum n z - 1|
      ∂standardGaussian (n + 2)) atTop (𝓝 0) := by
  rw [tendsto_order]
  constructor
  · intro b hb
    exact Eventually.of_forall (fun n => hb.trans_le (integral_nonneg (fun _ => abs_nonneg _)))
  · intro b hb
    let η := b / 4
    let K := 1 + 48 / b
    have hη : 0 < η := by dsimp [η]; positivity
    have hK : 1 ≤ K := by
      dsimp [K]
      have h := div_nonneg (by norm_num : (0 : ℝ) ≤ 48) hb.le
      linarith
    have hKpos : 0 < K := zero_lt_one.trans_le hK
    have htail : 12 / K < b / 4 := by
      apply (div_lt_iff₀ hKpos).mpr
      dsimp [K]
      have he : b * (48 / b) = 48 := by field_simp
      nlinarith
    have hprob := normalizedGaussianMaximum_tendsto_in_probability hη
    have hlim : Tendsto (fun n : ℕ => η + (K + 1) * (standardGaussian (n + 2)).real
        {z | η < |normalizedGaussianMaximum n z - 1|} + 12 / K)
        atTop (𝓝 (η + 12 / K)) := by
      simpa only [mul_zero, add_zero] using
        ((tendsto_const_nhds (x := η)).add (hprob.const_mul (K + 1))).add_const (12 / K)
    have hfinal : η + 12 / K < b := by dsimp [η]; linarith
    filter_upwards [hlim.eventually (eventually_lt_nhds hfinal)] with n hn
    exact (normalizedGaussianMaximum_L1_error_bound n hη.le hK).trans_lt hn

/-- The mean asymptotic follows from the actual probability convergence
and uniform integrability, without invoking the earlier mean limit. -/
theorem tendsto_gaussianMaximumMean_div_sqrt_log_via_uniform_integrability :
    Tendsto (fun m : ℕ => gaussianMaximumMean m / Real.sqrt (2 * Real.log (m : ℝ)))
      atTop (𝓝 1) := by
  have hmean (n : ℕ) :
      |(∫ z, normalizedGaussianMaximum n z ∂standardGaussian (n + 2)) - 1| ≤
        ∫ z, |normalizedGaussianMaximum n z - 1| ∂standardGaussian (n + 2) := by
    have hh := norm_integral_le_integral_norm
      (fun z : Vector (n + 2) => normalizedGaussianMaximum n z - 1)
      (μ := standardGaussian (n + 2))
    rw [integral_sub (integrable_normalizedGaussianMaximum n) (integrable_const 1)] at hh
    simpa only [integral_const, measureReal_univ_eq_one, one_smul, Real.norm_eq_abs] using hh
  have hlo : Tendsto (fun n : ℕ => 1 - ∫ z, |normalizedGaussianMaximum n z - 1|
      ∂standardGaussian (n + 2)) atTop (𝓝 1) := by
    simpa only [sub_zero] using (tendsto_const_nhds (x := (1 : ℝ))).sub normalizedGaussianMaximum_tendsto_L1
  have hhi : Tendsto (fun n : ℕ => 1 + ∫ z, |normalizedGaussianMaximum n z - 1|
      ∂standardGaussian (n + 2)) atTop (𝓝 1) := by
    simpa only [add_zero] using (tendsto_const_nhds (x := (1 : ℝ))).add normalizedGaussianMaximum_tendsto_L1
  have hh : Tendsto (fun n : ℕ => ∫ z, normalizedGaussianMaximum n z
      ∂standardGaussian (n + 2)) atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hhi
    · exact Eventually.of_forall (fun n => by linarith [(abs_le.mp (hmean n)).1])
    · exact Eventually.of_forall (fun n => by linarith [(abs_le.mp (hmean n)).2])
  apply (tendsto_add_atTop_iff_nat 2).mp
  apply hh.congr'
  exact Eventually.of_forall (fun n => by
    change (∫ z, normalizedGaussianMaximum n z ∂standardGaussian (n + 2)) =
      gaussianMaximumMean (n + 2) / Real.sqrt (2 * Real.log ((n + 2 : ℕ) : ℝ))
    rw [gaussianMaximumMean_eq_integral]
    exact integral_div _ _)

end
end RectangleCLT.Companion.SplitV4.Printed
