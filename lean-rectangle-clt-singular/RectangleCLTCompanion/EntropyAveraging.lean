import RectangleCLTCompanion.GaussianEntropy

/-! Averaging relative Gaussian selector masses. These are inequalities
for actual integrals, including zero-mass selectors. -/

open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section

/-- The nonnegative entropy contribution of a weight dominated by a
reference weight. It is zero when the smaller mass is zero. -/
def massEntropy (p b : ℝ) : ℝ := p * Real.log (b / p)

lemma massEntropy_nonneg {p b : ℝ} (hp : 0 ≤ p) (hpb : p ≤ b) :
    0 ≤ massEntropy p b := by
  by_cases hz : p = 0
  · simp [massEntropy, hz]
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  apply mul_nonneg hp
  exact Real.log_nonneg ((le_div_iff₀ hp').mpr (by simpa using hpb))

lemma massEntropy_le_reference {p b : ℝ} (hp : 0 ≤ p) (hpb : p ≤ b) :
    massEntropy p b ≤ b := by
  by_cases hz : p = 0
  · simpa [massEntropy, hz] using hpb
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hb : 0 < b := hp'.trans_le hpb
  have hh := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (div_pos hb hp')) hp
  have hcancel : p * (b / p - 1) = b - p := by field_simp
  rw [hcancel] at hh
  exact hh.trans (sub_le_self _ hp)

/-- A supporting plane for the jointly concave mass-entropy expression.
This elementary inequality will be integrated rather than assuming Jensen. -/
lemma massEntropy_le_support {p b P B : ℝ}
    (hp : 0 ≤ p) (hpb : p ≤ b) (hP : 0 < P) (hB : 0 < B) :
    massEntropy p b ≤ p * Real.log (B / P) + (P / B) * b - p := by
  by_cases hz : p = 0
  · simp only [massEntropy, hz, zero_mul, sub_zero, zero_add]
    exact mul_nonneg (div_nonneg hP.le hB.le) (hp.trans hpb)
  have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hb : 0 < b := hp'.trans_le hpb
  have hratio : 0 < (b * P) / (p * B) := div_pos (mul_pos hb hP) (mul_pos hp' hB)
  have hlog : Real.log (b / p) = Real.log (B / P) +
      Real.log ((b * P) / (p * B)) := by
    rw [← Real.log_mul (div_ne_zero hB.ne' hP.ne') (ne_of_gt hratio)]
    congr 1
    field_simp
    ring
  have ht := mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos hratio) hp
  unfold massEntropy
  rw [hlog, mul_add]
  have hid : p * ((b * P) / (p * B) - 1) = (P / B) * b - p := by
    field_simp
    ring
  rw [hid] at ht
  linarith

/-- A cap with no logarithm of the smoothing bandwidth: both masses
scale by the same quantity `T`. -/
theorem massEntropy_le_common_scale {p b T C M : ℝ}
    (hp : 0 ≤ p) (hpb : p ≤ b) (hT : 0 < T) (hC : 1 ≤ C) (hM : 1 ≤ M)
    (hpCap : p ≤ C * T) (hbCap : b ≤ C * M * T) :
    massEntropy p b ≤ T * (C * (C + Real.log M) + 1) := by
  have hC0 : 0 < C := lt_of_lt_of_le zero_lt_one hC
  have hM0 : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hlogM : 0 ≤ Real.log M := Real.log_nonneg hM
  by_cases hz : p = 0
  · simp only [massEntropy, hz, zero_mul]
    positivity
  have hp0 : 0 < p := lt_of_le_of_ne hp (Ne.symm hz)
  have hb0 : 0 < b := hp0.trans_le hpb
  have hlog := Real.log_le_log (div_pos hb0 hp0) ((div_le_div_iff_of_pos_right hp0).mpr hbCap)
  have hsplit : Real.log (C * M * T / p) = Real.log C + Real.log M + Real.log (T / p) := by
    rw [show C * M * T / p = (C * M) * (T / p) by ring,
      Real.log_mul (mul_pos hC0 hM0).ne' (div_pos hT hp0).ne',
      Real.log_mul hC0.ne' hM0.ne']
  rw [hsplit] at hlog
  have hnormal := mul_le_mul_of_nonneg_left
    (Real.log_le_sub_one_of_pos (div_pos hT hp0)) hp
  have hnEq : p * (T / p - 1) = T - p := by field_simp
  rw [hnEq] at hnormal
  have hlogC : Real.log C ≤ C := (Real.log_le_sub_one_of_pos hC0).trans (by linarith)
  have hpcap := mul_le_mul_of_nonneg_right hpCap (add_nonneg hC0.le hlogM)
  have hmul := mul_le_mul_of_nonneg_left hlog hp
  unfold massEntropy
  nlinarith [mul_le_mul_of_nonneg_left hlogC hp]

/-- Finite log-sum inequality, allowing individual zero masses. -/
theorem sum_massEntropy_le {ι : Type*} (S : Finset ι) (p b : ι → ℝ)
    (hp0 : ∀ i ∈ S, 0 ≤ p i) (hpb : ∀ i ∈ S, p i ≤ b i)
    (hP : 0 < ∑ i ∈ S, p i) :
    (∑ i ∈ S, massEntropy (p i) (b i)) ≤
      massEntropy (∑ i ∈ S, p i) (∑ i ∈ S, b i) := by
  let P := ∑ i ∈ S, p i
  let B := ∑ i ∈ S, b i
  have hB : 0 < B := hP.trans_le (Finset.sum_le_sum (fun i hi => hpb i hi))
  have hh := Finset.sum_le_sum (fun i hi =>
    massEntropy_le_support (hp0 i hi) (hpb i hi) hP hB)
  have heq : (∑ i ∈ S, (p i * Real.log (B / P) + (P / B) * b i - p i)) =
      P * Real.log (B / P) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.mul_sum]
    change P * Real.log (B / P) + (P / B) * B - P = _
    rw [div_mul_cancel₀ _ hB.ne', add_sub_cancel_right]
  rw [heq] at hh
  exact hh

/-- The mean-entropy lemma summed over an actual finite family of
Gaussian selector weights. The logarithm is taken after summing reference
masses, so the estimate retains the shared smoothing scale. -/
theorem sum_gaussian_mean_relative_to_faces {r : ℕ} {ι : Type*}
    (S : Finset ι) (u : ι → Vector r) (β : ι → ℝ → ℝ)
    (w : ι → Vector r → ℝ)
    (hu : ∀ i ∈ S, vectorNormSq (u i) = 1)
    (hβ : ∀ i ∈ S, Measurable (β i))
    (hβ0 : ∀ i ∈ S, ∀ t, 0 ≤ β i t)
    (hβ1 : ∀ i ∈ S, ∀ t, β i t ≤ 1)
    (hw : ∀ i ∈ S, Measurable (w i))
    (hwb : ∀ i ∈ S, ∀ z, 0 ≤ w i z ∧ w i z ≤ β i (faceDot (u i) z))
    (hmass : ∀ i ∈ S, 0 < weightMass (standardGaussian r) (w i))
    (hS : S.Nonempty) :
    (∑ i ∈ S, weightMass (standardGaussian r) (w i) *
      vectorNormSq (weightMean (standardGaussian r) id (w i))) ≤
      (∫ z, ∑ i ∈ S, w i z * (faceDot (u i) z) ^ 2 ∂standardGaussian r) +
      2 * massEntropy (∑ i ∈ S, weightMass (standardGaussian r) (w i))
        (∑ i ∈ S, ∫ z, β i (faceDot (u i) z) ∂standardGaussian r) := by
  let p := fun i => weightMass (standardGaussian r) (w i)
  let b := fun i => ∫ z, β i (faceDot (u i) z) ∂standardGaussian r
  have hbound (i : ι) (hi : i ∈ S) (z : Vector r) : |w i z| ≤ 1 := by
    rw [abs_of_nonneg (hwb i hi z).1]
    exact (hwb i hi z).2.trans (hβ1 i hi _)
  have hrefBound (i : ι) (hi : i ∈ S) (z : Vector r) :
      |β i (faceDot (u i) z)| ≤ 1 := by
    rw [abs_of_nonneg (hβ0 i hi _)]
    exact hβ1 i hi _
  have hrefMeas (i : ι) (hi : i ∈ S) :
      Measurable (fun z : Vector r => β i (faceDot (u i) z)) := by
    apply (hβ i hi).comp
    unfold faceDot
    fun_prop
  have hpb (i : ι) (hi : i ∈ S) : p i ≤ b i := by
    exact integral_mono (standardGaussian_integrable_bounded_weight _ (hw i hi) (hbound i hi))
      (standardGaussian_integrable_bounded_weight _ (hrefMeas i hi) (hrefBound i hi))
      (fun z => (hwb i hi z).2)
  have hP : 0 < ∑ i ∈ S, p i := Finset.sum_pos (fun i hi => hmass i hi) hS
  have hsum := Finset.sum_le_sum (fun i hi =>
    gaussian_mean_relative_to_one_face (u i) (hu i hi) (β i)
      (hβ i hi) (fun t => ⟨hβ0 i hi t, hβ1 i hi t⟩) (w i) (hw i hi) (hwb i hi) (hmass i hi))
  have hent := sum_massEntropy_le S p b (fun i hi => (hmass i hi).le) hpb hP
  have hint : (∑ i ∈ S, ∫ z, w i z * (faceDot (u i) z) ^ 2 ∂standardGaussian r) =
      ∫ z, ∑ i ∈ S, w i z * (faceDot (u i) z) ^ 2 ∂standardGaussian r := by
    symm
    exact integral_finset_sum S (fun i hi =>
      gaussian_integrable_weighted_linear_sq (w i) (hw i hi) (hbound i hi) (u i))
  simp only [mul_assoc, Finset.sum_add_distrib, ← Finset.mul_sum] at hsum
  rw [hint] at hsum
  exact hsum.trans (add_le_add_left (mul_le_mul_of_nonneg_left hent (by norm_num)) _)

lemma integrable_massEntropy {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (p b : Ω → ℝ) (hp : Measurable p) (hb : Measurable b)
    (hp0 : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ b x) (hbi : Integrable b ν) :
    Integrable (fun x => massEntropy (p x) (b x)) ν := by
  have hm : Measurable (fun x => massEntropy (p x) (b x)) := by
    unfold massEntropy
    fun_prop
  apply hbi.mono' hm.aestronglyMeasurable
  exact ae_of_all _ fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (massEntropy_nonneg (hp0 x) (hpb x))]
    exact massEntropy_le_reference (hp0 x) (hpb x)

/-- Log-sum/Jensen for the actual averaged selector masses. No probability
normalization of the underlying measure is needed. -/
theorem integral_massEntropy_le {Ω : Type*} [MeasurableSpace Ω]
    (ν : Measure Ω) (p b : Ω → ℝ) (hp : Measurable p) (hb : Measurable b)
    (hp0 : ∀ x, 0 ≤ p x) (hpb : ∀ x, p x ≤ b x)
    (hpi : Integrable p ν) (hbi : Integrable b ν) (hP : 0 < ∫ x, p x ∂ν) :
    (∫ x, massEntropy (p x) (b x) ∂ν) ≤
      massEntropy (∫ x, p x ∂ν) (∫ x, b x ∂ν) := by
  let P := ∫ x, p x ∂ν
  let B := ∫ x, b x ∂ν
  have hB : 0 < B := hP.trans_le (integral_mono hpi hbi hpb)
  have hi := ((hpi.mul_const (Real.log (B / P))).add
    (hbi.const_mul (P / B))).sub hpi
  have hh := integral_mono (integrable_massEntropy ν p b hp hb hp0 hpb hbi) hi
    (fun x => massEntropy_le_support (hp0 x) (hpb x) hP hB)
  have heq : (∫ x, (p x * Real.log (B / P) + (P / B) * b x) - p x ∂ν) =
      P * Real.log (B / P) + (P / B) * B - P := by
    have hs := integral_sub ((hpi.mul_const (Real.log (B / P))).add
      (hbi.const_mul (P / B))) hpi
    have ha := integral_add (hpi.mul_const (Real.log (B / P))) (hbi.const_mul (P / B))
    simp only [Pi.add_apply, Pi.sub_apply] at hs ha
    rw [hs, ha, integral_mul_const, integral_const_mul]
  simp only [Pi.sub_apply, Pi.add_apply] at hh
  rw [heq] at hh
  have hcancel : (P / B) * B = P := div_mul_cancel₀ _ hB.ne'
  rw [hcancel, add_sub_cancel_right] at hh
  exact hh

end
end RectangleCLT.Companion
