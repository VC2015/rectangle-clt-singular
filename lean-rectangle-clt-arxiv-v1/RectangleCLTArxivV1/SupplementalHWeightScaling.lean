import RectangleCLTArxivV1.SupplementalHProjectedMean

/-! Removing an arbitrary finite weight bound from H's Gaussian reductions.
The normalization constant cancels from actual masses, means, scores and
relative entropy; it may depend on the fixed base point. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem weightMass_const_mul {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (w : Ω → ℝ) (c : ℝ) :
    weightMass μ (fun x => c*w x) = c*weightMass μ w := by
  exact integral_const_mul c w

theorem weightMean_const_mul {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (V : Ω → Vector r) (w : Ω → ℝ) {c : ℝ} (hc : c ≠ 0) :
    weightMean μ V (fun x => c*w x) = weightMean μ V w := by
  funext j
  unfold weightMean
  rw [weightMass_const_mul]
  have he : (∫ x, V x j*(c*w x) ∂μ) = c*(∫ x, V x j*w x ∂μ) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (fun x => by ring))
  rw [he]
  by_cases hp : weightMass μ w=0
  · simp [hp]
  · field_simp
    ring

theorem weightedScore_const_mul {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}
    (μ : Measure Ω) (V : Ω → Vector r) (w : Ω → ℝ) (c : ℝ) :
    weightedScore μ V (fun x => c*w x) = c • weightedScore μ V w := by
  ext j k
  change (∫ x, (V x j*V x k-if j=k then 1 else 0)*(c*w x) ∂μ) =
    c*(∫ x, (V x j*V x k-if j=k then 1 else 0)*w x ∂μ)
  rw [← integral_const_mul]
  exact integral_congr_ae (ae_of_all _ (fun x => by ring))

theorem symmetricNuclearNorm_nonneg_smul {r : ℕ} (M : Matrix (Fin r) (Fin r) ℝ)
    {c : ℝ} (hc : 0 ≤ c) : symmetricNuclearNorm (c • M) = c*symmetricNuclearNorm M := by
  have htrace (B : Matrix (Fin r) (Fin r) ℝ) :
      Matrix.trace (B*(c • M)) = c*Matrix.trace (B*M) := by
    rw [Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul]
  apply le_antisymm
  · apply csSup_le (symmetricTrace_values_nonempty _)
    rintro t ⟨B,hB,rfl⟩
    rw [htrace]
    exact mul_le_mul_of_nonneg_left (trace_le_symmetricNuclearNorm M B hB) hc
  · by_cases hc0 : c=0
    · simp [hc0,symmetricNuclearNorm_zero]
    have hcp : 0 < c := lt_of_le_of_ne hc (Ne.symm hc0)
    have hb : symmetricNuclearNorm M ≤ symmetricNuclearNorm (c • M)/c := by
      apply csSup_le (symmetricTrace_values_nonempty _)
      rintro t ⟨B,hB,rfl⟩
      apply (le_div_iff₀ hcp).mpr
      simpa only [htrace,mul_comm] using trace_le_symmetricNuclearNorm (c • M) B hB
    exact (mul_le_mul_of_nonneg_left hb hc).trans_eq (by field_simp)

theorem NonnegativeLogConcave_const_mul {r : ℕ} {w : Vector r → ℝ}
    (hw0 : ∀ g, 0 ≤ w g) (hlog : Printed.NonnegativeLogConcave w)
    {c : ℝ} (hc : 0 < c) : Printed.NonnegativeLogConcave (fun x => c*w x) := by
  intro x y t ht0 ht1
  rw [Real.mul_rpow hc.le (hw0 x),Real.mul_rpow hc.le (hw0 y)]
  have he : c^(1-t)*c^t=c := by
    rw [←Real.rpow_add hc,show (1-t)+t=1 by ring,Real.rpow_one]
  calc
    _ = (c^(1-t)*c^t)*(w x^(1-t)*w y^t) := by ring
    _ = c*(w x^(1-t)*w y^t) := by rw [he]
    _ ≤ _ := mul_le_mul_of_nonneg_left (hlog x y t ht0 ht1) hc.le

theorem gaussian_logConcave_matrix_reduction_of_bound {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hw0 : ∀ g, 0 ≤ w g)
    {M : ℝ} (hM : 0 < M) (hwM : ∀ g, w g ≤ M)
    (hp : 0 < weightMass (standardGaussian r) w) (hlog : Printed.NonnegativeLogConcave w) :
    symmetricNuclearNorm (weightedScore (standardGaussian r) id w) ≤
      2*weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w)-
        ∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r := by
  let c : ℝ := M⁻¹
  have hc : 0 < c := inv_pos.mpr hM
  have hb (g : Vector r) : c*w g ≤ 1 := by
    have hh := mul_le_mul_of_nonneg_left (hwM g) hc.le
    simpa only [c,inv_mul_cancel₀ hM.ne'] using hh
  have hh := gaussian_bounded_logConcave_matrix_reduction (fun g => c*w g)
    (measurable_const.mul hw) (fun g => mul_nonneg hc.le (hw0 g)) hb
    (by rw [weightMass_const_mul]; exact mul_pos hc hp)
    (NonnegativeLogConcave_const_mul hw0 hlog hc)
  rw [weightedScore_const_mul,symmetricNuclearNorm_nonneg_smul _ hc.le,
    weightMass_const_mul,weightMean_const_mul _ _ _ hc.ne'] at hh
  have ht : (∫ g, (vectorNormSq g-(r:ℝ))*(c*w g) ∂standardGaussian r) =
      c*(∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r) := by
    rw [←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (fun g => by ring))
  rw [ht] at hh
  have he : 2*(c*weightMass (standardGaussian r) w)*vectorNormSq (weightMean (standardGaussian r) id w)-
      c*(∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r) =
      c*(2*weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w)-
        ∫ g, (vectorNormSq g-(r:ℝ))*w g ∂standardGaussian r) := by ring
  rw [he] at hh
  exact (mul_le_mul_left hc).mp hh

theorem gaussian_projected_mean_of_bounded_reference {r : ℕ}
    (P : Matrix (Fin r) (Fin r) ℝ) (hPt : P.transpose=P) (hPP : P*P=P)
    (β : Vector r → ℝ) (hβ : Measurable β) {M : ℝ} (hM : 0 < M)
    (hβb : ∀ x, 0 ≤ β x ∧ β x ≤ M)
    (w : Vector r → ℝ) (hw : Measurable w)
    (hwb : ∀ g, 0 ≤ w g ∧ w g ≤ β (P.mulVec g))
    (hpw : 0 < weightMass (standardGaussian r) w) :
    weightMass (standardGaussian r) w*vectorNormSq (weightMean (standardGaussian r) id w) ≤
      (∫ g, w g*vectorNormSq (P.mulVec g) ∂standardGaussian r)+
        2*weightMass (standardGaussian r) w*
          Real.log ((∫ g, β (P.mulVec g) ∂standardGaussian r)/weightMass (standardGaussian r) w) := by
  let c : ℝ := M⁻¹
  have hc : 0 < c := inv_pos.mpr hM
  have hβc (x : Vector r) : 0 ≤ c*β x ∧ c*β x ≤ 1 := by
    refine ⟨mul_nonneg hc.le (hβb x).1, ?_⟩
    have hh := mul_le_mul_of_nonneg_left (hβb x).2 hc.le
    simpa only [c,inv_mul_cancel₀ hM.ne'] using hh
  have hh := gaussian_mean_relative_to_projection P hPt hPP
    (fun x => c*β x) (measurable_const.mul hβ) hβc
    (fun g => c*w g) (measurable_const.mul hw)
    (fun g => ⟨mul_nonneg hc.le (hwb g).1,mul_le_mul_of_nonneg_left (hwb g).2 hc.le⟩)
    (by rw [weightMass_const_mul]; exact mul_pos hc hpw)
  rw [weightMass_const_mul,weightMean_const_mul _ _ _ hc.ne'] at hh
  have hsecond : (∫ g, (c*w g)*vectorNormSq (P.mulVec g) ∂standardGaussian r) =
      c*(∫ g, w g*vectorNormSq (P.mulVec g) ∂standardGaussian r) := by
    rw [←integral_const_mul]
    exact integral_congr_ae (ae_of_all _ (fun g => by ring))
  have hreference : (∫ g, c*β (P.mulVec g) ∂standardGaussian r) =
      c*(∫ g, β (P.mulVec g) ∂standardGaussian r) := integral_const_mul c _
  rw [hsecond,hreference] at hh
  have hratio : (c*(∫ g, β (P.mulVec g) ∂standardGaussian r))/
      (c*weightMass (standardGaussian r) w) =
      (∫ g, β (P.mulVec g) ∂standardGaussian r)/weightMass (standardGaussian r) w := by
    field_simp [hc.ne',hpw.ne']
    ring
  rw [hratio] at hh
  apply (mul_le_mul_left hc).mp
  convert hh using 1 <;> ring

end
end RectangleCLTArxivV1
