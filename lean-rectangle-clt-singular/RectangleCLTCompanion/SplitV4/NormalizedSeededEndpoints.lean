import RectangleCLTCompanion.SplitV4.NormalizedSeededPath

open MeasureTheory Set

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def seededInitializationTime (ε : ℝ) : ℝ := ε / (1 + ε)

theorem seededInitializationTime_mem_Icc {ε : ℝ} (hε : 0 ≤ ε) :
    seededInitializationTime ε ∈ Icc (0 : ℝ) 1 := by
  unfold seededInitializationTime
  exact ⟨div_nonneg hε (by linarith), (div_le_one (by linarith : 0 < 1 + ε)).mpr (by linarith)⟩

theorem seededInitializationTime_sqrt_complement {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (1 - seededInitializationTime ε) = (seededNormalization ε)⁻¹ := by
  have hd : 1 + ε ≠ 0 := by linarith
  have he : 1 - seededInitializationTime ε = 1 / (1 + ε) := by
    unfold seededInitializationTime
    field_simp
  rw [he, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 1) (1 + ε), Real.sqrt_one]
  simp only [seededNormalization, one_div]

theorem seededInitializationTime_sqrt {ε : ℝ} (hε : 0 ≤ ε) :
    Real.sqrt (seededInitializationTime ε) = Real.sqrt ε / seededNormalization ε := by
  exact Real.sqrt_div hε (1 + ε)

theorem gaussianLaw_scalar_map {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    (gaussianLaw A).map (fun y => c • y) = gaussianLaw (c • A) := by
  rw [gaussianLaw, Measure.map_map (by fun_prop) (measurable_mulVec A)]
  congr 1
  funext g
  simp only [Function.comp_apply, Matrix.smul_mulVec_assoc]

theorem map_sum_scaled_gaussianLaw
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω) [SFinite μ]
    (S : Ω → Vector p) (hS : Measurable S) (A : Matrix (Fin p) (Fin p) ℝ) (c : ℝ) :
    (μ.prod (gaussianLaw A)).map (fun z => S z.1 + c • z.2) =
      Measure.conv (μ.map S) (gaussianLaw (c • A)) := by
  have hm : (μ.map S).prod (gaussianLaw (c • A)) =
      (μ.prod (gaussianLaw A)).map (Prod.map S (fun y => c • y)) := by
    rw [← gaussianLaw_scalar_map A c]
    exact Measure.map_prod_map μ (gaussianLaw A) hS (by fun_prop)
  rw [Measure.conv, hm, Measure.map_map (measurable_fst.add measurable_snd) (hS.prodMap (by fun_prop))]
  rfl

theorem normalizedSeededInterpolationLaw_one
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    normalizedSeededInterpolationLaw μ ξ A ε 1 = gaussianLaw A := by
  unfold normalizedSeededInterpolationLaw seededInterpolationLaw
  rw [interpolationLaw_one]
  have hg : Measure.conv (gaussianLaw (Real.sqrt ε • A)) (gaussianLaw A) =
      gaussianLaw (Real.sqrt (1 + ε) • A) := by
    simpa only [Real.sqrt_one, one_smul] using gaussian_seed_conv A hε (by norm_num : (0 : ℝ) ≤ 1)
  rw [hg]
  change (gaussianLaw (seededNormalization ε • A)).map
    (fun y => (seededNormalization ε)⁻¹ • y) = _
  rw [gaussianLaw_scalar_map, smul_smul, inv_mul_cancel₀ (seededNormalization_pos hε).ne', one_smul]

/-- The initial normalized seeded law is exactly the ordinary Slepian
law at `ε/(1+ε)`, on the actual original-sample/Gaussian product law. -/
theorem normalizedSeededInterpolationLaw_zero
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    normalizedSeededInterpolationLaw μ ξ A ε 0 =
      (μ.prod (gaussianLaw A)).map (fun z =>
        Real.sqrt (1 - seededInitializationTime ε) • sumVector ξ z.1 +
          Real.sqrt (seededInitializationTime ε) • z.2) := by
  unfold normalizedSeededInterpolationLaw seededInterpolationLaw
  rw [interpolationLaw_zero μ ξ hξ A, Measure.conv_comm]
  have hSum : Measurable (sumVector ξ) := by
    unfold sumVector
    exact Finset.measurable_sum _ (fun i _ => hξ i)
  rw [← map_sum_scaled_gaussianLaw μ (sumVector ξ) hSum A (Real.sqrt ε),
    Measure.map_map (by fun_prop) (by fun_prop)]
  congr 1
  funext z
  simp only [Function.comp_apply, smul_add, smul_smul,
    seededInitializationTime_sqrt_complement hε, seededInitializationTime_sqrt hε,
    div_eq_mul_inv, mul_comm]

end

end RectangleCLT.Companion.SplitV4
