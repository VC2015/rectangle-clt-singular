import RectangleCLTArxivV1.GaussianWidthOrder
import RectangleCLTArxivV1.SignedVariance
import RectangleCLTCompanion.SubexponentialL2
import RectangleCLTCompanion.SplitV4.PairedNormalization
import Mathlib.Topology.MetricSpace.Lipschitz

/-! Odd common coordinate clipping contracts signed increments. The conclusion
compares the actual Gaussian maxima without claiming a covariance order. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem clipAt_neg {T : ℝ} (hT : 0 ≤ T) (x : ℝ) : clipAt T (-x) = -clipAt T x := by
  unfold clipAt
  rcases le_total x (-T) with hx | hx
  · have h1 : max (-T) (min T x) = -T := by rw [min_eq_right (by linarith), max_eq_left hx]
    have h2 : max (-T) (min T (-x)) = T := by rw [min_eq_left (by linarith), max_eq_right (by linarith)]
    rw [h1,h2]; ring
  · rcases le_total x T with hx' | hx'
    · have h1 : max (-T) (min T x) = x := by rw [min_eq_right hx', max_eq_right hx]
      have h2 : max (-T) (min T (-x)) = -x := by rw [min_eq_right (by linarith), max_eq_right (by linarith)]
      rw [h1,h2]
    · have h1 : max (-T) (min T x) = T := by rw [min_eq_left hx', max_eq_right (by linarith)]
      have h2 : max (-T) (min T (-x)) = -T := by rw [min_eq_right (by linarith), max_eq_left (by linarith)]
      rw [h1,h2]

theorem signedCoordinate_smul_real {p : ℕ} (t : SignedIndex p) (c : ℝ) (x : Vector p) :
    signedCoordinate t (c • x) = c * signedCoordinate t x := by
  cases t with
  | none => simp
  | some v => rcases v with ⟨b,j⟩; cases b <;> simp [signedCoordinate, Pi.smul_apply, smul_eq_mul]

theorem abs_clipAt_sub_le (T x y : ℝ) : |clipAt T x - clipAt T y| ≤ |x-y| := by
  have h : LipschitzWith 1 (clipAt T) := (LipschitzWith.id.const_min T).const_max (-T)
  simpa only [Real.dist_eq, NNReal.coe_one, one_mul] using h.dist_le_mul x y

theorem signedCoordinate_clipAt {p : ℕ} {T : ℝ} (hT : 0 ≤ T)
    (t : SignedIndex p) (x : Vector p) :
    signedCoordinate t (fun j => clipAt T (x j)) = clipAt T (signedCoordinate t x) := by
  cases t with
  | none => simp [clipAt, max_eq_right (by linarith : -T ≤ 0), min_eq_right hT]
  | some v =>
    rcases v with ⟨b,j⟩
    cases b
    · exact (clipAt_neg hT _).symm
    · rfl

theorem signedCoordinate_centeredClipped {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p n : ℕ}
    (X : Fin n → Ω → Vector p) (_hX : ∀ i, Measurable (X i)) {T : ℝ}
    (hT : 0 ≤ T) (i : Fin n) (t : SignedIndex p) (ω : Ω) :
    signedCoordinate t (centeredClippedRows μ X T i ω) =
      clipAt T (signedCoordinate t (X i ω)) -
        ∫ z, clipAt T (signedCoordinate t (X i z)) ∂μ := by
  cases t with
  | none => simp [centeredClippedRows, clipAt, max_eq_right (by linarith : -T ≤ 0), min_eq_right hT]
  | some v =>
    rcases v with ⟨b,j⟩
    cases b
    · simp only [signedCoordinate_neg, centeredClippedRows, clipAt_neg hT, integral_neg]
      ring
    · rfl

theorem sum_integral_projection_sq_of_memLp
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} (ξ : Fin n → Ω → Vector p) (hind : iIndepFun ξ μ)
    (hLp : ∀ i j, MemLp (fun ω => ξ i ω j) 2 μ)
    (hc : ∀ i j, (∫ ω, ξ i ω j ∂μ) = 0) (v : Vector p) :
    (∑ i, ∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ) =
      matrixQuadratic (covariance μ (sumVector ξ)) v := by
  have hint (i : Fin n) (j : Fin p) : Integrable (fun ω => ξ i ω j) μ :=
    (hLp i j).integrable (by norm_num)
  have hpair (i l : Fin n) (j k : Fin p) : Integrable (fun ω => ξ i ω j * ξ l ω k) μ :=
    (hLp i j).integrable_mul (hLp l k)
  have hcov := covariance_sum_of_centered_cross hint hpair hc
    (independent_centered_cross_zero hind hint hc)
  have hexpand (x : Vector p) :
      (dotProduct v x) ^ 2 = ∑ j, ∑ k, v j * (x j * x k) * v k := by
    simp only [dotProduct, pow_two, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring
  have hi (i : Fin n) :
      (∫ ω, (dotProduct v (ξ i ω)) ^ 2 ∂μ) =
      ∑ j, ∑ k, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := by
    simp_rw [hexpand]
    rw [integral_finset_sum Finset.univ (fun j _ =>
      integrable_finset_sum Finset.univ (fun k _ =>
        ((hpair i i j k).const_mul (v j)).mul_const (v k)))]
    apply Finset.sum_congr rfl
    intro j _
    rw [integral_finset_sum Finset.univ (fun k _ =>
      ((hpair i i j k).const_mul (v j)).mul_const (v k))]
    simp only [integral_mul_const, integral_const_mul]
  simp only [hi]
  unfold matrixQuadratic
  simp_rw [hcov]
  calc
    _ = ∑ j, ∑ i, ∑ k, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ i, v j * (∫ ω, ξ i ω j * ξ i ω k ∂μ) * v k := by
      apply Finset.sum_congr rfl
      intro j _
      exact Finset.sum_comm
    _ = _ := by simp only [Finset.mul_sum, Finset.sum_mul]

theorem signedCoordinate_memLp_two {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} [IsProbabilityMeasure μ] {p : ℕ} {X : Ω → Vector p}
    (hLp : ∀ j, MemLp (fun ω => X ω j) 2 μ) (t : SignedIndex p) :
    MemLp (fun ω => signedCoordinate t (X ω)) 2 μ := by
  cases t with
  | none => exact MemLp.zero'
  | some v => rcases v with ⟨b,j⟩; cases b; exact (hLp j).neg; exact hLp j

theorem gaussianMaximumMean_clipped_le
    {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω} [IsProbabilityMeasure μ]
    {p n : ℕ} {X : Fin n → Ω → Vector p} {K u : ℝ}
    (h : SubexponentialIndependentHypotheses μ X K) (hu : 0 ≤ u)
    (A AT : Matrix (Fin p) (Fin p) ℝ)
    (hA : A * A.transpose = covariance μ (normalizedObservationSum X))
    (hAT : AT * AT.transpose = covariance μ
      (sumVector (normalizedClippedRows μ X (K * u)))) :
    gaussianMaximumMean AT ≤ gaussianMaximumMean A := by
  have hT : 0 ≤ K * u := mul_nonneg (zero_le_one.trans h.one_le_scale) hu
  have hbounded := normalizedClippedRows_boundedHypotheses h.measurable h.independent hT
  rw [← gaussianWidth_signedFactorRows AT, ← gaussianWidth_signedFactorRows A]
  apply GenericChaining.gaussianWidth_mono_of_increment_le
  intro s t
  rw [signed_factorRows_norm_sq AT t s, signed_factorRows_norm_sq A t s, hAT, hA]
  rw [← sum_variance_signedContrast hbounded]
  have horig := sum_integral_projection_sq_of_memLp (normalizedSummands X)
    (normalizedSummands_independent h.independent)
    (normalizedSummands_coordinate_memLp_two h.coordinate_memLp_two)
    (normalizedSummands_centered h.centered) (signedDirection s - signedDirection t)
  rw [sumVector_normalizedSummands] at horig
  rw [← horig]
  apply Finset.sum_le_sum
  intro i _
  let Y : Ω → ℝ := fun ω => clipAt (K*u) (signedCoordinate s (X i ω)) -
    clipAt (K*u) (signedCoordinate t (X i ω))
  let V : Ω → ℝ := fun ω => signedCoordinate s (X i ω) - signedCoordinate t (X i ω)
  have hY : MemLp Y 2 μ := by
    apply MemLp.of_bound (((clipAt_continuous _).measurable.comp
      ((signedCoordinate_measurable s).comp (h.measurable i))).sub
      ((clipAt_continuous _).measurable.comp
        ((signedCoordinate_measurable t).comp (h.measurable i)))).aestronglyMeasurable (2*(K*u))
    apply ae_of_all
    intro ω
    simp only [Real.norm_eq_abs]
    have hs := abs_clipAt_le hT (signedCoordinate s (X i ω))
    have ht := abs_clipAt_le hT (signedCoordinate t (X i ω))
    exact (abs_sub _ _).trans (by dsimp only [Function.comp_apply]; linarith)
  have hV : MemLp V 2 μ :=
    (signedCoordinate_memLp_two (h.coordinate_memLp_two i) s).sub
      (signedCoordinate_memLp_two (h.coordinate_memLp_two i) t)
  have hy (ω : Ω) : signedContrast (normalizedClippedRows μ X (K*u)) t s i ω =
      (Real.sqrt (n : ℝ))⁻¹ * (Y ω - ∫ z, Y z ∂μ) := by
    have hs := signedCoordinate_centeredClipped (μ := μ) X h.measurable hT i s ω
    have ht := signedCoordinate_centeredClipped (μ := μ) X h.measurable hT i t ω
    have his : Integrable (fun z => clipAt (K*u) (signedCoordinate s (X i z))) μ := by
      apply (integrable_const (K*u)).mono'
        ((clipAt_continuous _).measurable.comp
          ((signedCoordinate_measurable s).comp (h.measurable i))).aestronglyMeasurable
      exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using abs_clipAt_le hT _
    have hit : Integrable (fun z => clipAt (K*u) (signedCoordinate t (X i z))) μ := by
      apply (integrable_const (K*u)).mono'
        ((clipAt_continuous _).measurable.comp
          ((signedCoordinate_measurable t).comp (h.measurable i))).aestronglyMeasurable
      exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using abs_clipAt_le hT _
    dsimp only [Y]
    rw [integral_sub his hit]
    simp only [signedContrast, normalizedClippedRows, signedCoordinate_smul_real, smul_eq_mul, hs, ht]
    ring
  have hv (ω : Ω) : dotProduct (signedDirection s - signedDirection t)
      (normalizedSummands X i ω) = (Real.sqrt (n : ℝ))⁻¹ * V ω := by
    rw [← signedContrast_eq_dotProduct]
    simp only [signedContrast, normalizedSummands, signedCoordinate_smul_real, smul_eq_mul, V]
    ring
  simp_rw [hy, hv, mul_pow, integral_const_mul]
  apply mul_le_mul_of_nonneg_left _ (sq_nonneg _)
  apply (integral_centered_sq_le hY).trans
  apply integral_mono hY.integrable_sq hV.integrable_sq
  intro ω
  have hclip := abs_clipAt_sub_le (K*u) (signedCoordinate s (X i ω)) (signedCoordinate t (X i ω))
  simpa only [Y, V, sq_abs] using pow_le_pow_left₀ (abs_nonneg _) hclip 2

end
end RectangleCLTArxivV1
