import RectangleCLT.GaussianMoments
import RectangleCLTCompanion.CovarianceRestoration
import Mathlib.MeasureTheory.Measure.CharacteristicFunction
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.LinearAlgebra.Matrix.BilinearForm

/-! Rectangular Gaussian factors and the dependent covariance-restoration
coupling used for sub-exponential observations. No inverse covariance or
independence between the two restored blocks is assumed. -/

open MeasureTheory ProbabilityTheory BoundedContinuousFunction
open scoped BigOperators Matrix

namespace RectangleCLT.Companion

noncomputable section

def rectangularGaussianLaw {p q : ℕ} (B : Matrix (Fin p) (Fin q) ℝ) :
    Measure (Vector p) := (standardGaussian q).map B.mulVec

theorem measurable_rectangular_mulVec {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) : Measurable B.mulVec :=
  (continuous_const.matrix_mulVec continuous_id).measurable

instance rectangularGaussianLaw_isProbability {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) : IsProbabilityMeasure (rectangularGaussianLaw B) :=
  isProbabilityMeasure_map (measurable_rectangular_mulVec B).aemeasurable

private def coordinateDotBilin (p : ℕ) : Vector p →ₗ[ℝ] Vector p →ₗ[ℝ] ℝ where
  toFun x :=
    { toFun := fun y => ∑ j, x j * y j
      map_add' := by intro y z; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro a y
        simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
        exact Finset.sum_congr rfl (fun j _ => by ring) }
  map_add' := by
    intro x y
    ext z
    simp [add_mul, Finset.sum_add_distrib]
  map_smul' := by
    intro a x
    ext y
    simp only [LinearMap.smul_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl (fun j _ => by ring)

private theorem coordinateDotBilin_nondegenerate {p : ℕ}
    (v : Vector p) (hv : v ≠ 0) : coordinateDotBilin p v ≠ 0 := by
  obtain ⟨j, hj⟩ : ∃ j, v j ≠ 0 := by
    by_contra! h
    exact hv (funext h)
  intro h
  have he := congrArg (fun f : Vector p →ₗ[ℝ] ℝ => f (Pi.single j 1)) h
  have he' : v j = 0 := by
    simpa [coordinateDotBilin, Pi.single_apply, mul_ite] using he
  exact hj he'

private theorem coordinateDotBilin_continuous (p : ℕ) :
    Continuous (fun z : Vector p × Vector p => coordinateDotBilin p z.1 z.2) :=
  continuous_finset_sum _ (fun j _ =>
    (continuous_apply j).comp continuous_fst |>.mul
      ((continuous_apply j).comp continuous_snd))

/-- The characteristic function of every finite standard-Gaussian projection. -/
theorem standardGaussian_integral_complex_projection {q : ℕ} (a : Vector q) :
    (∫ z : Vector q, Complex.exp (((∑ j, a j * z j : ℝ) : ℂ) * Complex.I)
      ∂standardGaussian q) =
      Complex.exp (-((∑ j, a j ^ 2 : ℝ) : ℂ) / 2) := by
  classical
  have hprod (z : Vector q) :
      Complex.exp (((∑ j, a j * z j : ℝ) : ℂ) * Complex.I) =
        ∏ j, Complex.exp (((a j * z j : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_sum]
    congr 1
    simp only [Complex.ofReal_sum, Finset.sum_mul]
  simp_rw [hprod]
  have hscalar (j : Fin q) :
      (∫ x : ℝ, Complex.exp (((a j * x : ℝ) : ℂ) * Complex.I)
        ∂gaussianReal 0 1) = Complex.exp (-((a j ^ 2 : ℝ) : ℂ) / 2) := by
    have h := charFun_gaussianReal (μ := 0) (v := 1) (a j)
    simpa only [charFun_apply_real, mul_comm (a j), Complex.ofReal_mul,
      Complex.ofReal_zero, Complex.ofReal_one, mul_zero, zero_mul, one_mul,
      zero_sub, Complex.ofReal_pow] using h
  letI : MeasureSpace ℝ := ⟨gaussianReal 0 1⟩
  change (∫ z : Vector q, ∏ j, Complex.exp (((a j * z j : ℝ) : ℂ) * Complex.I)
    ∂Measure.pi (fun _ => gaussianReal 0 1)) = _
  rw [show Measure.pi (fun _ : Fin q => gaussianReal 0 1) = volume from rfl,
    integral_fintype_prod_eq_prod]
  simp_rw [hscalar]
  rw [← Complex.exp_sum]
  congr 1
  simp only [Complex.ofReal_sum, Finset.sum_neg_distrib, Finset.sum_div]

private theorem projected_normSq_eq_gram {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) (t : Vector p) :
    (∑ i, (∑ j, t j * B j i) ^ 2) =
      dotProduct t ((B * B.transpose).mulVec t) := by
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  simp only [dotProduct, Matrix.vecMul, pow_two]

/-- The pushforward law of a rectangular Gaussian factor depends only on
its row Gram matrix, including in the singular case. -/
theorem rectangularGaussianLaw_eq_of_gram {p q r : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) (C : Matrix (Fin p) (Fin r) ℝ)
    (hgram : B * B.transpose = C * C.transpose) :
    rectangularGaussianLaw B = rectangularGaussianLaw C := by
  apply ext_of_integral_char_eq continuous_probChar probChar_ne_one
    coordinateDotBilin_nondegenerate (coordinateDotBilin_continuous p)
  intro t
  rw [integral_map (measurable_rectangular_mulVec B).aemeasurable
      (char continuous_probChar (coordinateDotBilin_continuous p) t).continuous.measurable.aestronglyMeasurable,
    integral_map (measurable_rectangular_mulVec C).aemeasurable
      (char continuous_probChar (coordinateDotBilin_continuous p) t).continuous.measurable.aestronglyMeasurable]
  have hfun {s : ℕ} (D : Matrix (Fin p) (Fin s) ℝ) (z : Vector s) :
      char continuous_probChar (coordinateDotBilin_continuous p) t (D.mulVec z) =
        Complex.exp (((∑ i, (∑ j, t j * D j i) * z i : ℝ) : ℂ) * Complex.I) := by
    simp only [char_apply, probChar_apply, coordinateDotBilin, Matrix.mulVec,
      dotProduct, Finset.mul_sum, Finset.sum_mul]
    congr 2
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => by ring))
  simp_rw [hfun, standardGaussian_integral_complex_projection,
    projected_normSq_eq_gram, hgram]

theorem rectangularGaussianLaw_eq_gaussianLaw {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) (A : Matrix (Fin p) (Fin p) ℝ)
    (hgram : B * B.transpose = A * A.transpose) :
    rectangularGaussianLaw B = gaussianLaw A :=
  rectangularGaussianLaw_eq_of_gram B A hgram

private def jointColumns {p : ℕ} (D : Matrix (Fin p) (JointIndex p) ℝ) :
    Matrix (Fin p) (Fin (p + p)) ℝ := fun j k => D j (finSumFinEquiv.symm k)

private theorem jointColumns_cross_gram {p : ℕ}
    (D E : Matrix (Fin p) (JointIndex p) ℝ) :
    jointColumns D * (jointColumns E).transpose = D * E.transpose := by
  ext j k
  simp only [Matrix.mul_apply, Matrix.transpose_apply, jointColumns]
  exact Equiv.sum_comp finSumFinEquiv.symm (fun i => D j i * E k i)

/-- An actual common Gaussian probability space restores the covariance,
with the original cross blocks retained. Both marginal laws are identified
with the public square-factor Gaussian laws. -/
theorem jointRestoration_gaussianCoupling_exists {p : ℕ}
    (Q : Matrix (JointIndex p) (JointIndex p) ℝ) (hQ : Q.PosSemidef)
    (AT A : Matrix (Fin p) (Fin p) ℝ)
    (hAT : AT * AT.transpose = covarianceBlock11 Q)
    (hA : A * A.transpose = restoredCovariance Q) :
    ∃ L R : Matrix (Fin p) (Fin (p + p)) ℝ,
      L * L.transpose = covarianceBlock11 Q ∧
      L * R.transpose = covarianceBlock12 Q ∧
      R * L.transpose = covarianceBlock21 Q ∧
      R * R.transpose = covarianceBlock22 Q ∧
      rectangularGaussianLaw L = gaussianLaw AT ∧
      rectangularGaussianLaw (L + R) = gaussianLaw A := by
  obtain ⟨L, R, hLL, hLR, hRL, hRR, hsum⟩ :=
    jointCovariance_restoration_exists Q hQ
  refine ⟨jointColumns L, jointColumns R, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (jointColumns_cross_gram L L).trans hLL
  · exact (jointColumns_cross_gram L R).trans hLR
  · exact (jointColumns_cross_gram R L).trans hRL
  · exact (jointColumns_cross_gram R R).trans hRR
  · apply rectangularGaussianLaw_eq_gaussianLaw
    exact ((jointColumns_cross_gram L L).trans hLL).trans hAT.symm
  · apply rectangularGaussianLaw_eq_gaussianLaw
    have hcols : jointColumns L + jointColumns R = jointColumns (L + R) := rfl
    rw [hcols, jointColumns_cross_gram, hsum, ← hA]

private theorem gaussian_projection_mgf {q : ℕ} (a : Vector q) (t : ℝ) :
    mgf (fun z : Vector q => ∑ j, a j * z j) (standardGaussian q) t =
      Real.exp (t ^ 2 * (∑ j, a j ^ 2) / 2) := by
  classical
  have hind : iIndepFun (fun i (z : Vector q) => a i * z i) (standardGaussian q) :=
    (standardGaussian_iIndepFun q).comp (fun i u => a i * u)
      (fun i => measurable_const.mul measurable_id)
  have hmeas (i : Fin q) : Measurable (fun z : Vector q => a i * z i) :=
    measurable_const.mul (measurable_pi_apply i)
  have hfun : (fun z : Vector q => ∑ j, a j * z j) =
      ∑ i ∈ Finset.univ, fun z : Vector q => a i * z i := by funext z; simp
  rw [hfun, hind.mgf_sum hmeas]
  have hscalar (i : Fin q) :
      mgf (fun z : Vector q => a i * z i) (standardGaussian q) t =
        Real.exp ((a i * t) ^ 2 / 2) := by
    change mgf ((a i) • (fun z : Vector q => z i)) (standardGaussian q) t = _
    rw [mgf_smul_left, ← mgf_id_map (measurable_pi_apply i).aemeasurable,
      standardGaussian_map_eval, standardRealGaussian_mgf]
  simp_rw [hscalar]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl (fun i _ => by ring)

private theorem gaussian_projection_subgaussian {q : ℕ}
    (a : Vector q) (c : ℝ≥0) (hc : (∑ j, a j ^ 2) ≤ c) :
    HasSubgaussianMGF (fun z : Vector q => ∑ j, a j * z j) c
      (standardGaussian q) where
  integrable_exp_mul t := mgf_pos_iff.mp (by rw [gaussian_projection_mgf]; positivity)
  mgf_le t := by
    rw [gaussian_projection_mgf]
    apply Real.exp_le_exp.mpr
    nlinarith [mul_le_mul_of_nonneg_left hc (sq_nonneg t)]

/-- A Gaussian maximum tail bound derived from the actual product Gaussian
law. The coordinates of `B G` may be arbitrarily dependent. -/
theorem standardGaussian_rectangular_norm_tail {p q : ℕ}
    (B : Matrix (Fin p) (Fin q) ℝ) {τ s : ℝ} (hτ : 0 ≤ τ) (hs : 0 ≤ s)
    (hrows : ∀ j, (∑ k, (B j k) ^ 2) ≤ τ ^ 2) :
    (standardGaussian q).real {z | τ * Real.sqrt (2 * s) < ‖B.mulVec z‖} ≤
      (2 * (p : ℝ)) * Real.exp (-s) := by
  classical
  by_cases hτ0 : τ = 0
  · subst τ
    have hB : B = 0 := by
      ext j k
      have hsq := (Finset.single_le_sum (fun i _ => sq_nonneg (B j i))
        (Finset.mem_univ k)).trans (hrows j)
      simpa only [zero_pow (by norm_num : (2 : ℕ) ≠ 0)] using
        (sq_nonpos_iff.mp (by simpa using hsq))
    simp only [hB, Matrix.zero_mulVec, norm_zero, zero_mul, lt_self_iff_false,
      Set.setOf_false, measureReal_empty]
    positivity
  have hτp : 0 < τ := lt_of_le_of_ne hτ (Ne.symm hτ0)
  let r := τ * Real.sqrt (2 * s)
  have hr : 0 ≤ r := mul_nonneg hτ (Real.sqrt_nonneg _)
  have hr2 : r ^ 2 = τ ^ 2 * (2 * s) := by
    dsimp [r]
    rw [mul_pow, Real.sq_sqrt (by positivity)]
  have hexp : Real.exp (-r ^ 2 / (2 * τ ^ 2)) = Real.exp (-s) := by
    congr 1
    rw [hr2]
    field_simp [hτ0]
    ring
  let E : Fin p → Set (Vector q) := fun j =>
    {z | r ≤ B.mulVec z j} ∪ {z | r ≤ -(B.mulVec z j)}
  have hcoord (j : Fin p) : (standardGaussian q).real (E j) ≤
      2 * Real.exp (-s) := by
    have hpos := (gaussian_projection_subgaussian (B j) ⟨τ ^ 2, sq_nonneg τ⟩
      (hrows j)).measure_ge_le hr
    have hnegrow : (∑ k, (-B j k) ^ 2) ≤ (⟨τ ^ 2, sq_nonneg τ⟩ : ℝ≥0) := by
      simpa only [neg_sq, NNReal.coe_mk] using hrows j
    have hneg := (gaussian_projection_subgaussian (fun k => -B j k)
      ⟨τ ^ 2, sq_nonneg τ⟩ hnegrow).measure_ge_le hr
    simp only [NNReal.coe_mk, hexp] at hpos hneg
    have hnegfun (z : Vector q) : (∑ k, -B j k * z k) = -(B.mulVec z j) := by
      simp only [Matrix.mulVec, dotProduct, neg_mul, Finset.sum_neg_distrib]
    simp_rw [hnegfun] at hneg
    exact (measureReal_union_le _ _).trans (by
      change (standardGaussian q).real {z | r ≤ B.mulVec z j} +
        (standardGaussian q).real {z | r ≤ -(B.mulVec z j)} ≤ _
      change (standardGaussian q).real {z | r ≤ B.mulVec z j} ≤ _ at hpos
      linarith)
  have hsub : {z : Vector q | r < ‖B.mulVec z‖} ⊆ ⋃ j, E j := by
    intro z hz
    by_contra h
    have hsmall (j : Fin p) : |B.mulVec z j| ≤ r := by
      have hj : z ∉ E j := fun hj => h (Set.mem_iUnion.mpr ⟨j, hj⟩)
      have hp : ¬r ≤ B.mulVec z j := fun hh => hj (Or.inl hh)
      have hn : ¬r ≤ -(B.mulVec z j) := fun hh => hj (Or.inr hh)
      exact abs_le.mpr ⟨by linarith, le_of_not_ge hp⟩
    exact (not_le_of_gt hz) ((pi_norm_le_iff_of_nonneg hr).mpr
      (fun j => by simpa only [Real.norm_eq_abs] using hsmall j))
  calc
    _ ≤ (standardGaussian q).real (⋃ j, E j) := measureReal_mono hsub
    _ ≤ ∑ j, (standardGaussian q).real (E j) := measureReal_iUnion_fintype_le _
    _ ≤ ∑ _j : Fin p, 2 * Real.exp (-s) :=
      Finset.sum_le_sum (fun j _ => hcoord j)
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul]; ring

/-- The joint coordinates on the original probability space. -/
def jointValue {Ω : Type*} {p : ℕ} (U V : Ω → Vector p) (ω : Ω) :
    JointIndex p → ℝ := Sum.elim (U ω) (V ω)

/-- The literal joint second-moment matrix. Under joint centeredness this
is the block covariance of the two vectors. -/
def jointSecondMoment {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (μ : Measure Ω) (U V : Ω → Vector p) : Matrix (JointIndex p) (JointIndex p) ℝ :=
  fun a b => ∫ ω, jointValue U V ω a * jointValue U V ω b ∂μ

private theorem joint_product_integrable
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} {μ : Measure Ω}
    {U V : Ω → Vector p}
    (hL2 : ∀ a, MemLp (fun ω => jointValue U V ω a) (2 : ENNReal) μ)
    (a b : JointIndex p) :
    Integrable (fun ω => jointValue U V ω a * jointValue U V ω b) μ := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  exact (hL2 a).integrable_mul (hL2 b)

theorem jointSecondMoment_posSemidef
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} {μ : Measure Ω}
    {U V : Ω → Vector p}
    (hL2 : ∀ a, MemLp (fun ω => jointValue U V ω a) (2 : ENNReal) μ) :
    (jointSecondMoment μ U V).PosSemidef := by
  classical
  constructor
  · rw [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
    ext a b
    simp only [Matrix.transpose_apply, jointSecondMoment, mul_comm]
  · intro v
    have hpoint (ω : Ω) : (∑ a, v a * jointValue U V ω a) ^ 2 =
        ∑ a, ∑ b, v a * (jointValue U V ω a * jointValue U V ω b) * v b := by
      rw [pow_two, Finset.sum_mul_sum]
      exact Finset.sum_congr rfl (fun a _ =>
        Finset.sum_congr rfl (fun b _ => by ring))
    have hi (a b : JointIndex p) : Integrable
        (fun ω => v a * (jointValue U V ω a * jointValue U V ω b) * v b) μ :=
      ((joint_product_integrable hL2 a b).const_mul (v a)).mul_const (v b)
    have hnon := integral_nonneg (μ := μ)
      (fun ω => sq_nonneg (∑ a, v a * jointValue U V ω a))
    simp_rw [hpoint] at hnon
    rw [integral_finset_sum _ (fun a _ =>
      integrable_finset_sum _ (fun b _ => hi a b))] at hnon
    simp_rw [integral_finset_sum _ (fun b _ => hi _ b), integral_mul_const,
      integral_const_mul] at hnon
    simpa only [dotProduct, Matrix.mulVec, Pi.star_apply, star_trivial,
      Finset.mul_sum, jointSecondMoment, mul_assoc] using hnon

theorem jointSecondMoment_block11
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω)
    (U V : Ω → Vector p)
    (hmean : ∀ a, (∫ ω, jointValue U V ω a ∂μ) = 0) :
    covarianceBlock11 (jointSecondMoment μ U V) = covariance μ U := by
  ext j k
  have hj := hmean (Sum.inl j)
  have hk := hmean (Sum.inl k)
  change (∫ ω, U ω j ∂μ) = 0 at hj
  change (∫ ω, U ω k ∂μ) = 0 at hk
  simp only [covarianceBlock11, Matrix.submatrix_apply, jointSecondMoment,
    jointValue, Sum.elim_inl, covariance, hj, hk, zero_mul, sub_zero]

theorem jointSecondMoment_block22
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} (μ : Measure Ω)
    (U V : Ω → Vector p)
    (hmean : ∀ a, (∫ ω, jointValue U V ω a ∂μ) = 0) :
    covarianceBlock22 (jointSecondMoment μ U V) = covariance μ V := by
  ext j k
  have hj := hmean (Sum.inr j)
  have hk := hmean (Sum.inr k)
  change (∫ ω, V ω j ∂μ) = 0 at hj
  change (∫ ω, V ω k ∂μ) = 0 at hk
  simp only [covarianceBlock22, Matrix.submatrix_apply, jointSecondMoment,
    jointValue, Sum.elim_inr, covariance, hj, hk, zero_mul, sub_zero]

theorem jointSecondMoment_restoredCovariance
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ} {μ : Measure Ω}
    [IsProbabilityMeasure μ] (U V : Ω → Vector p)
    (hL2 : ∀ a, MemLp (fun ω => jointValue U V ω a) (2 : ENNReal) μ)
    (hmean : ∀ a, (∫ ω, jointValue U V ω a ∂μ) = 0) :
    restoredCovariance (jointSecondMoment μ U V) = covariance μ (U + V) := by
  ext j k
  have hUi (j : Fin p) : Integrable (fun ω => U ω j) μ :=
    (hL2 (Sum.inl j)).integrable (by norm_num)
  have hVi (j : Fin p) : Integrable (fun ω => V ω j) μ :=
    (hL2 (Sum.inr j)).integrable (by norm_num)
  have hsum (j : Fin p) : (∫ ω, (U + V) ω j ∂μ) = 0 := by
    change (∫ ω, U ω j + V ω j ∂μ) = 0
    rw [integral_add (hUi j) (hVi j)]
    change (∫ ω, jointValue U V ω (Sum.inl j) ∂μ) +
      (∫ ω, jointValue U V ω (Sum.inr j) ∂μ) = 0
    rw [hmean, hmean, add_zero]
  have hUU := joint_product_integrable hL2 (Sum.inl j) (Sum.inl k)
  have hUV := joint_product_integrable hL2 (Sum.inl j) (Sum.inr k)
  have hVU := joint_product_integrable hL2 (Sum.inr j) (Sum.inl k)
  have hVV := joint_product_integrable hL2 (Sum.inr j) (Sum.inr k)
  change Integrable (fun ω => U ω j * U ω k) μ at hUU
  change Integrable (fun ω => U ω j * V ω k) μ at hUV
  change Integrable (fun ω => V ω j * U ω k) μ at hVU
  change Integrable (fun ω => V ω j * V ω k) μ at hVV
  simp only [restoredCovariance_apply, jointSecondMoment, jointValue,
    Sum.elim_inl, Sum.elim_inr, covariance, hsum, zero_mul, sub_zero]
  have hpoint (ω : Ω) : (U + V) ω j * (U + V) ω k =
      ((U ω j * U ω k + U ω j * V ω k) + V ω j * U ω k) + V ω j * V ω k := by
    simp only [Pi.add_apply]
    ring
  simp_rw [hpoint]
  rw [integral_add ((hUU.add hUV).add hVU) hVV,
    integral_add (hUU.add hUV) hVU, integral_add hUU hUV]

end
end RectangleCLT.Companion
