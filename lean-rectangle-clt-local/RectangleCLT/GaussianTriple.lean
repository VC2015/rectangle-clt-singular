import RectangleCLT.GaussianFaces
import RectangleCLT.GaussianStein
import Mathlib.Tactic.FinCases

/-!
# The three-face Schur-complement estimate

The determinant cost and the regression coefficient are bounded together.
These are the algebraic estimates used in the Gaussian three-face argument;
the Gaussian face integration and derivative estimates are separate steps.
-/

open scoped BigOperators Matrix NNReal

namespace RectangleCLT.GaussianTriple

noncomputable section

def correlationMatrix (ρ α β : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![1, ρ, α; ρ, 1, β; α, β, 1]

def pairDeterminant (ρ : ℝ) : ℝ := 1 - ρ ^ 2

def regressionFirst (ρ α β : ℝ) : ℝ := (α - ρ * β) / pairDeterminant ρ

def regressionSecond (ρ α β : ℝ) : ℝ := (β - ρ * α) / pairDeterminant ρ

def regressionNormSq (ρ α β : ℝ) : ℝ :=
  regressionFirst ρ α β ^ 2 + regressionSecond ρ α β ^ 2

def schurComplement (ρ α β : ℝ) : ℝ :=
  1 - α * regressionFirst ρ α β - β * regressionSecond ρ α β

theorem pairDeterminant_lower {ρ c : ℝ} (hc : 0 ≤ c) (hc1 : c ≤ 1)
    (hρ : |ρ| ≤ 1 - c) : c ≤ pairDeterminant ρ := by
  have hbound : |ρ| ^ 2 ≤ (1 - c) ^ 2 :=
    (sq_le_sq₀ (abs_nonneg ρ) (by linarith)).mpr hρ
  rw [sq_abs] at hbound
  unfold pairDeterminant
  nlinarith [sq_nonneg c]

theorem regression_equations {ρ α β : ℝ} (hd : pairDeterminant ρ ≠ 0) :
    regressionFirst ρ α β + ρ * regressionSecond ρ α β = α ∧
    ρ * regressionFirst ρ α β + regressionSecond ρ α β = β := by
  constructor <;> unfold regressionFirst regressionSecond
  · field_simp
    simp only [pairDeterminant]
    ring
  · field_simp
    simp only [pairDeterminant]
    ring

theorem determinant_eq {ρ α β : ℝ} (hd : pairDeterminant ρ ≠ 0) :
    (correlationMatrix ρ α β).det = pairDeterminant ρ * schurComplement ρ α β := by
  simp only [Matrix.det_fin_three, correlationMatrix, Matrix.of_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Matrix.cons_val_fin_one]
  unfold schurComplement regressionFirst regressionSecond
  field_simp
  simp only [pairDeterminant]
  ring

def schurTestVector (ρ α β : ℝ) : Fin 3 → ℝ :=
  ![-regressionFirst ρ α β, -regressionSecond ρ α β, 1]

theorem schurTestVector_normSq (ρ α β : ℝ) :
    vectorNormSq (schurTestVector ρ α β) = 1 + regressionNormSq ρ α β := by
  simp [vectorNormSq, schurTestVector, regressionNormSq, Fin.sum_univ_succ]
  ring

theorem schurTestVector_quadratic {ρ α β : ℝ} (hd : pairDeterminant ρ ≠ 0) :
    matrixQuadratic (correlationMatrix ρ α β) (schurTestVector ρ α β) =
      schurComplement ρ α β := by
  obtain ⟨h₁, h₂⟩ := regression_equations (α := α) (β := β) hd
  have heq : matrixQuadratic (correlationMatrix ρ α β) (schurTestVector ρ α β) =
      1 - 2 * α * regressionFirst ρ α β - 2 * β * regressionSecond ρ α β +
        regressionFirst ρ α β ^ 2 +
        2 * ρ * regressionFirst ρ α β * regressionSecond ρ α β +
        regressionSecond ρ α β ^ 2 := by
    simp [matrixQuadratic, correlationMatrix, schurTestVector, Fin.sum_univ_succ]
    ring
  rw [heq]
  unfold schurComplement
  nlinarith [congrArg (fun t => t * regressionFirst ρ α β) h₁,
    congrArg (fun t => t * regressionSecond ρ α β) h₂]

/-- Testing the local spectral inequality at `(-B⁻¹r,1)` retains the entire
regression norm in the Schur complement. -/
theorem schurComplement_lower {ρ α β a : ℝ} (hd : pairDeterminant ρ ≠ 0)
    (hlower : ∀ u : Fin 3 → ℝ,
      a * vectorNormSq u ≤ matrixQuadratic (correlationMatrix ρ α β) u) :
    a * (1 + regressionNormSq ρ α β) ≤ schurComplement ρ α β := by
  simpa only [schurTestVector_normSq, schurTestVector_quadratic hd] using
    hlower (schurTestVector ρ α β)

theorem regressionNormSq_nonneg (ρ α β : ℝ) : 0 ≤ regressionNormSq ρ α β :=
  add_nonneg (sq_nonneg _) (sq_nonneg _)

theorem determinant_pos {ρ α β a : ℝ} (ha : 0 < a) (hd : 0 < pairDeterminant ρ)
    (hlower : ∀ u : Fin 3 → ℝ,
      a * vectorNormSq u ≤ matrixQuadratic (correlationMatrix ρ α β) u) :
    0 < (correlationMatrix ρ α β).det := by
  rw [determinant_eq hd.ne']
  apply mul_pos hd
  exact (mul_pos ha (by linarith [regressionNormSq_nonneg ρ α β])).trans_le
    (schurComplement_lower hd.ne' hlower)

/-- The combined regression/determinant cost is of order `1/(a*c)`, avoiding
the additional inverse power produced by bounding the two factors separately. -/
theorem regression_weight_div_det_le {ρ α β a c : ℝ} (ha : 0 < a)
    (hc : 0 < c) (hcd : c ≤ pairDeterminant ρ)
    (hlower : ∀ u : Fin 3 → ℝ,
      a * vectorNormSq u ≤ matrixQuadratic (correlationMatrix ρ α β) u) :
    (1 + Real.sqrt (regressionNormSq ρ α β)) / (correlationMatrix ρ α β).det ≤
      2 / (a * c) := by
  have hd : 0 < pairDeterminant ρ := hc.trans_le hcd
  have hdet := determinant_pos ha hd hlower
  have hs := schurComplement_lower hd.ne' hlower
  have hB := regressionNormSq_nonneg ρ α β
  have hroot : 1 + Real.sqrt (regressionNormSq ρ α β) ≤
      2 * (1 + regressionNormSq ρ α β) := by
    have hsq := Real.sq_sqrt hB
    nlinarith [sq_nonneg (Real.sqrt (regressionNormSq ρ α β) - 1)]
  apply (div_le_div_iff₀ hdet (mul_pos ha hc)).mpr
  calc
    _ ≤ (2 * (1 + regressionNormSq ρ α β)) * (a * pairDeterminant ρ) :=
      mul_le_mul hroot (mul_le_mul_of_nonneg_left hcd ha.le)
        (mul_nonneg ha.le hc.le) (by positivity)
    _ = 2 * (pairDeterminant ρ * (a * (1 + regressionNormSq ρ α β))) := by ring
    _ ≤ 2 * (pairDeterminant ρ * schurComplement ρ α β) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hs hd.le) (by norm_num)
    _ = _ := by rw [← determinant_eq hd.ne']

end

end RectangleCLT.GaussianTriple

namespace RectangleCLT.CompatibleFaceTuple

variable {p : ℕ} (S : CompatibleFaceTuple p 3)

theorem gram_three_eq {Q : Matrix (Fin p) (Fin p) ℝ}
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i = 1) :
    S.gram Q = GaussianTriple.correlationMatrix (S.gram Q 0 1)
      (S.gram Q 0 2) (S.gram Q 1 2) := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact S.gram_diagonal hdiag 0
  · rfl
  · rfl
  · exact S.gram_symmetric hsym 1 0
  · exact S.gram_diagonal hdiag 1
  · rfl
  · exact S.gram_symmetric hsym 2 0
  · exact S.gram_symmetric hsym 2 1
  · exact S.gram_diagonal hdiag 2

/-- The Schur regression bound for an actual compatible signed triple from
a locally conditioned covariance matrix. The full matrix may be singular. -/
theorem triple_regression_weight_div_det_le {Q : Matrix (Fin p) (Fin p) ℝ} {a : ℝ}
    (hQ : LocalCovarianceLower Q 3 a) (ha : 0 < a)
    (hsym : ∀ i j, Q i j = Q j i) (hdiag : ∀ i, Q i i = 1)
    (hc : 0 < pairGap Q) :
    (1 + Real.sqrt (GaussianTriple.regressionNormSq
      (S.gram Q 0 1) (S.gram Q 0 2) (S.gram Q 1 2))) / (S.gram Q).det ≤
      2 / (a * pairGap Q) := by
  have hrep := S.gram_three_eq hsym hdiag
  have hcd := GaussianTriple.pairDeterminant_lower hc.le (pairGap_le_one Q)
    (S.abs_gram_offDiagonal (Q := Q) 0 1 (by decide))
  have hlower : ∀ u : Fin 3 → ℝ, a * vectorNormSq u ≤
      matrixQuadratic (GaussianTriple.correlationMatrix
        (S.gram Q 0 1) (S.gram Q 0 2) (S.gram Q 1 2)) u := by
    intro u
    rw [← hrep]
    exact S.gram_lower hQ u
  simpa only [← hrep] using GaussianTriple.regression_weight_div_det_le ha hc hcd hlower

end RectangleCLT.CompatibleFaceTuple

namespace RectangleCLT

open MeasureTheory ProbabilityTheory

/-- Product-Gaussian integration by parts with integrability hypotheses. This
version permits polynomial Gaussian weights in the test function; it does not
assume that such weights are bounded or that boundary terms vanish. -/
theorem standardGaussian_coordinate_stein_of_integrable {p : ℕ} (j : Fin p)
    {g g' : Vector p → ℝ}
    (hgderiv : ∀ x, HasDerivAt (fun t => g (Function.update x j t)) (g' x) (x j))
    (hg : Integrable g (standardGaussian p))
    (hg' : Integrable g' (standardGaussian p))
    (hxg : Integrable (fun x => x j * g x) (standardGaussian p)) :
    (∫ x, x j * g x ∂standardGaussian p) = ∫ x, g' x ∂standardGaussian p := by
  cases p with
  | zero => exact Fin.elim0 j
  | succ n =>
    let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) j
    have hmp : MeasurePreserving e (standardGaussian (n + 1))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      measurePreserving_piFinSuccAbove (fun _ => gaussianReal 0 1) j
    have hinv := MeasurePreserving.symm e hmp
    have hplain : Integrable (fun z : ℝ × Vector n => g (e.symm z))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      (hinv.integrable_comp_emb e.symm.measurableEmbedding).mpr hg
    have hleft : Integrable
        (fun z : ℝ × Vector n => (e.symm z) j * g (e.symm z))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      (hinv.integrable_comp_emb e.symm.measurableEmbedding).mpr hxg
    have hright : Integrable (fun z : ℝ × Vector n => g' (e.symm z))
        ((gaussianReal 0 1).prod (standardGaussian n)) :=
      (hinv.integrable_comp_emb e.symm.measurableEmbedding).mpr hg'
    have hscalar : ∀ᵐ y : Vector n ∂standardGaussian n,
        (∫ t, (e.symm (t, y)) j * g (e.symm (t, y)) ∂gaussianReal 0 1) =
          ∫ t, g' (e.symm (t, y)) ∂gaussianReal 0 1 := by
      filter_upwards [hplain.prod_left_ae, hleft.prod_left_ae, hright.prod_left_ae]
        with y hy hyx hyd
      have hpoint : ∀ t, HasDerivAt (fun a => g (j.insertNth a y))
          (g' (j.insertNth t y)) t := by
        intro t
        simpa only [Fin.insertNth_apply_same, Fin.update_insertNth] using
          hgderiv (j.insertNth t y)
      have hs := standardRealGaussian_stein_of_integrable hpoint
        (by simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hy)
        (by simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hyd)
        (by simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hyx)
      simpa [e, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using hs
    calc
      _ = ∫ z : ℝ × Vector n, (e.symm z) j * g (e.symm z)
          ∂(gaussianReal 0 1).prod (standardGaussian n) :=
        (hinv.integral_comp' (fun x => x j * g x)).symm
      _ = ∫ y : Vector n, ∫ t, (e.symm (t, y)) j * g (e.symm (t, y))
          ∂gaussianReal 0 1 ∂standardGaussian n := integral_prod_symm _ hleft
      _ = ∫ y : Vector n, ∫ t, g' (e.symm (t, y))
          ∂gaussianReal 0 1 ∂standardGaussian n := integral_congr_ae hscalar
      _ = ∫ z : ℝ × Vector n, g' (e.symm z)
          ∂(gaussianReal 0 1).prod (standardGaussian n) :=
        (integral_prod_symm _ hright).symm
      _ = ∫ x, g' x ∂standardGaussian (n + 1) := hinv.integral_comp' g'

theorem standardGaussian_directional_stein_of_integrable {p : ℕ} (u : Vector p)
    {g : Vector p → ℝ} {g' : Fin p → Vector p → ℝ}
    (hgderiv : ∀ j x, HasDerivAt (fun t => g (Function.update x j t)) (g' j x) (x j))
    (hg : Integrable g (standardGaussian p))
    (hg' : ∀ j, Integrable (g' j) (standardGaussian p))
    (hxg : ∀ j, Integrable (fun x => x j * g x) (standardGaussian p)) :
    (∫ x, faceDot u x * g x ∂standardGaussian p) =
      ∫ x, ∑ j, u j * g' j x ∂standardGaussian p := by
  have heq (x : Vector p) : faceDot u x * g x = ∑ j, u j * (x j * g x) := by
    simp only [faceDot, Finset.sum_mul, mul_assoc]
  simp_rw [heq]
  rw [integral_finset_sum Finset.univ (fun j _ => (hxg j).const_mul (u j)),
    integral_finset_sum Finset.univ (fun j _ => (hg' j).const_mul (u j))]
  simp only [integral_const_mul]
  apply Finset.sum_congr rfl
  intro j _
  rw [standardGaussian_coordinate_stein_of_integrable j (hgderiv j) hg (hg' j) (hxg j)]

theorem standardGaussian_memLp_faceDot {p : ℕ} (u : Vector p) (q : ℝ≥0) :
    MemLp (faceDot u) q (standardGaussian p) := by
  exact memLp_finset_sum Finset.univ
    (fun j _ => (standardGaussian_memLp_coordinate p j q).const_mul (u j))

theorem standardGaussian_integrable_faceDot {p : ℕ} (u : Vector p) :
    Integrable (faceDot u) (standardGaussian p) := by
  exact integrable_finset_sum Finset.univ
    (fun j _ => (standardGaussian_integrable_coordinate p j).const_mul (u j))

theorem standardGaussian_integrable_faceDot_product {p : ℕ} (u v : Vector p) :
    Integrable (fun z => faceDot u z * faceDot v z) (standardGaussian p) := by
  haveI : ENNReal.HolderTriple (2 : ENNReal) 2 1 :=
    ⟨by simpa only [inv_one] using ENNReal.inv_two_add_inv_two⟩
  have hu : MemLp (faceDot u) (2 : ENNReal) (standardGaussian p) := by
    simpa using standardGaussian_memLp_faceDot u 2
  have hv : MemLp (faceDot v) (2 : ENNReal) (standardGaussian p) := by
    simpa using standardGaussian_memLp_faceDot v 2
  exact hu.integrable_mul hv

theorem hasDerivAt_faceDot_update {p : ℕ} (u z : Vector p) (j : Fin p) :
    HasDerivAt (fun t => faceDot u (Function.update z j t)) (u j) (z j) := by
  classical
  have heq (t : ℝ) : faceDot u (Function.update z j t) =
      faceDot u z + (t - z j) * u j := by
    have hf : (fun k => u k * Function.update z j t k) =
        Function.update (fun k => u k * z k) j (u j * t) := by
      ext k
      by_cases hk : k = j
      · subst k; simp
      · simp [Function.update_of_ne hk]
    unfold faceDot
    rw [hf]
    rw [Finset.sum_update_of_mem (Finset.mem_univ j)]
    have hs := Finset.sum_sdiff (f := fun k => u k * z k)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ j))
    simp only [Finset.sum_singleton] at hs
    linarith
  simp_rw [heq]
  simpa using (hasDerivAt_const (z j) (faceDot u z)).add
    (((hasDerivAt_id (z j)).sub_const (z j)).mul_const (u j))

namespace FaceSmoother

variable {p : ℕ} (s : FaceSmoother p)

noncomputable def softFaceDirectional (S : Finset (Face p)) (y x : Vector p) : ℝ :=
  s.softFaceWeight S x / s.bandwidth *
    ((∑ f ∈ S, normalDot f y) - ((S.card : ℝ) + 1) * (s.weights x).directionalMean y)

theorem hasDerivAt_softFaceDirectional (S : Finset (Face p)) (y x : Vector p) (t : ℝ) :
    HasDerivAt (fun a => s.softFaceWeight S (line x y a))
      (s.softFaceDirectional S y (line x y t)) t :=
  s.hasDerivAt_softFaceWeight_line S x y t

@[fun_prop] theorem continuous_softFaceDirectional (S : Finset (Face p)) (y : Vector p) :
    Continuous (s.softFaceDirectional S y) := by
  apply ((s.continuous_softFaceWeight S).div_const _).mul
  apply continuous_const.sub
  apply continuous_const.mul
  simp only [FaceWeights.directionalMean_eq]
  exact continuous_finset_sum _ (fun j _ => (s.continuous_v j).mul continuous_const)

theorem abs_softFaceDirectional_le (S : Finset (Face p)) (y x : Vector p) :
    |s.softFaceDirectional S y x| ≤
      ((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) / s.bandwidth := by
  have hcard : 0 ≤ (S.card : ℝ) + 1 := by positivity
  have hsum : |(∑ f ∈ S, normalDot f y) -
      ((S.card : ℝ) + 1) * (s.weights x).directionalMean y| ≤
      (∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖ := by
    calc
      _ ≤ |∑ f ∈ S, normalDot f y| +
          |((S.card : ℝ) + 1) * (s.weights x).directionalMean y| := abs_sub _ _
      _ ≤ _ := add_le_add (Finset.abs_sum_le_sum_abs _ _) (by
        rw [abs_mul, abs_of_nonneg hcard]
        exact mul_le_mul_of_nonneg_left ((s.weights x).abs_directionalMean_le_norm y) hcard)
  unfold softFaceDirectional
  rw [abs_mul, abs_div, abs_of_nonneg (s.softFaceWeight_nonneg S x),
    abs_of_pos s.bandwidth_pos]
  calc
    _ ≤ (1 / s.bandwidth) *
        ((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) :=
      mul_le_mul (div_le_div_of_nonneg_right (s.softFaceWeight_le_one S x) s.bandwidth_pos.le)
        hsum (abs_nonneg _) (div_nonneg zero_le_one s.bandwidth_pos.le)
    _ = _ := by ring

private theorem gaussianFactor_update (A : Matrix (Fin p) (Fin p) ℝ)
    (z : Vector p) (j : Fin p) (t : ℝ) (x : Vector p) :
    A.mulVec (Function.update z j t) + x =
      line (A.mulVec z + x) (fun k => A k j) (t - z j) := by
  classical
  have heq : Function.update z j t =
      z + (t - z j) • (Pi.single j (1 : ℝ) : Vector p) := by
    ext k
    by_cases hk : k = j
    · subst k; simp
    · simp [Function.update_of_ne hk, Pi.single_eq_of_ne hk]
  rw [heq, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_single_one]
  ext k
  simp only [line, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Matrix.transpose_apply]
  ring

/-- Actual coordinate-slice derivatives of a soft face weight evaluated on a
Gaussian factor. This is the derivative hypothesis used by Gaussian Stein. -/
theorem hasDerivAt_softFaceWeight_gaussian_slice (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x z : Vector p) (j : Fin p) :
    HasDerivAt (fun t => s.softFaceWeight S (A.mulVec (Function.update z j t) + x))
      (s.softFaceDirectional S (fun k => A k j) (A.mulVec z + x)) (z j) := by
  have hd0 : HasDerivAt
      (fun a => s.softFaceWeight S (line (A.mulVec z + x) (fun k => A k j) a))
      (s.softFaceDirectional S (fun k => A k j) (A.mulVec z + x)) (z j - z j) := by
    simpa only [sub_self, line_zero] using
      s.hasDerivAt_softFaceDirectional S (fun k => A k j) (A.mulVec z + x) 0
  have hd := hd0.comp
    (h := fun t : ℝ => t - z j) (z j) ((hasDerivAt_id (z j)).sub_const (z j))
  simpa only [Function.comp_apply, sub_self, line_zero, mul_one,
    gaussianFactor_update] using hd

theorem softFaceDirectional_mulVec (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (u x : Vector p) :
    s.softFaceDirectional S (A.mulVec u) x =
      ∑ j, u j * s.softFaceDirectional S (fun k => A k j) x := by
  have hnormal (f : Face p) : normalDot f (A.mulVec u) =
      ∑ j, u j * normalDot f (fun k => A k j) := by
    cases hf : f.2 <;>
      simp only [normalDot, hf, Bool.false_eq_true, ↓reduceIte,
        Matrix.mulVec, dotProduct, Finset.sum_neg_distrib]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hmean : (s.weights x).directionalMean (A.mulVec u) =
      ∑ j, u j * (s.weights x).directionalMean (fun k => A k j) := by
    simp only [FaceWeights.directionalMean_eq, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold softFaceDirectional
  rw [hmean]
  simp_rw [hnormal]
  rw [Finset.sum_comm]
  simp only [Finset.mul_sum, mul_sub, Finset.sum_sub_distrib]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro f _
    ring
  · apply Finset.sum_congr rfl
    intro j _
    ring

private theorem integrable_softFaceWeight_factor (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x : Vector p) :
    Integrable (fun z => s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
  apply (integrable_const (1 : ℝ)).mono'
    (((s.continuous_softFaceWeight S).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Function.comp_apply, id_eq, Real.norm_eq_abs,
      abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
      s.softFaceWeight_le_one S (A.mulVec z + x))

private theorem integrable_softFaceDirectional_factor (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y : Vector p) :
    Integrable (fun z => s.softFaceDirectional S y (A.mulVec z + x)) (standardGaussian p) := by
  apply (integrable_const (((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) /
    s.bandwidth)).mono'
    (((s.continuous_softFaceDirectional S y).comp
      ((continuous_const.matrix_mulVec continuous_id).add continuous_const)).measurable.aestronglyMeasurable)
  exact ae_of_all _ (fun z => by
    simpa only [Real.norm_eq_abs] using s.abs_softFaceDirectional_le S y (A.mulVec z + x))

/-- Sparse dual-normal integration by parts for the actual positive soft-face
kernel. The direction `u` is arbitrary; selecting a local Gram dual normal
later only uses local, rather than full, covariance nondegeneracy. -/
theorem softFaceWeight_gaussian_directional_stein (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u : Vector p) :
    (∫ z, faceDot u z * s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) =
      ∫ z, s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x) ∂standardGaussian p := by
  have hg := s.integrable_softFaceWeight_factor A S x
  have hd (j : Fin p) := s.integrable_softFaceDirectional_factor A S x (fun k => A k j)
  have hxg (j : Fin p) : Integrable
      (fun z => z j * s.softFaceWeight S (A.mulVec z + x)) (standardGaussian p) := by
    have hi := (standardGaussian_integrable_coordinate p j).bdd_mul hg.aestronglyMeasurable
      ⟨1, fun z => by
        simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
          s.softFaceWeight_le_one S (A.mulVec z + x)⟩
    simpa only [mul_comm] using hi
  have hs := standardGaussian_directional_stein_of_integrable u
    (fun j z => s.hasDerivAt_softFaceWeight_gaussian_slice A S x z j) hg hd hxg
  simpa only [← s.softFaceDirectional_mulVec] using hs

private theorem softFaceWeight_bdd_factor (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x : Vector p) :
    ∃ C : ℝ, ∀ z, ‖s.softFaceWeight S (A.mulVec z + x)‖ ≤ C := by
  refine ⟨1, fun z => ?_⟩
  simpa only [Real.norm_eq_abs, abs_of_nonneg (s.softFaceWeight_nonneg S _)] using
    s.softFaceWeight_le_one S (A.mulVec z + x)

private theorem softFaceDirectional_bdd_factor (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x y : Vector p) :
    ∃ C : ℝ, ∀ z, ‖s.softFaceDirectional S y (A.mulVec z + x)‖ ≤ C := by
  refine ⟨((∑ f ∈ S, |normalDot f y|) + ((S.card : ℝ) + 1) * ‖y‖) / s.bandwidth,
    fun z => ?_⟩
  exact s.abs_softFaceDirectional_le S y (A.mulVec z + x)

/-- The weighted soft-face Stein identity, with the Gaussian linear weight
differentiated explicitly. Its correction is the exact inner product `u·v`.
All Gaussian polynomial integrability is discharged in the proof. -/
theorem softFaceWeight_gaussian_weighted_stein (A : Matrix (Fin p) (Fin p) ℝ)
    (S : Finset (Face p)) (x u v : Vector p) :
    (∫ z, faceDot u z * (faceDot v z * s.softFaceWeight S (A.mulVec z + x))
      ∂standardGaussian p) =
      faceDot u v * (∫ z, s.softFaceWeight S (A.mulVec z + x) ∂standardGaussian p) +
        ∫ z, faceDot v z * s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x)
          ∂standardGaussian p := by
  let P : Vector p → ℝ := fun z => s.softFaceWeight S (A.mulVec z + x)
  let D : Fin p → Vector p → ℝ :=
    fun j z => s.softFaceDirectional S (fun k => A k j) (A.mulVec z + x)
  have hP := s.integrable_softFaceWeight_factor A S x
  have hD (j : Fin p) := s.integrable_softFaceDirectional_factor A S x (fun k => A k j)
  have hbP := s.softFaceWeight_bdd_factor A S x
  have hmP := hP.aestronglyMeasurable
  have hdotP : Integrable (fun z => faceDot v z * P z) (standardGaussian p) := by
    simpa only [mul_comm] using
      (standardGaussian_integrable_faceDot v).bdd_mul hmP hbP
  have hdotD (j : Fin p) : Integrable (fun z => faceDot v z * D j z) (standardGaussian p) := by
    simpa only [mul_comm] using
      (standardGaussian_integrable_faceDot v).bdd_mul (hD j).aestronglyMeasurable
        (s.softFaceDirectional_bdd_factor A S x (fun k => A k j))
  have hxg (j : Fin p) : Integrable
      (fun z => z j * (faceDot v z * P z)) (standardGaussian p) := by
    have hbase : Integrable (fun z => z j * faceDot v z) (standardGaussian p) := by
      have heq : (fun z : Vector p => z j) = faceDot (localBasisVector j) := by
        funext z
        simp [faceDot, localBasisVector]
      have hh := standardGaussian_integrable_faceDot_product (localBasisVector j) v
      simpa only [← heq] using hh
    simpa only [mul_comm, mul_left_comm, mul_assoc] using hbase.bdd_mul hmP hbP
  have hgrad (j : Fin p) : Integrable
      (fun z => v j * P z + faceDot v z * D j z) (standardGaussian p) :=
    (hP.const_mul (v j)).add (hdotD j)
  have hs := standardGaussian_directional_stein_of_integrable u
    (g := fun z => faceDot v z * P z)
    (g' := fun j z => v j * P z + faceDot v z * D j z)
    (fun j z => by
      convert (hasDerivAt_faceDot_update v z j).mul
        (s.hasDerivAt_softFaceWeight_gaussian_slice A S x z j) using 1
      simp only [P, D, Function.update_eq_self]) hdotP hgrad hxg
  rw [hs]
  have hpoint (z : Vector p) :
      (∑ j, u j * (v j * P z + faceDot v z * D j z)) =
        faceDot u v * P z + faceDot v z *
          s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x) := by
    rw [s.softFaceDirectional_mulVec]
    simp only [faceDot, mul_add, Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, D]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      ring
  simp_rw [hpoint]
  have hlast : Integrable
      (fun z => faceDot v z * s.softFaceDirectional S (A.mulVec u) (A.mulVec z + x))
      (standardGaussian p) := by
    simpa only [mul_comm] using
      (standardGaussian_integrable_faceDot v).bdd_mul
        (s.integrable_softFaceDirectional_factor A S x (A.mulVec u)).aestronglyMeasurable
        (s.softFaceDirectional_bdd_factor A S x (A.mulVec u))
  rw [integral_add (hP.const_mul _) hlast, integral_const_mul]


end FaceSmoother

end RectangleCLT
