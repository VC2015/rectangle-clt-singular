import RectangleCLTCompanion.SignedSurfaceBoundary
import RectangleCLT.GaussianSoftRecursion

/-! The actual signed Gaussian tangent identity for logistic soft faces.
No polyhedral boundary formula or Gaussian surface estimate is assumed. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators NNReal ENNReal

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

open FaceSmoother

variable {p : ℕ}

def softFacePower (s : FaceSmoother p) (a : ℕ) (f : Face p) (x : Vector p) : ℝ :=
  s.F x ^ a * s.softFaceWeight {f} x

def softFacePowerDirectional (s : FaceSmoother p) (a : ℕ) (f : Face p)
    (y x : Vector p) : ℝ :=
  softFacePower s a f x / s.bandwidth *
    (normalDot f y - ((a : ℝ) + 2) * (s.weights x).directionalMean y)

theorem continuous_softFacePower (s : FaceSmoother p) (a : ℕ) (f : Face p) :
    Continuous (softFacePower s a f) :=
  (s.continuous_F.pow a).mul (s.continuous_softFaceWeight {f})

theorem softFacePower_nonneg (s : FaceSmoother p) (a : ℕ) (f : Face p) (x : Vector p) :
    0 ≤ softFacePower s a f x :=
  mul_nonneg (pow_nonneg (s.F_pos x).le _) (s.softFaceWeight_nonneg _ _)

theorem softFacePower_le_one (s : FaceSmoother p) (a : ℕ) (f : Face p) (x : Vector p) :
    softFacePower s a f x ≤ 1 := by
  exact (mul_le_mul (pow_le_one₀ (s.F_pos x).le (s.F_le_one x))
    (s.softFaceWeight_le_one _ _) (s.softFaceWeight_nonneg _ _) zero_le_one).trans_eq (one_mul _)

theorem continuous_softFacePowerDirectional (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (y : Vector p) : Continuous (softFacePowerDirectional s a f y) := by
  apply ((continuous_softFacePower s a f).div_const _).mul
  apply continuous_const.sub
  apply continuous_const.mul
  simp only [FaceWeights.directionalMean_eq]
  exact continuous_finset_sum _ (fun j _ => (s.continuous_v j).mul continuous_const)

theorem abs_softFacePowerDirectional_le (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (y x : Vector p) :
    |softFacePowerDirectional s a f y x| ≤
      (|normalDot f y| + ((a : ℝ) + 2) * ‖y‖) / s.bandwidth := by
  have ha : 0 ≤ (a : ℝ) + 2 := by positivity
  have hbracket : |normalDot f y - ((a : ℝ) + 2) * (s.weights x).directionalMean y| ≤
      |normalDot f y| + ((a : ℝ) + 2) * ‖y‖ := by
    refine (abs_sub _ _).trans (add_le_add_left ?_ _)
    rw [abs_mul, abs_of_nonneg ha]
    exact mul_le_mul_of_nonneg_left ((s.weights x).abs_directionalMean_le_norm y) ha
  rw [softFacePowerDirectional, abs_mul, abs_div,
    abs_of_nonneg (softFacePower_nonneg _ _ _ _), abs_of_pos s.bandwidth_pos]
  exact (mul_le_mul (div_le_div_of_nonneg_right (softFacePower_le_one _ _ _ _)
    s.bandwidth_pos.le) hbracket (abs_nonneg _)
    (div_nonneg zero_le_one s.bandwidth_pos.le)).trans_eq (by ring)

theorem hasDerivAt_softFacePower_line (s : FaceSmoother p) (a : ℕ) (f : Face p)
    (x y : Vector p) (t : ℝ) :
    HasDerivAt (fun b => softFacePower s a f (line x y b))
      (softFacePowerDirectional s a f y (line x y t)) t := by
  induction a with
  | zero =>
    have htwo : (1 : ℝ) + 1 = 2 := by norm_num
    simpa only [softFacePowerDirectional, softFacePower, pow_zero, one_mul,
      Nat.cast_zero, zero_add, Finset.card_singleton, Nat.cast_one, Finset.sum_singleton,
      htwo] using s.hasDerivAt_softFaceWeight_line {f} x y t
  | succ a ih =>
    have hh := ih.mul (s.hasDerivAt_F_line x y t)
    convert hh using 1
    · funext b
      simp only [softFacePower, pow_succ]
      ring
    · simp only [softFacePowerDirectional, softFacePower, pow_succ, Nat.cast_add, Nat.cast_one]
      ring

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

theorem hasDerivAt_softFacePower_gaussian_slice (s : FaceSmoother p) (a : ℕ)
    (f : Face p) (A : Matrix (Fin p) (Fin p) ℝ) (x z : Vector p) (j : Fin p) :
    HasDerivAt (fun t => softFacePower s a f (A.mulVec (Function.update z j t) + x))
      (softFacePowerDirectional s a f (fun k => A k j) (A.mulVec z + x)) (z j) := by
  have hd0 : HasDerivAt
      (fun b => softFacePower s a f (line (A.mulVec z + x) (fun k => A k j) b))
      (softFacePowerDirectional s a f (fun k => A k j) (A.mulVec z + x)) (z j - z j) := by
    simpa only [sub_self, line_zero] using
      hasDerivAt_softFacePower_line s a f (A.mulVec z + x) (fun k => A k j) 0
  simpa only [Function.comp_apply, sub_self, line_zero, mul_one, gaussianFactor_update] using
    hd0.comp (h := fun t : ℝ => t - z j) (z j) ((hasDerivAt_id (z j)).sub_const (z j))

theorem softFacePowerDirectional_mulVec (s : FaceSmoother p) (a : ℕ) (f : Face p)
    (A : Matrix (Fin p) (Fin p) ℝ) (u x : Vector p) :
    softFacePowerDirectional s a f (A.mulVec u) x =
      ∑ j, u j * softFacePowerDirectional s a f (fun k => A k j) x := by
  have hn : normalDot f (A.mulVec u) = ∑ j, u j * normalDot f (fun k => A k j) := by
    cases hf : f.2 <;>
      simp only [normalDot, hf, Bool.false_eq_true, ↓reduceIte, Matrix.mulVec,
        dotProduct, Finset.sum_neg_distrib]
    · rw [← Finset.sum_neg_distrib]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      ring
  have hm : (s.weights x).directionalMean (A.mulVec u) =
      ∑ j, u j * (s.weights x).directionalMean (fun k => A k j) := by
    simp only [FaceWeights.directionalMean_eq, Matrix.mulVec, dotProduct, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    ring
  unfold softFacePowerDirectional
  rw [hn, hm, Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem faceDot_sub_smul (u v z : Vector p) (t : ℝ) :
    faceDot u (z - t • v) = faceDot u z - t * faceDot u v := by
  simp only [faceDot, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mul_sub,
    Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem normalDot_scaledFactor (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ)
    (f : Face p) (z : Vector p) :
    normalDot f ((σ • A).mulVec z) = σ * faceDot (signedRowNormal A f) z := by
  rw [Matrix.smul_mulVec_assoc]
  rw [faceDot_signedRowNormal_eq]
  cases hf : f.2 <;> simp [normalDot, hf]

/-- The actual tangent derivative of `F^(a+1) π_f`, with the normal term
cancelled before taking any absolute value. -/
theorem softFacePower_tangent_derivative (s : FaceSmoother p) (a : ℕ) (f : Face p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (x z : Vector p)
    (hu : vectorNormSq (signedRowNormal A f) = 1) :
    (∑ j, (z j - faceDot (signedRowNormal A f) z * signedRowNormal A f j) *
      softFacePowerDirectional s a f (fun k => (σ • A) k j) ((σ • A).mulVec z + x)) =
      -(((a : ℝ) + 2) * σ / s.bandwidth) *
        ∑ k, softFacePower s a f ((σ • A).mulVec z + x) *
          (s.weights ((σ • A).mulVec z + x)).pi k *
            (faceDot (signedRowNormal A k) z -
              faceDot (signedRowNormal A k) (signedRowNormal A f) *
                faceDot (signedRowNormal A f) z) := by
  let u := signedRowNormal A f
  let y := (σ • A).mulVec z + x
  let R := z - faceDot u z • u
  have huu : faceDot u u = 1 := by simpa only [faceDot, vectorNormSq, sq] using hu
  have hn : normalDot f ((σ • A).mulVec R) = 0 := by
    rw [normalDot_scaledFactor, faceDot_sub_smul, huu]
    ring
  have hm : (s.weights y).directionalMean ((σ • A).mulVec R) =
      σ * ∑ k, (s.weights y).pi k *
        (faceDot (signedRowNormal A k) z - faceDot (signedRowNormal A k) u * faceDot u z) := by
    unfold FaceWeights.directionalMean
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    change (s.weights y).pi k * normalDot k ((σ • A).mulVec R) = _
    rw [normalDot_scaledFactor, faceDot_sub_smul]
    ring
  change (∑ j, R j * softFacePowerDirectional s a f (fun k => (σ • A) k j) y) = _
  rw [← softFacePowerDirectional_mulVec, softFacePowerDirectional, hn, hm]
  have hfac : (∑ k, softFacePower s a f y * (s.weights y).pi k *
      (faceDot (signedRowNormal A k) z - faceDot (signedRowNormal A k) u * faceDot u z)) =
      softFacePower s a f y * ∑ k, (s.weights y).pi k *
      (faceDot (signedRowNormal A k) z - faceDot (signedRowNormal A k) u * faceDot u z) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change _ = -(((a : ℝ) + 2) * σ / s.bandwidth) *
    ∑ k, softFacePower s a f y * (s.weights y).pi k *
      (faceDot (signedRowNormal A k) z - faceDot (signedRowNormal A k) u * faceDot u z)
  rw [hfac]
  ring

/-- The signed Gaussian identity for the actual logistic face kernel,
including arbitrary shifts, Gaussian scales and singular matrix factors.
`softFacePower a f` is exactly `F^(a+1) * π_f`. -/
theorem softFacePower_gaussian_tangent_identity (s : FaceSmoother p) (a : ℕ) (f : Face p)
    (A : Matrix (Fin p) (Fin p) ℝ) (σ : ℝ) (x : Vector p)
    (hu : vectorNormSq (signedRowNormal A f) = 1) :
    (∫ z, (vectorNormSq z - (p : ℝ)) * softFacePower s a f ((σ • A).mulVec z + x)
      ∂standardGaussian p) =
      (∫ z, (faceDot (signedRowNormal A f) z ^ 2 - 1) *
        softFacePower s a f ((σ • A).mulVec z + x) ∂standardGaussian p) -
      (((a : ℝ) + 2) * σ / s.bandwidth) * ∑ k,
        (∫ z, softFacePower s a f ((σ • A).mulVec z + x) *
          (s.weights ((σ • A).mulVec z + x)).pi k *
            (faceDot (signedRowNormal A k) z -
              faceDot (signedRowNormal A k) (signedRowNormal A f) *
                faceDot (signedRowNormal A f) z) ∂standardGaussian p) := by
  let B := σ • A
  let g := fun z => softFacePower s a f (B.mulVec z + x)
  let D := fun j z => softFacePowerDirectional s a f (fun k => B k j) (B.mulVec z + x)
  have hin : Continuous (fun z : Vector p => B.mulVec z + x) := by fun_prop
  have hg : Continuous g := (continuous_softFacePower s a f).comp hin
  have hD (j : Fin p) : Continuous (D j) :=
    (continuous_softFacePowerDirectional s a f (fun k => B k j)).comp hin
  have hderiv (j : Fin p) (z : Vector p) :
      HasDerivAt (fun t => g (Function.update z j t)) (D j z) (z j) :=
    hasDerivAt_softFacePower_gaussian_slice s a f B x z j
  have hgb : ∃ M, ∀ z, ‖g z‖ ≤ M := by
    refine ⟨1, fun z => ?_⟩
    rw [Real.norm_eq_abs, abs_of_nonneg (softFacePower_nonneg _ _ _ _)]
    exact softFacePower_le_one _ _ _ _
  have hDb (j : Fin p) : ∃ M, ∀ z, ‖D j z‖ ≤ M := by
    refine ⟨(|normalDot f (fun k => B k j)| + ((a : ℝ) + 2) *
      ‖(fun k => B k j)‖) / s.bandwidth, fun z => ?_⟩
    simpa only [Real.norm_eq_abs] using
      abs_softFacePowerDirectional_le s a f (fun k => B k j) (B.mulVec z + x)
  have hpi (k : Face p) (z : Vector p) : (s.weights (B.mulVec z + x)).pi k ≤ 1 :=
    ((s.weights _).pi_le_theta k).trans (s.weights _).theta_lt_one.le
  have hi (k : Face p) : Integrable (fun z => g z * (s.weights (B.mulVec z + x)).pi k *
      (faceDot (signedRowNormal A k) z -
        faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) z))
      (standardGaussian p) := by
    have hgk : Continuous (fun z => g z * (s.weights (B.mulVec z + x)).pi k) :=
      hg.mul ((s.continuous_pi k).comp hin)
    have hbound : ∃ M, ∀ z, ‖g z * (s.weights (B.mulVec z + x)).pi k‖ ≤ M := by
      refine ⟨1, fun z => ?_⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (softFacePower_nonneg _ _ _ _)
        ((s.weights _).pi_nonneg k))]
      exact (mul_le_mul (softFacePower_le_one _ _ _ _) (hpi k z)
        ((s.weights _).pi_nonneg k) zero_le_one).trans_eq (one_mul _)
    have hlinear : Integrable (fun z => faceDot (signedRowNormal A k) z -
        faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) z)
        (standardGaussian p) :=
      (standardGaussian_integrable_faceDot _).sub ((standardGaussian_integrable_faceDot _).const_mul _)
    simpa only [mul_comm] using integrable_gaussian_bounded_mul hgk hbound hlinear
  have htangent :
      (∫ z, ∑ j, (z j - faceDot (signedRowNormal A f) z * signedRowNormal A f j) *
        D j z ∂standardGaussian p) =
      -(((a : ℝ) + 2) * σ / s.bandwidth) * ∑ k,
        (∫ z, g z * (s.weights (B.mulVec z + x)).pi k *
          (faceDot (signedRowNormal A k) z -
            faceDot (signedRowNormal A k) (signedRowNormal A f) *
              faceDot (signedRowNormal A f) z) ∂standardGaussian p) := by
    change (∫ z, ∑ j, (z j - faceDot (signedRowNormal A f) z * signedRowNormal A f j) *
      softFacePowerDirectional s a f (fun k => (σ • A) k j) ((σ • A).mulVec z + x)
        ∂standardGaussian p) = _
    simp_rw [softFacePower_tangent_derivative s a f A σ x _ hu]
    rw [integral_const_mul, integral_finset_sum Finset.univ (fun k _ => hi k)]
  have hh := gaussian_tangent_score_stein hg hD hderiv hgb hDb (signedRowNormal A f) hu
  rw [htangent] at hh
  simpa only [B, g, sub_eq_add_neg, neg_mul] using hh

theorem signedRowNormal_unit_normSq (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (f : Face p) :
    vectorNormSq (signedRowNormal A f) = 1 := by
  have hh := signedRowNormal_gram A f f
  rw [hdiag] at hh
  have hss := faceSign_sq f
  have hd : faceDot (signedRowNormal A f) (signedRowNormal A f) =
      vectorNormSq (signedRowNormal A f) := by simp only [faceDot, vectorNormSq, sq]
  rw [hd] at hh
  nlinarith

/-- The positive two-face kernel is symmetric, including coincident and
opposite coordinate faces. -/
theorem softFacePower_pair_kernel_symm (s : FaceSmoother p) (a : ℕ)
    (f k : Face p) (y : Vector p) :
    softFacePower s a f y * (s.weights y).pi k =
      softFacePower s a k y * (s.weights y).pi f := by
  simp only [softFacePower, FaceSmoother.softFaceWeight, Finset.prod_singleton]
  ring

/-- Pairing the two actual tangent boundary terms before taking absolute
values produces the factor `1−ρ`. Both angular degeneracies are included. -/
theorem softFacePower_ridge_pairing (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (f k : Face p) (y z : Vector p) :
    softFacePower s a f y * (s.weights y).pi k *
        (faceDot (signedRowNormal A k) z -
          faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) z) +
      softFacePower s a k y * (s.weights y).pi f *
        (faceDot (signedRowNormal A f) z -
          faceDot (signedRowNormal A f) (signedRowNormal A k) * faceDot (signedRowNormal A k) z) =
      softFacePower s a f y * (s.weights y).pi k *
        (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
          (faceDot (signedRowNormal A f) z + faceDot (signedRowNormal A k) z) := by
  rw [softFacePower_pair_kernel_symm s a k f y,
    faceDot_comm (signedRowNormal A k) (signedRowNormal A f)]
  ring

/-- Exact finite pairing of the entire ridge contribution. There is no
triangle inequality between the two ordered ridge terms. -/
theorem softFacePower_sum_ridge_pairing (s : FaceSmoother p) (a : ℕ)
    (A : Matrix (Fin p) (Fin p) ℝ) (y z : Vector p) :
    2 * (∑ f : Face p, ∑ k : Face p,
      softFacePower s a f y * (s.weights y).pi k *
        (faceDot (signedRowNormal A k) z -
          faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) z)) =
      ∑ f : Face p, ∑ k : Face p,
        softFacePower s a f y * (s.weights y).pi k *
          (1 - faceDot (signedRowNormal A f) (signedRowNormal A k)) *
            (faceDot (signedRowNormal A f) z + faceDot (signedRowNormal A k) z) := by
  let Q := fun f k : Face p => softFacePower s a f y * (s.weights y).pi k *
    (faceDot (signedRowNormal A k) z -
      faceDot (signedRowNormal A k) (signedRowNormal A f) * faceDot (signedRowNormal A f) z)
  have hswap : (∑ f : Face p, ∑ k : Face p, Q f k) =
      ∑ f : Face p, ∑ k : Face p, Q k f := Finset.sum_comm
  calc
    _ = (∑ f : Face p, ∑ k : Face p, Q f k) +
        ∑ f : Face p, ∑ k : Face p, Q k f := by rw [← hswap]; ring
    _ = ∑ f : Face p, ∑ k : Face p, (Q f k + Q k f) := by
      simp only [Finset.sum_add_distrib]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro f _
      apply Finset.sum_congr rfl
      intro k _
      exact softFacePower_ridge_pairing s a A f k y z

/-- Summing all actual soft singleton powers gives the scalar clock kernel.
Absent faces contribute zero through their existing normalized weights. -/
theorem sum_softFacePower (s : FaceSmoother p) (a : ℕ) (x : Vector p) :
    (∑ f : Face p, softFacePower s a f x) =
      s.F x ^ (a + 1) * (s.weights x).theta := by
  simp only [softFacePower, FaceSmoother.softFaceWeight, Finset.prod_singleton]
  rw [← Finset.mul_sum, ← Finset.mul_sum, FaceWeights.sum_pi]
  change s.F x ^ a * (s.F x * (s.weights x).theta) = _
  rw [pow_succ]
  ring

end
end RectangleCLT.Companion.SignedSurface
