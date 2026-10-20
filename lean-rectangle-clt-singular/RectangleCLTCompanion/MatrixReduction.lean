import RectangleCLT.LocalCovariance
import RectangleCLT.GaussianMoments

/-! The finite matrix reduction used in Appendix B of the companion paper.
The trace pairing is controlled directly from quadratic-form bounds. This
avoids introducing a nuclear norm and gives exactly the estimate consumed
by the restoration argument. Covariance contraction of Gaussian tilts is
an analytic input to these algebraic theorems. -/

open scoped BigOperators
open MeasureTheory

namespace RectangleCLT.Companion

noncomputable section

set_option autoImplicit false

theorem trace_mul_gram_eq_sum_quadratic {r s : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (X : Matrix (Fin r) (Fin s) ℝ) :
    Matrix.trace (B * (X * X.transpose)) =
      ∑ j, matrixQuadratic B (fun i => X i j) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, matrixQuadratic, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  exact Finset.sum_comm

theorem trace_gram_eq_sum_normSq {r s : ℕ} (X : Matrix (Fin r) (Fin s) ℝ) :
    Matrix.trace (X * X.transpose) = ∑ j, vectorNormSq (fun i => X i j) := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply,
    Matrix.transpose_apply, vectorNormSq, pow_two]
  exact Finset.sum_comm

/-- A quadratic operator bound controls its trace pairing with every
positive semidefinite matrix, without a factor depending on dimension. -/
theorem abs_trace_mul_le_of_posSemidef {r : ℕ}
    (B D : Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hB : ∀ v, |matrixQuadratic B v| ≤ b * vectorNormSq v)
    (hD : D.PosSemidef) :
    |Matrix.trace (B * D)| ≤ b * Matrix.trace D := by
  let X := hD.sqrt
  have hXt : X.transpose = X := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hD.posSemidef_sqrt.isHermitian
  have hXX : X * X.transpose = D := by rw [hXt]; exact hD.sqrt_mul_self
  rw [← hXX, trace_mul_gram_eq_sum_quadratic, trace_gram_eq_sum_normSq,
    Finset.mul_sum]
  exact (Finset.abs_sum_le_sum_abs _ _).trans
    (Finset.sum_le_sum (fun j _ => hB (fun i => X i j)))

def rankOne {r : ℕ} (v : Fin r → ℝ) : Matrix (Fin r) (Fin r) ℝ :=
  fun j k => v j * v k

@[simp] theorem trace_rankOne {r : ℕ} (v : Fin r → ℝ) :
    Matrix.trace (rankOne v) = vectorNormSq v := by
  simp only [Matrix.trace, Matrix.diag_apply, rankOne, vectorNormSq, pow_two]

@[simp] theorem trace_mul_rankOne {r : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (v : Fin r → ℝ) :
    Matrix.trace (B * rankOne v) = matrixQuadratic B v := by
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, rankOne, matrixQuadratic]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The matrix `E[(GGᵀ−I)w]` expressed using the weight mass, normalized
mean, and normalized covariance. Its identification with the actual
Gaussian integral is a separate moment identity. -/
def tiltScore {r : ℕ} (p : ℝ) (K : Matrix (Fin r) (Fin r) ℝ) (m : Fin r → ℝ) :
    Matrix (Fin r) (Fin r) ℝ := p • (K - 1 + rankOne m)

theorem trace_tiltScore {r : ℕ} (p : ℝ) (K : Matrix (Fin r) (Fin r) ℝ)
    (m : Fin r → ℝ) :
    Matrix.trace (tiltScore p K m) = p * (vectorNormSq m - Matrix.trace (1 - K)) := by
  simp only [tiltScore, Matrix.trace_smul, Matrix.trace_add, Matrix.trace_sub,
    trace_rankOne, smul_eq_mul]
  ring

/-- Direct trace-duality form of the companion's nuclear-norm reduction.
Covariance contraction is exactly positivity of `I−K`; the final right
side retains the signed score trace needed for surface cancellation. -/
theorem abs_trace_mul_tiltScore_le {r : ℕ}
    (B K : Matrix (Fin r) (Fin r) ℝ) (m : Fin r → ℝ) {p b : ℝ}
    (hp : 0 ≤ p) (hB : ∀ v, |matrixQuadratic B v| ≤ b * vectorNormSq v)
    (hK : (1 - K).PosSemidef) :
    |Matrix.trace (B * tiltScore p K m)| ≤
      b * (2 * p * vectorNormSq m - Matrix.trace (tiltScore p K m)) := by
  have heq : B * tiltScore p K m = p • (B * rankOne m - B * (1 - K)) := by
    simp only [tiltScore, Matrix.mul_smul, Matrix.mul_add, Matrix.mul_sub,
      Matrix.mul_one, smul_sub]
    module
  rw [heq, Matrix.trace_smul, Matrix.trace_sub, trace_mul_rankOne,
    smul_eq_mul, abs_mul, abs_of_nonneg hp]
  calc
    _ ≤ p * (|matrixQuadratic B m| + |Matrix.trace (B * (1 - K))|) :=
      mul_le_mul_of_nonneg_left (abs_sub _ _) hp
    _ ≤ p * (b * vectorNormSq m + b * Matrix.trace (1 - K)) :=
      mul_le_mul_of_nonneg_left (add_le_add (hB m)
        (abs_trace_mul_le_of_posSemidef B (1 - K) hB hK)) hp
    _ = _ := by rw [trace_tiltScore]; ring

/-- All selector weights can be summed before estimating the signed trace.
The matrices paired with them may differ, as in conditional restoration. -/
theorem abs_sum_trace_mul_tiltScore_le {r : ℕ} {ι : Type*} (S : Finset ι)
    (B K : ι → Matrix (Fin r) (Fin r) ℝ) (m : ι → Fin r → ℝ) (p : ι → ℝ) {b : ℝ}
    (hp : ∀ i ∈ S, 0 ≤ p i)
    (hB : ∀ i ∈ S, ∀ v, |matrixQuadratic (B i) v| ≤ b * vectorNormSq v)
    (hK : ∀ i ∈ S, (1 - K i).PosSemidef) :
    |∑ i ∈ S, Matrix.trace (B i * tiltScore (p i) (K i) (m i))| ≤
      b * (2 * (∑ i ∈ S, p i * vectorNormSq (m i)) -
        ∑ i ∈ S, Matrix.trace (tiltScore (p i) (K i) (m i))) := by
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ i ∈ S, b * (2 * p i * vectorNormSq (m i) -
        Matrix.trace (tiltScore (p i) (K i) (m i))) :=
      Finset.sum_le_sum (fun i hi => abs_trace_mul_tiltScore_le (B i) (K i) (m i)
        (hp i hi) (hB i hi) (hK i hi))
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_sub_distrib, mul_sub, mul_assoc]

section ActualMoments

variable {Ω : Type*} [MeasurableSpace Ω] {r : ℕ}

def weightMass (ν : Measure Ω) (w : Ω → ℝ) : ℝ := ∫ z, w z ∂ν

def weightMean (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ) (j : Fin r) : ℝ :=
  (∫ z, g z j * w z ∂ν) / weightMass ν w

/-- The normalized weighted covariance, expressed using its second raw
moment. `weightCovariance_eq_centered` identifies it with central moments. -/
def weightCovariance (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun j k => (∫ z, g z j * g z k * w z ∂ν) / weightMass ν w -
    weightMean ν g w j * weightMean ν g w k

/-- The actual weighted standard Gaussian score, or the same polynomial
score evaluated at an arbitrary measurable vector. -/
def weightedScore (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ) :
    Matrix (Fin r) (Fin r) ℝ :=
  fun j k => ∫ z, (g z j * g z k - if j = k then 1 else 0) * w z ∂ν

theorem weightCovariance_eq_centered
    (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ)
    (hw : Integrable w ν)
    (hg : ∀ j, Integrable (fun z => g z j * w z) ν)
    (hgg : ∀ j k, Integrable (fun z => g z j * g z k * w z) ν)
    (hp : weightMass ν w ≠ 0) (j k : Fin r) :
    weightCovariance ν g w j k =
      (∫ z, (g z j - weightMean ν g w j) * (g z k - weightMean ν g w k) * w z ∂ν) /
        weightMass ν w := by
  have hpoint (z : Ω) :
      (g z j - weightMean ν g w j) * (g z k - weightMean ν g w k) * w z =
      ((g z j * g z k * w z - weightMean ν g w j * (g z k * w z)) -
        weightMean ν g w k * (g z j * w z)) +
        (weightMean ν g w j * weightMean ν g w k) * w z := by ring
  have h₁ := ((hgg j k).sub ((hg k).const_mul (weightMean ν g w j))).sub
    ((hg j).const_mul (weightMean ν g w k))
  have h₂ := hw.const_mul (weightMean ν g w j * weightMean ν g w k)
  have hsum := integral_add h₁ h₂
  have hsub₁ := integral_sub ((hgg j k).sub ((hg k).const_mul (weightMean ν g w j)))
    ((hg j).const_mul (weightMean ν g w k))
  have hsub₂ := integral_sub (hgg j k) ((hg k).const_mul (weightMean ν g w j))
  simp only [Pi.sub_apply] at hsum hsub₁ hsub₂
  simp_rw [hpoint]
  rw [hsum, hsub₁, hsub₂]
  simp only [integral_const_mul, weightCovariance, weightMean, weightMass]
  field_simp [show (∫ z, w z ∂ν) ≠ 0 from hp]
  ring

/-- Identification with the actual integral is proved, rather than assumed
as a covariance property of a named tilt. -/
theorem weightedScore_eq_tiltScore
    (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ)
    (hw : Integrable w ν)
    (hgg : ∀ j k, Integrable (fun z => g z j * g z k * w z) ν)
    (hp : weightMass ν w ≠ 0) :
    weightedScore ν g w =
      tiltScore (weightMass ν w) (weightCovariance ν g w) (weightMean ν g w) := by
  classical
  ext j k
  have hpoint (z : Ω) : (g z j * g z k - if j = k then 1 else 0) * w z =
      g z j * g z k * w z - (if j = k then 1 else 0) * w z := by ring
  simp only [weightedScore, hpoint]
  rw [integral_sub (hgg j k) (hw.const_mul _), integral_const_mul]
  simp only [tiltScore, weightCovariance, Matrix.smul_apply, Matrix.add_apply,
    Matrix.sub_apply, Matrix.one_apply, rankOne, smul_eq_mul]
  change (∫ z, g z j * g z k * w z ∂ν) - (if j = k then 1 else 0) * weightMass ν w = _
  field_simp [hp]
  ring

/-- Actual weighted score pairing, ready for the selector weights. The only
remaining analytic hypothesis here is covariance contraction of the tilt. -/
theorem abs_trace_mul_weightedScore_le
    (ν : Measure Ω) (g : Ω → Fin r → ℝ) (w : Ω → ℝ)
    (B : Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hw : Integrable w ν)
    (hgg : ∀ j k, Integrable (fun z => g z j * g z k * w z) ν)
    (hp : 0 < weightMass ν w)
    (hB : ∀ v, |matrixQuadratic B v| ≤ b * vectorNormSq v)
    (hK : (1 - weightCovariance ν g w).PosSemidef) :
    |Matrix.trace (B * weightedScore ν g w)| ≤
      b * (2 * weightMass ν w * vectorNormSq (weightMean ν g w) -
        Matrix.trace (weightedScore ν g w)) := by
  rw [weightedScore_eq_tiltScore ν g w hw hgg hp.ne']
  exact abs_trace_mul_tiltScore_le B (weightCovariance ν g w) (weightMean ν g w)
    hp.le hB hK

end ActualMoments

theorem standardGaussian_integrable_bounded_weight {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) :
    Integrable w (standardGaussian r) := by
  have hh := (integrable_const 1 : Integrable (fun _ : Vector r => (1 : ℝ))
    (standardGaussian r)).bdd_mul hw.aestronglyMeasurable
      ⟨1, fun z => by simpa only [Real.norm_eq_abs] using hb z⟩
  simpa only [mul_one] using hh

theorem standardGaussian_integrable_weighted_coordinate {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) (j : Fin r) :
    Integrable (fun z => z j * w z) (standardGaussian r) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_coordinate r j).bdd_mul hw.aestronglyMeasurable
      ⟨1, fun z => by simpa only [Real.norm_eq_abs] using hb z⟩

theorem standardGaussian_integrable_weighted_product {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1) (j k : Fin r) :
    Integrable (fun z => z j * z k * w z) (standardGaussian r) := by
  simpa only [mul_comm] using
    (standardGaussian_integrable_coordinate_product r j k).bdd_mul hw.aestronglyMeasurable
      ⟨1, fun z => by simpa only [Real.norm_eq_abs] using hb z⟩

/-- The concrete product-Gaussian score reduction has no integrability
premises: they follow from the bounded measurable selector weight. Proving
the contraction hypothesis for log-concave selectors remains separate. -/
theorem standardGaussian_weightedScore_reduction {r : ℕ}
    (w : Vector r → ℝ) (hw : Measurable w) (hb : ∀ z, |w z| ≤ 1)
    (B : Matrix (Fin r) (Fin r) ℝ) {b : ℝ}
    (hp : 0 < weightMass (standardGaussian r) w)
    (hB : ∀ v, |matrixQuadratic B v| ≤ b * vectorNormSq v)
    (hK : (1 - weightCovariance (standardGaussian r) id w).PosSemidef) :
    |Matrix.trace (B * weightedScore (standardGaussian r) id w)| ≤
      b * (2 * weightMass (standardGaussian r) w *
        vectorNormSq (weightMean (standardGaussian r) id w) -
        Matrix.trace (weightedScore (standardGaussian r) id w)) := by
  exact abs_trace_mul_weightedScore_le (standardGaussian r) id w B
    (standardGaussian_integrable_bounded_weight w hw hb)
    (standardGaussian_integrable_weighted_product w hw hb) hp hB hK

end
end RectangleCLT.Companion
