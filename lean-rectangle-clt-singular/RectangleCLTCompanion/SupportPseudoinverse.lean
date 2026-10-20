import RectangleCLTCompanion.SupportCoordinates
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-! A spectral pseudoinverse produces an ambient covariance-support
projection without a lower bound on any positive eigenvalue. This construction
uses reciprocal eigenvalues only algebraically, never a uniform inverse norm. -/

open scoped BigOperators Matrix ComplexOrder

namespace RectangleCLT.Companion

noncomputable section

private def spectralMatrix {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) (f : ℝ → ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  let U : Matrix (Fin q) (Fin q) ℝ := hQ.eigenvectorUnitary
  U * Matrix.diagonal (fun j => f (hQ.eigenvalues j)) * star U

private theorem spectralMatrix_mul {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) (f g : ℝ → ℝ) :
    spectralMatrix hQ f * spectralMatrix hQ g = spectralMatrix hQ (fun t => f t * g t) := by
  let U : Matrix (Fin q) (Fin q) ℝ := hQ.eigenvectorUnitary
  have hUU : star U * U = 1 := unitary.coe_star_mul_self hQ.eigenvectorUnitary
  change (U * Matrix.diagonal (fun j => f (hQ.eigenvalues j)) * star U) *
      (U * Matrix.diagonal (fun j => g (hQ.eigenvalues j)) * star U) = _
  calc
    _ = U * (Matrix.diagonal (fun j => f (hQ.eigenvalues j)) * (star U * U) *
        Matrix.diagonal (fun j => g (hQ.eigenvalues j))) * star U := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [hUU, Matrix.mul_one, Matrix.diagonal_mul_diagonal]; rfl

private theorem spectralMatrix_transpose {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) (f : ℝ → ℝ) :
    (spectralMatrix hQ f).transpose = spectralMatrix hQ f := by
  simp only [spectralMatrix, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_mul,
    Matrix.transpose_transpose, Matrix.diagonal_transpose, Matrix.mul_assoc]

private theorem spectralMatrix_id {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : spectralMatrix hQ id = Q := by
  simpa only [spectralMatrix, id_eq, RCLike.ofReal_real_eq_id, Function.comp_id] using
    hQ.spectral_theorem.symm

private theorem spectralMatrix_one {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : spectralMatrix hQ (fun _ => 1) = 1 := by
  simp [spectralMatrix]

private theorem spectralMatrix_sub {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) (f g : ℝ → ℝ) :
    spectralMatrix hQ (fun t => f t - g t) = spectralMatrix hQ f - spectralMatrix hQ g := by
  simp only [spectralMatrix, ← Matrix.diagonal_sub, Matrix.mul_sub, Matrix.sub_mul]

private theorem spectralMatrix_posSemidef {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) (f : ℝ → ℝ) (hf : ∀ t, 0 ≤ f t) :
    (spectralMatrix hQ f).PosSemidef := by
  have hd : (Matrix.diagonal (fun j => f (hQ.eigenvalues j))).PosSemidef :=
    Matrix.posSemidef_diagonal_iff.mpr (fun j => hf _)
  simpa only [spectralMatrix, Matrix.star_eq_conjTranspose] using
    hd.mul_mul_conjTranspose_same (hQ.eigenvectorUnitary : Matrix (Fin q) (Fin q) ℝ)

def spectralSupportIndicator (t : ℝ) : ℝ := if t = 0 then 0 else 1

/-- The reciprocal spectral transform is zero on the null eigenspaces. -/
def supportPseudoInverse {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : Matrix (Fin q) (Fin q) ℝ := spectralMatrix hQ (fun t => t⁻¹)

/-- Orthogonal support projection, represented in the original coordinates. -/
def supportProjection {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : Matrix (Fin q) (Fin q) ℝ := spectralMatrix hQ spectralSupportIndicator

theorem supportPseudoInverse_transpose {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : (supportPseudoInverse hQ).transpose = supportPseudoInverse hQ :=
  spectralMatrix_transpose hQ _

theorem supportProjection_transpose {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : (supportProjection hQ).transpose = supportProjection hQ :=
  spectralMatrix_transpose hQ _

theorem supportPseudoInverse_mul_self {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : supportPseudoInverse hQ * Q = supportProjection hQ := by
  have hh := spectralMatrix_mul hQ (fun t => t⁻¹) id
  have hf : (fun t : ℝ => t⁻¹ * id t) = spectralSupportIndicator := by
    funext t
    by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]
  rw [hf] at hh
  simpa only [spectralMatrix_id] using hh

theorem self_mul_supportPseudoInverse {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : Q * supportPseudoInverse hQ = supportProjection hQ := by
  have hh := spectralMatrix_mul hQ id (fun t => t⁻¹)
  have hf : (fun t : ℝ => id t * t⁻¹) = spectralSupportIndicator := by
    funext t
    by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]
  rw [hf] at hh
  simpa only [spectralMatrix_id] using hh

theorem supportProjection_idempotent {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : supportProjection hQ * supportProjection hQ = supportProjection hQ := by
  have hh := spectralMatrix_mul hQ spectralSupportIndicator spectralSupportIndicator
  have hf : (fun t => spectralSupportIndicator t * spectralSupportIndicator t) =
      spectralSupportIndicator := by
    funext t
    by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]
  rw [hf] at hh
  exact hh

theorem self_mul_supportProjection {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : Q * supportProjection hQ = Q := by
  have hh := spectralMatrix_mul hQ id spectralSupportIndicator
  have hf : (fun t : ℝ => id t * spectralSupportIndicator t) = id := by
    funext t
    by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]
  rw [hf] at hh
  simpa only [spectralMatrix_id] using hh

theorem supportProjection_posSemidef {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : (supportProjection hQ).PosSemidef := by
  apply spectralMatrix_posSemidef hQ
  intro t
  by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]

/-- The covariance budget is bounded by identity without any spectral loss. -/
theorem one_sub_supportProjection_posSemidef {q : ℕ} {Q : Matrix (Fin q) (Fin q) ℝ}
    (hQ : Q.IsHermitian) : (1 - supportProjection hQ).PosSemidef := by
  rw [← spectralMatrix_one hQ, supportProjection, ← spectralMatrix_sub]
  apply spectralMatrix_posSemidef hQ
  intro t
  by_cases ht : t = 0 <;> simp [spectralSupportIndicator, ht]

/-- Domain Gram matrix of an arbitrary rectangular covariance factor. -/
def factorGram {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  A.transpose * A

theorem factorGram_isHermitian {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    (factorGram A).IsHermitian := by
  simpa only [factorGram, Matrix.conjTranspose_eq_transpose_of_trivial] using
    Matrix.isHermitian_transpose_mul_self A

/-- Ambient pseudowhitening on the domain of a possibly singular factor. -/
def ambientWhitening {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin q) (Fin p) ℝ := supportPseudoInverse (factorGram_isHermitian A) * A.transpose

def ambientSupportProjection {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    Matrix (Fin q) (Fin q) ℝ := supportProjection (factorGram_isHermitian A)

theorem ambientWhitening_mul_factor {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    ambientWhitening A * A = ambientSupportProjection A := by
  unfold ambientWhitening ambientSupportProjection
  rw [Matrix.mul_assoc]
  exact supportPseudoInverse_mul_self (factorGram_isHermitian A)

theorem ambientSupportProjection_transpose {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    (ambientSupportProjection A).transpose = ambientSupportProjection A :=
  supportProjection_transpose _

theorem ambientSupportProjection_idempotent {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    ambientSupportProjection A * ambientSupportProjection A = ambientSupportProjection A :=
  supportProjection_idempotent _

theorem ambientSupportProjection_posSemidef {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    (ambientSupportProjection A).PosSemidef := supportProjection_posSemidef _

theorem one_sub_ambientSupportProjection_posSemidef {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) :
    (1 - ambientSupportProjection A).PosSemidef := one_sub_supportProjection_posSemidef _

/-- Projection does not change any observable direction of the factor. -/
theorem factor_mul_ambientSupportProjection {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    A * ambientSupportProjection A = A := by
  have hzero : A.transpose * A * (ambientSupportProjection A - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one]
    exact sub_eq_zero.mpr (self_mul_supportProjection (factorGram_isHermitian A))
  have hz : A * (ambientSupportProjection A - 1) = 0 :=
    (Matrix.conjTranspose_mul_self_mul_eq_zero A _).mp (by
      simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using hzero)
  rw [Matrix.mul_sub, Matrix.mul_one] at hz
  exact sub_eq_zero.mp hz

/-- The pseudowhitening map is a right inverse at every point of the actual
factor range. It need not invert anything outside that range. -/
theorem factor_ambientWhitening_on_range {p q : ℕ}
    (A : Matrix (Fin p) (Fin q) ℝ) (x : Vector p)
    (hx : x ∈ LinearMap.range A.mulVecLin) : A.mulVec ((ambientWhitening A).mulVec x) = x := by
  obtain ⟨y, rfl⟩ := LinearMap.mem_range.mp hx
  change A.mulVec ((ambientWhitening A).mulVec (A.mulVec y)) = A.mulVec y
  have hy : (ambientWhitening A).mulVec (A.mulVec y) = (ambientSupportProjection A).mulVec y := by
    rw [Matrix.mulVec_mulVec, ambientWhitening_mul_factor]
  rw [hy, Matrix.mulVec_mulVec, factor_mul_ambientSupportProjection]

/-- Exact transformed covariance: the ambient whitened total covariance is
an orthogonal support projection, and hence is at most the identity. -/
theorem ambientWhitening_covariance {p q : ℕ} (A : Matrix (Fin p) (Fin q) ℝ) :
    ambientWhitening A * (A * A.transpose) * (ambientWhitening A).transpose =
      ambientSupportProjection A := by
  calc
    _ = (ambientWhitening A * A) * (ambientWhitening A * A).transpose := by
      simp only [Matrix.transpose_mul, Matrix.mul_assoc]
    _ = ambientSupportProjection A * (ambientSupportProjection A).transpose := by
      rw [ambientWhitening_mul_factor]
    _ = _ := by rw [ambientSupportProjection_transpose, ambientSupportProjection_idempotent]

end
end RectangleCLT.Companion
