import RectangleCLTCompanion.MatrixReduction
import Mathlib.LinearAlgebra.Matrix.Spectrum
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Analysis.Matrix

/-! A continuous trace-dual presentation of the genuine nuclear norm on real
symmetric matrices. The spectral theorem below identifies it with the sum
of the absolute eigenvalues. The entry bound in the dual set supplies a
simple uniform Lipschitz majorant; spectral sign matrices attain the norm.
-/

open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4

noncomputable section

variable {r : ℕ}

local instance : NormedAddCommGroup (Matrix (Fin r) (Fin r) ℝ) := Matrix.normedAddCommGroup

def symmetricTraceUnitBall (B : Matrix (Fin r) (Fin r) ℝ) : Prop :=
  B.IsSymm ∧ (∀ z, |matrixQuadratic B z| ≤ vectorNormSq z) ∧
    ∀ j k, |B j k| ≤ 1

def symmetricNuclearNorm (M : Matrix (Fin r) (Fin r) ℝ) : ℝ :=
  sSup {t | ∃ B, symmetricTraceUnitBall B ∧ t = Matrix.trace (B * M)}

theorem zero_mem_symmetricTraceUnitBall :
    symmetricTraceUnitBall (0 : Matrix (Fin r) (Fin r) ℝ) := by
  refine ⟨by simp, ?_, by simp⟩
  intro z
  simp only [matrixQuadratic, Matrix.zero_apply, mul_zero, zero_mul, Finset.sum_const_zero,
    abs_zero]
  exact Finset.sum_nonneg (fun j _ => sq_nonneg _)

theorem symmetricTraceUnitBall_neg {B : Matrix (Fin r) (Fin r) ℝ}
    (hB : symmetricTraceUnitBall B) : symmetricTraceUnitBall (-B) := by
  refine ⟨hB.1.neg, ?_, fun j k => by simpa only [Matrix.neg_apply, abs_neg] using hB.2.2 j k⟩
  intro z
  simpa only [matrixQuadratic, Matrix.neg_apply, mul_neg, neg_mul,
    Finset.sum_neg_distrib, abs_neg] using hB.2.1 z

theorem abs_trace_mul_le_entrySum {B M : Matrix (Fin r) (Fin r) ℝ}
    (hB : ∀ j k, |B j k| ≤ 1) :
    |Matrix.trace (B * M)| ≤ ∑ j, ∑ k, |M k j| := by
  unfold Matrix.trace Matrix.diag
  simp only [Matrix.mul_apply]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  apply Finset.sum_le_sum
  intro j _
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  exact Finset.sum_le_sum (fun k _ => by
    rw [abs_mul]
    exact (mul_le_mul_of_nonneg_right (hB j k) (abs_nonneg _)).trans_eq (one_mul _))

theorem symmetricTrace_values_nonempty (M : Matrix (Fin r) (Fin r) ℝ) :
    {t | ∃ B, symmetricTraceUnitBall B ∧ t = Matrix.trace (B * M)}.Nonempty :=
  ⟨0, 0, zero_mem_symmetricTraceUnitBall, by simp⟩

theorem symmetricTrace_values_bddAbove (M : Matrix (Fin r) (Fin r) ℝ) :
    BddAbove {t | ∃ B, symmetricTraceUnitBall B ∧ t = Matrix.trace (B * M)} := by
  refine ⟨∑ j, ∑ k, |M k j|, ?_⟩
  rintro t ⟨B, hB, rfl⟩
  exact (le_abs_self _).trans (abs_trace_mul_le_entrySum hB.2.2)

theorem trace_le_symmetricNuclearNorm (M B : Matrix (Fin r) (Fin r) ℝ)
    (hB : symmetricTraceUnitBall B) : Matrix.trace (B * M) ≤ symmetricNuclearNorm M :=
  le_csSup (symmetricTrace_values_bddAbove M) ⟨B, hB, rfl⟩

theorem symmetricNuclearNorm_nonneg (M : Matrix (Fin r) (Fin r) ℝ) :
    0 ≤ symmetricNuclearNorm M := by
  simpa only [Matrix.zero_mul, Matrix.trace_zero] using
    trace_le_symmetricNuclearNorm M 0 zero_mem_symmetricTraceUnitBall

theorem symmetricNuclearNorm_le_entrySum (M : Matrix (Fin r) (Fin r) ℝ) :
    symmetricNuclearNorm M ≤ ∑ j, ∑ k, |M k j| := by
  apply csSup_le (symmetricTrace_values_nonempty M)
  rintro t ⟨B, hB, rfl⟩
  exact (le_abs_self _).trans (abs_trace_mul_le_entrySum hB.2.2)

theorem symmetricNuclearNorm_zero : symmetricNuclearNorm (0 : Matrix (Fin r) (Fin r) ℝ) = 0 := by
  apply le_antisymm
  · simpa only [Matrix.zero_apply, abs_zero, Finset.sum_const_zero] using
      symmetricNuclearNorm_le_entrySum (0 : Matrix (Fin r) (Fin r) ℝ)
  · exact symmetricNuclearNorm_nonneg _

theorem symmetricNuclearNorm_neg (M : Matrix (Fin r) (Fin r) ℝ) :
    symmetricNuclearNorm (-M) = symmetricNuclearNorm M := by
  have hle (N : Matrix (Fin r) (Fin r) ℝ) : symmetricNuclearNorm (-N) ≤ symmetricNuclearNorm N := by
    apply csSup_le (symmetricTrace_values_nonempty (-N))
    rintro t ⟨B, hB, rfl⟩
    simpa only [Matrix.mul_neg, Matrix.neg_mul] using
      trace_le_symmetricNuclearNorm N (-B) (symmetricTraceUnitBall_neg hB)
  exact le_antisymm (hle M) (by simpa only [neg_neg] using hle (-M))

theorem symmetricNuclearNorm_add_le (M N : Matrix (Fin r) (Fin r) ℝ) :
    symmetricNuclearNorm (M + N) ≤ symmetricNuclearNorm M + symmetricNuclearNorm N := by
  apply csSup_le (symmetricTrace_values_nonempty (M + N))
  rintro t ⟨B, hB, rfl⟩
  rw [Matrix.mul_add, Matrix.trace_add]
  exact add_le_add (trace_le_symmetricNuclearNorm M B hB) (trace_le_symmetricNuclearNorm N B hB)

theorem symmetricNuclearNorm_abs_sub_le (M N : Matrix (Fin r) (Fin r) ℝ) :
    |symmetricNuclearNorm M - symmetricNuclearNorm N| ≤ symmetricNuclearNorm (M - N) := by
  have h₁ := symmetricNuclearNorm_add_le (M - N) N
  have h₂ := symmetricNuclearNorm_add_le (N - M) M
  rw [sub_add_cancel] at h₁ h₂
  rw [show N - M = -(M - N) by abel, symmetricNuclearNorm_neg] at h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem symmetricNuclearNorm_le_dimension_mul_norm (M : Matrix (Fin r) (Fin r) ℝ) :
    symmetricNuclearNorm M ≤ (r : ℝ) ^ 2 * ‖M‖ := by
  apply (symmetricNuclearNorm_le_entrySum M).trans
  calc
    _ ≤ ∑ _j : Fin r, ∑ _k : Fin r, ‖M‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact Finset.sum_le_sum (fun k _ => by
        simpa only [Real.norm_eq_abs] using (norm_le_pi_norm (M k) j).trans (norm_le_pi_norm M k))
    _ = _ := by simp; ring

theorem lipschitzWith_symmetricNuclearNorm :
    LipschitzWith ⟨(r : ℝ) ^ 2, sq_nonneg _⟩
      (symmetricNuclearNorm : Matrix (Fin r) (Fin r) ℝ → ℝ) := by
  apply LipschitzWith.of_dist_le_mul
  intro M N
  rw [Real.dist_eq, dist_eq_norm]
  exact (symmetricNuclearNorm_abs_sub_le M N).trans (symmetricNuclearNorm_le_dimension_mul_norm _)

theorem continuous_symmetricNuclearNorm :
    Continuous (symmetricNuclearNorm : Matrix (Fin r) (Fin r) ℝ → ℝ) :=
  lipschitzWith_symmetricNuclearNorm.continuous

theorem matrixQuadratic_eq_dotProduct_mulVec (M : Matrix (Fin r) (Fin r) ℝ) (z : Vector r) :
    matrixQuadratic M z = dotProduct z (M.mulVec z) := by
  simp only [matrixQuadratic, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem orthogonal_row_sq_sum (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Q * Q.transpose = 1) (j : Fin r) : ∑ i, (Q j i) ^ 2 = 1 := by
  have hh := congrArg (fun M : Matrix (Fin r) (Fin r) ℝ => M j j) hQ
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq, pow_two] using hh

theorem orthogonal_transpose_mulVec_normSq (Q : Matrix (Fin r) (Fin r) ℝ)
    (hQ : Q * Q.transpose = 1) (z : Vector r) :
    vectorNormSq (Q.transpose.mulVec z) = vectorNormSq z := by
  have he : vectorNormSq (Q.transpose.mulVec z) = dotProduct z ((Q * Q.transpose).mulVec z) := by
    rw [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
    simp only [vectorNormSq, dotProduct, pow_two]
  rw [he, hQ, Matrix.one_mulVec]
  simp only [vectorNormSq, dotProduct, pow_two]

theorem orthogonal_conjugate_diagonal_quadratic
    (Q : Matrix (Fin r) (Fin r) ℝ) (d : Fin r → ℝ) (z : Vector r) :
    matrixQuadratic (Q * Matrix.diagonal d * Q.transpose) z =
      ∑ i, d i * (Q.transpose.mulVec z i) ^ 2 := by
  rw [matrixQuadratic_eq_dotProduct_mulVec, ← Matrix.mulVec_mulVec,
    ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose]
  simp only [Matrix.mulVec_diagonal, dotProduct]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem orthogonal_conjugate_diagonal_mem_traceUnitBall
    (Q : Matrix (Fin r) (Fin r) ℝ) (hQ : Q * Q.transpose = 1)
    (d : Fin r → ℝ) (hd : ∀ i, |d i| ≤ 1) :
    symmetricTraceUnitBall (Q * Matrix.diagonal d * Q.transpose) := by
  refine ⟨?_, ?_, ?_⟩
  · change (Q * Matrix.diagonal d * Q.transpose).transpose = _
    simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.diagonal_transpose,
      Matrix.mul_assoc]
  · intro z
    rw [orthogonal_conjugate_diagonal_quadratic]
    calc
      _ ≤ ∑ i, |d i * (Q.transpose.mulVec z i) ^ 2| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i, (Q.transpose.mulVec z i) ^ 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_of_nonneg (sq_nonneg (Q.transpose.mulVec z i))]
        exact (mul_le_mul_of_nonneg_right (hd i) (sq_nonneg _)).trans_eq (one_mul _)
      _ = _ := orthogonal_transpose_mulVec_normSq Q hQ z
  · intro j k
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply,
      mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    calc
      _ ≤ ∑ i, ((Q j i) ^ 2 + (Q k i) ^ 2) / 2 := by
        apply Finset.sum_le_sum
        intro i _
        rw [abs_mul, abs_mul]
        have hh := mul_le_mul_of_nonneg_left (hd i) (abs_nonneg (Q j i))
        have hh' := mul_le_mul_of_nonneg_right hh (abs_nonneg (Q k i))
        have hs := sq_nonneg (|Q j i| - |Q k i|)
        nlinarith [sq_abs (Q j i), sq_abs (Q k i)]
      _ = 1 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib,
          orthogonal_row_sq_sum Q hQ j, orthogonal_row_sq_sum Q hQ k]
        norm_num

theorem trace_mul_orthogonal_diagonal_eq
    (B Q : Matrix (Fin r) (Fin r) ℝ) (d : Fin r → ℝ) :
    Matrix.trace (B * (Q * Matrix.diagonal d * Q.transpose)) =
      ∑ i, d i * matrixQuadratic B (Q.transpose i) := by
  rw [← Matrix.mul_assoc, Matrix.trace_mul_cycle]
  simp only [← Matrix.mul_assoc]
  simp only [Matrix.trace, Matrix.diag_apply, Matrix.mul_diagonal]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Matrix.mul_apply, Matrix.transpose_apply, matrixQuadratic, Finset.sum_mul,
    Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun j _ => Finset.sum_congr rfl (fun k _ => by ring))

theorem spectral_orthogonal_identities (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    let Q : Matrix (Fin r) (Fin r) ℝ := hM.eigenvectorUnitary
    Q * Q.transpose = 1 ∧ Q.transpose * Q = 1 ∧
      M = Q * Matrix.diagonal hM.eigenvalues * Q.transpose := by
  dsimp only
  have hs (Q : Matrix (Fin r) (Fin r) ℝ) : star Q = Q.transpose := by
    rw [Matrix.star_eq_conjTranspose]
    exact Matrix.conjTranspose_eq_transpose_of_trivial Q
  refine ⟨?_, ?_, ?_⟩
  · simpa only [unitary.coe_star, hs] using unitary.coe_mul_star_self hM.eigenvectorUnitary
  · simpa only [unitary.coe_star, hs] using unitary.coe_star_mul_self hM.eigenvectorUnitary
  · simpa only [hs, Function.comp_apply, RCLike.ofReal_real_eq_id] using hM.spectral_theorem

/-- For a real symmetric matrix the defined continuous function is exactly
the nuclear norm: the sum of the absolute spectral eigenvalues. -/
theorem symmetricNuclearNorm_eq_sum_abs_eigenvalues
    (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    symmetricNuclearNorm M = ∑ i, |hM.eigenvalues i| := by
  let Q : Matrix (Fin r) (Fin r) ℝ := hM.eigenvectorUnitary
  obtain ⟨hQQ, hQtQ, hspec⟩ := spectral_orthogonal_identities M hM
  change Q * Q.transpose = 1 at hQQ
  change Q.transpose * Q = 1 at hQtQ
  change M = Q * Matrix.diagonal hM.eigenvalues * Q.transpose at hspec
  have hcol (i : Fin r) : vectorNormSq (Q.transpose i) = 1 := by
    exact orthogonal_row_sq_sum Q.transpose (by simpa only [Matrix.transpose_transpose] using hQtQ) i
  apply le_antisymm
  · apply csSup_le (symmetricTrace_values_nonempty M)
    rintro t ⟨B, hB, rfl⟩
    conv_lhs => rhs; rw [hspec]
    rw [trace_mul_orthogonal_diagonal_eq]
    apply Finset.sum_le_sum
    intro i _
    have hb := hB.2.1 (Q.transpose i)
    rw [hcol] at hb
    calc
      _ ≤ |hM.eigenvalues i * matrixQuadratic B (Q.transpose i)| := le_abs_self _
      _ = |hM.eigenvalues i| * |matrixQuadratic B (Q.transpose i)| := abs_mul _ _
      _ ≤ |hM.eigenvalues i| * 1 := mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = _ := mul_one _
  · let d (i : Fin r) : ℝ := if 0 ≤ hM.eigenvalues i then 1 else -1
    let B := Q * Matrix.diagonal d * Q.transpose
    have hd (i : Fin r) : |d i| ≤ 1 := by dsimp [d]; split_ifs <;> norm_num
    have hB : symmetricTraceUnitBall B := orthogonal_conjugate_diagonal_mem_traceUnitBall Q hQQ d hd
    have ht : Matrix.trace (B * M) = ∑ i, |hM.eigenvalues i| := by
      conv_lhs => rhs; rw [hspec]
      dsimp only [B]
      have he : (Q * Matrix.diagonal d * Q.transpose) *
          (Q * Matrix.diagonal hM.eigenvalues * Q.transpose) =
          Q * (Matrix.diagonal d * Matrix.diagonal hM.eigenvalues) * Q.transpose := by
        calc
          _ = (Q * Matrix.diagonal d) * (Q.transpose * Q) *
              (Matrix.diagonal hM.eigenvalues * Q.transpose) := by simp only [Matrix.mul_assoc]
          _ = _ := by rw [hQtQ, Matrix.mul_one]; simp only [Matrix.mul_assoc]
      rw [he, Matrix.trace_mul_cycle, hQtQ, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
      simp only [Matrix.trace_diagonal]
      apply Finset.sum_congr rfl
      intro i _
      dsimp only [d, Pi.mul_apply]
      split_ifs with hi
      · rw [one_mul, abs_of_nonneg hi]
      · rw [neg_one_mul, abs_of_neg (lt_of_not_ge hi)]
    rw [← ht]
    exact trace_le_symmetricNuclearNorm M B hB

def upperLeftMatrixExtension {s : ℕ} (B : Matrix (Fin r) (Fin r) ℝ) :
    Matrix (Fin (r + s)) (Fin (r + s)) ℝ :=
  Fin.addCases (fun j => Fin.addCases (B j) (fun _ => 0)) (fun _ _ => 0)

theorem upperLeftMatrixExtension_quadratic {s : ℕ} (B : Matrix (Fin r) (Fin r) ℝ)
    (z : Vector (r + s)) :
    matrixQuadratic (upperLeftMatrixExtension (s := s) B) z =
      matrixQuadratic B (fun j => z (Fin.castAdd s j)) := by
  simp [matrixQuadratic, Fin.sum_univ_add, upperLeftMatrixExtension]

theorem upperLeftMatrixExtension_mem_traceUnitBall {s : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (hB : symmetricTraceUnitBall B) :
    symmetricTraceUnitBall (upperLeftMatrixExtension (s := s) B) := by
  refine ⟨?_, ?_, ?_⟩
  · ext j k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa [upperLeftMatrixExtension, Matrix.transpose_apply] using congrFun (congrFun hB.1 j) k
    all_goals simp [upperLeftMatrixExtension, Matrix.transpose_apply]
  · intro z
    rw [upperLeftMatrixExtension_quadratic]
    apply (hB.2.1 _).trans
    have hn := Finset.sum_nonneg (fun j (_ : j ∈ (Finset.univ : Finset (Fin s))) =>
      sq_nonneg (z (Fin.natAdd r j)))
    simpa only [vectorNormSq, Fin.sum_univ_add] using le_add_of_nonneg_right hn
  · intro j k
    refine Fin.addCases (fun j => ?_) (fun j => ?_) j <;>
      refine Fin.addCases (fun k => ?_) (fun k => ?_) k
    · simpa [upperLeftMatrixExtension] using hB.2.2 j k
    all_goals simp [upperLeftMatrixExtension]

theorem upperLeftMatrixExtension_trace_mul {s : ℕ}
    (B : Matrix (Fin r) (Fin r) ℝ) (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) :
    Matrix.trace (upperLeftMatrixExtension (s := s) B * M) =
      Matrix.trace (B * M.submatrix (Fin.castAdd s) (Fin.castAdd s)) := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_add, upperLeftMatrixExtension]

/-- Compression to the original coordinates cannot increase the actual
symmetric nuclear norm. This is the last deterministic step in the padded
normal regularization, and it assumes no positive eigenvalue. -/
theorem symmetricNuclearNorm_upperLeft_le {s : ℕ}
    (M : Matrix (Fin (r + s)) (Fin (r + s)) ℝ) :
    symmetricNuclearNorm (M.submatrix (Fin.castAdd s) (Fin.castAdd s)) ≤ symmetricNuclearNorm M := by
  apply csSup_le (symmetricTrace_values_nonempty _)
  rintro t ⟨B, hB, rfl⟩
  rw [← upperLeftMatrixExtension_trace_mul]
  exact trace_le_symmetricNuclearNorm M (upperLeftMatrixExtension B)
    (upperLeftMatrixExtension_mem_traceUnitBall B hB)

end

end RectangleCLT.Companion.SplitV4
