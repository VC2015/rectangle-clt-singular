import RectangleCLT.LocalCovariance

/-! Correlation-gap stability under entrywise perturbations.  The initial
zero in the off-diagonal maximum handles dimension one without a special
case or a nonempty off-diagonal index assumption. -/

namespace RectangleCLT.Companion

noncomputable section

theorem maxOffDiagonal_le_of_entrywise_sub_le {p : ℕ}
    (P Q : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsub : ∀ j k, j ≠ k → |P j k - Q j k| ≤ ε) :
    maxOffDiagonal P ≤ maxOffDiagonal Q + ε := by
  classical
  unfold maxOffDiagonal at ⊢
  apply (Finset.fold_max_le _).mpr
  refine ⟨add_nonneg (maxOffDiagonal_nonneg Q) hε, ?_⟩
  intro jk _
  by_cases hjk : jk.1 = jk.2
  · simp only [if_pos hjk]
    exact add_nonneg (maxOffDiagonal_nonneg Q) hε
  · simp only [if_neg hjk]
    have hQ : |Q jk.1 jk.2| ≤ maxOffDiagonal Q := by
      simpa only [pairGap, sub_sub_cancel] using abs_offDiagonal_le Q jk.1 jk.2 hjk
    calc
      _ = |(P jk.1 jk.2 - Q jk.1 jk.2) + Q jk.1 jk.2| := by rw [sub_add_cancel]
      _ ≤ |P jk.1 jk.2 - Q jk.1 jk.2| + |Q jk.1 jk.2| := abs_add _ _
      _ ≤ ε + maxOffDiagonal Q := add_le_add (hsub jk.1 jk.2 hjk) hQ
      _ = _ := add_comm _ _

theorem pairGap_sub_le_of_entrywise_sub_le {p : ℕ}
    (P Q : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsub : ∀ j k, j ≠ k → |P j k - Q j k| ≤ ε) :
    pairGap Q - ε ≤ pairGap P := by
  have hmax := maxOffDiagonal_le_of_entrywise_sub_le P Q hε hsub
  unfold pairGap
  linarith

theorem abs_pairGap_sub_le_of_entrywise_sub_le {p : ℕ}
    (P Q : Matrix (Fin p) (Fin p) ℝ) {ε : ℝ} (hε : 0 ≤ ε)
    (hsub : ∀ j k, j ≠ k → |P j k - Q j k| ≤ ε) :
    |pairGap P - pairGap Q| ≤ ε := by
  have hPQ := pairGap_sub_le_of_entrywise_sub_le P Q hε hsub
  have hQP := pairGap_sub_le_of_entrywise_sub_le Q P hε (fun j k hjk => by
    simpa only [abs_sub_comm] using hsub j k hjk)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

end

end RectangleCLT.Companion
