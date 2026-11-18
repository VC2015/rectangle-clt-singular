import RectangleCLTArxivV1.CapLocalMass
import RectangleCLTCompanion.SplitV4.LogisticPaddingLimits

/-! Integrable scalar majorants for the genuine logistic selector weights. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem cap_logistic_single_le (s D : ℝ) (hD1 : 1 ≤ D) (hDs : Real.exp s ≤ D) :
    Real.exp s / D^2 ≤ capLaplace s := by
  let M := max 0 s
  have hM : Real.exp M ≤ D := by
    rcases le_total 0 s with hs | hs
    · simpa [M,max_eq_right hs] using hDs
    · simpa [M,max_eq_left hs] using hD1
  have hMpos := Real.exp_pos M
  have hDpos : 0 < D := lt_of_lt_of_le zero_lt_one hD1
  have hpow : Real.exp (2*M) ≤ D^2 := by
    have he : Real.exp (2*M) = Real.exp M^2 := by simpa using Real.exp_nat_mul M 2
    rw [he]
    exact pow_le_pow_left₀ hMpos.le hM 2
  have hscalar : s-2*M ≤ -(|s|/2) := by
    rcases le_total 0 s with hs | hs
    · simp only [M,max_eq_right hs,abs_of_nonneg hs]; linarith
    · simp only [M,max_eq_left hs,abs_of_nonpos hs]; linarith
  calc
    _ ≤ Real.exp s / Real.exp (2*M) := div_le_div_of_nonneg_left (Real.exp_pos s).le (Real.exp_pos _) hpow
    _ = Real.exp (s-2*M) := (Real.exp_sub _ _).symm
    _ ≤ capLaplace s := Real.exp_le_exp.mpr hscalar

theorem cap_logistic_pair_le (s t D : ℝ) (hD1 : 1 ≤ D)
    (hDs : Real.exp s ≤ D) (hDt : Real.exp t ≤ D) :
    Real.exp s * Real.exp t / D^3 ≤ capLaplace s*capLaplace t := by
  let M := max 0 (max s t)
  have hM : Real.exp M ≤ D := by
    rcases le_total 0 (max s t) with hm | hm
    · rw [show M = max s t from max_eq_right hm]
      rcases le_total s t with hst | hst
      · simpa [max_eq_right hst] using hDt
      · simpa [max_eq_left hst] using hDs
    · simpa [M,max_eq_left hm] using hD1
  have hMpos := Real.exp_pos M
  have hpow : Real.exp (3*M) ≤ D^3 := by
    have he : Real.exp (3*M) = Real.exp M^3 := by simpa using Real.exp_nat_mul M 3
    rw [he]
    exact pow_le_pow_left₀ hMpos.le hM 3
  have hscalar : s+t-3*M ≤ -(|s|/2)-(|t|/2) := by
    have hM0 : 0 ≤ M := le_max_left _ _
    have hMs : s ≤ M := (le_max_left s t).trans (le_max_right 0 _)
    have hMt : t ≤ M := (le_max_right s t).trans (le_max_right 0 _)
    rcases le_total 0 s with hs | hs <;> rcases le_total 0 t with ht | ht
    · rw [abs_of_nonneg hs,abs_of_nonneg ht]; linarith
    · rw [abs_of_nonneg hs,abs_of_nonpos ht]; linarith
    · rw [abs_of_nonpos hs,abs_of_nonneg ht]; linarith
    · rw [abs_of_nonpos hs,abs_of_nonpos ht]; linarith
  calc
    _ ≤ Real.exp s * Real.exp t / Real.exp (3*M) :=
      div_le_div_of_nonneg_left (by positivity) (Real.exp_pos _) hpow
    _ = Real.exp (s+t-3*M) := by rw [← Real.exp_add,← Real.exp_sub]
    _ ≤ capLaplace s*capLaplace t := by
      unfold capLaplace
      rw [← Real.exp_add]
      exact Real.exp_le_exp.mpr hscalar

theorem logisticTupleWeight_single_le_capLaplace {m r : ℕ}
    (U : Fin m → Vector r) (a : Vector m) (h : ℝ) (j : Fin m) (x : Vector r) :
    logisticTupleWeight U a h ![j] x ≤ capLaplace ((faceDot (U j) x-a j)/h) := by
  let D := 1+∑ k, Real.exp ((faceDot (U k) x-a k)/h)
  have hsum : 0 ≤ ∑ k, Real.exp ((faceDot (U k) x-a k)/h) := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith
  have hDs : Real.exp ((faceDot (U j) x-a j)/h) ≤ D := by
    have hj : Real.exp ((faceDot (U j) x-a j)/h) ≤ ∑ k, Real.exp ((faceDot (U k) x-a k)/h) :=
      Finset.single_le_sum (f := fun k => Real.exp ((faceDot (U k) x-a k)/h))
        (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ j)
    dsimp only [D]
    linarith
  have he : logisticTupleWeight U a h ![j] x = Real.exp ((faceDot (U j) x-a j)/h)/D^2 := by
    simp only [logisticTupleWeight,Fin.prod_univ_one,Matrix.cons_val_zero,logisticFaceWeight,logisticNullWeight]
    change (1/D)*(Real.exp ((faceDot (U j) x-a j)/h)*(1/D)) = _
    field_simp
    ring
  rw [he]
  exact cap_logistic_single_le _ D hD1 hDs

theorem logisticTupleWeight_pair_le_capLaplace {m r : ℕ}
    (U : Fin m → Vector r) (a : Vector m) (h : ℝ) (j k : Fin m) (x : Vector r) :
    logisticTupleWeight U a h ![j,k] x ≤
      capLaplace ((faceDot (U j) x-a j)/h)*capLaplace ((faceDot (U k) x-a k)/h) := by
  let D := 1+∑ l, Real.exp ((faceDot (U l) x-a l)/h)
  have hsum : 0 ≤ ∑ l, Real.exp ((faceDot (U l) x-a l)/h) := Finset.sum_nonneg (fun _ _ => (Real.exp_pos _).le)
  have hD1 : 1 ≤ D := by dsimp only [D]; linarith
  have hD (l : Fin m) : Real.exp ((faceDot (U l) x-a l)/h) ≤ D := by
    have hl : Real.exp ((faceDot (U l) x-a l)/h) ≤ ∑ k, Real.exp ((faceDot (U k) x-a k)/h) :=
      Finset.single_le_sum (f := fun k => Real.exp ((faceDot (U k) x-a k)/h))
        (fun k _ => (Real.exp_pos _).le) (Finset.mem_univ l)
    dsimp only [D]
    linarith
  have he : logisticTupleWeight U a h ![j,k] x =
      Real.exp ((faceDot (U j) x-a j)/h)*Real.exp ((faceDot (U k) x-a k)/h)/D^3 := by
    simp only [logisticTupleWeight,Fin.prod_univ_two,Matrix.cons_val_zero,Matrix.cons_val_one,
      logisticFaceWeight,logisticNullWeight]
    change (1/D)*((Real.exp ((faceDot (U j) x-a j)/h)*(1/D))*
      (Real.exp ((faceDot (U k) x-a k)/h)*(1/D))) = _
    field_simp
    ring
  rw [he]
  exact cap_logistic_pair_le _ _ D hD1 (hD j) (hD k)

end
end RectangleCLTArxivV1
