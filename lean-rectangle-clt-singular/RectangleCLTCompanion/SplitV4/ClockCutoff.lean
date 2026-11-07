import RectangleCLT.ExponentialMixture
import RectangleCLT.Optimization
import Mathlib.Tactic

/-! A concrete high-probability exponential-clock event for the
Gaussian-endpoint smoothing argument. All probabilities use the actual
product law of the logistic random-rectangle representation. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4
noncomputable section

def clockBound (p : ℕ) : ℝ := 16 * (2 * (p : ℝ) + 1)

def clockGood (p : ℕ) : Set (ℝ × (Face p → ℝ)) :=
  {e | e.1 ∈ Icc (clockBound p)⁻¹ (clockBound p) ∧
    ∀ f, e.2 f ∈ Icc (clockBound p)⁻¹ (clockBound p)}

def clockRadius (p : ℕ) (h : ℝ) : ℝ := 2 * h * Real.log (clockBound p)

theorem clockBound_pos (p : ℕ) : 0 < clockBound p := by
  unfold clockBound
  positivity

theorem one_lt_clockBound (p : ℕ) : 1 < clockBound p := by
  unfold clockBound
  have hp : 0 ≤ (p : ℝ) := Nat.cast_nonneg p
  nlinarith

theorem measurableSet_clockGood (p : ℕ) : MeasurableSet (clockGood p) := by
  unfold clockGood
  simp only [setOf_and, setOf_forall]
  exact (measurableSet_Icc.preimage measurable_fst).inter
    (MeasurableSet.iInter fun f : Face p =>
      measurableSet_Icc.preimage ((measurable_pi_apply f).comp measurable_snd))

private theorem exponential_bad_interval_le {B : ℝ} (hB : 0 < B) :
    unitExponential.real (Icc B⁻¹ B)ᶜ ≤ 2 / B := by
  have hs : (Icc B⁻¹ B)ᶜ ⊆ Iic B⁻¹ ∪ Ioi B := by
    intro x hx
    by_cases hlo : x ≤ B⁻¹
    · exact Or.inl hlo
    · right
      by_contra hhi
      exact hx ⟨(lt_of_not_ge hlo).le, le_of_not_gt hhi⟩
  have hlo : unitExponential.real (Iic B⁻¹) ≤ B⁻¹ := by
    rw [unitExponential_Iic (inv_nonneg.mpr hB.le)]
    linarith [Real.add_one_le_exp (-B⁻¹)]
  have hhi : unitExponential.real (Ioi B) ≤ B⁻¹ := by
    rw [unitExponential_Ioi hB.le, Real.exp_neg]
    have he : B ≤ Real.exp B := by linarith [Real.add_one_le_exp B]
    simpa only [one_div] using one_div_le_one_div_of_le hB he
  calc
    _ ≤ unitExponential.real (Iic B⁻¹ ∪ Ioi B) := measureReal_mono hs
    _ ≤ unitExponential.real (Iic B⁻¹) + unitExponential.real (Ioi B) :=
      measureReal_union_le _ _
    _ ≤ B⁻¹ + B⁻¹ := add_le_add hlo hhi
    _ = _ := by ring

private theorem faceExponential_coordinate_real {p : ℕ} (f : Face p) (S : Set ℝ) :
    (faceExponentialLaw p).real {e | e f ∈ S} = unitExponential.real S := by
  classical
  have he : {e : Face p → ℝ | e f ∈ S} =
      Set.pi Set.univ (fun j => if j = f then S else Set.univ) := by
    ext e
    simp only [mem_setOf_eq, mem_pi, mem_univ, forall_true_left]
    constructor
    · intro h j
      split_ifs with hj
      · simpa only [hj] using h
      · trivial
    · intro h
      simpa using h f
  rw [he, measureReal_def, faceExponentialLaw, Measure.pi_pi]
  simp [apply_ite, measureReal_def]

private theorem clock_fst_real {p : ℕ} (S : Set ℝ) :
    (exponentialRectangleLaw p).real {e | e.1 ∈ S} = unitExponential.real S := by
  have he : {e : ℝ × (Face p → ℝ) | e.1 ∈ S} = S ×ˢ Set.univ := by
    ext e
    simp
  rw [he, exponentialRectangleLaw, measureReal_prod_prod]
  simp

private theorem clock_face_real {p : ℕ} (f : Face p) (S : Set ℝ) :
    (exponentialRectangleLaw p).real {e | e.2 f ∈ S} = unitExponential.real S := by
  have he : {e : ℝ × (Face p → ℝ) | e.2 f ∈ S} =
      Set.univ ×ˢ {e : Face p → ℝ | e f ∈ S} := by
    ext e
    simp
  rw [he, exponentialRectangleLaw, measureReal_prod_prod]
  simp only [measureReal_univ_eq_one, one_mul]
  exact faceExponential_coordinate_real f S

theorem clockGood_compl_probability_le (p : ℕ) :
    (exponentialRectangleLaw p).real (clockGood p)ᶜ ≤ 1 / 4 := by
  classical
  let S : Set ℝ := (Icc (clockBound p)⁻¹ (clockBound p))ᶜ
  have hs : (clockGood p)ᶜ ⊆ {e | e.1 ∈ S} ∪ ⋃ f : Face p, {e | e.2 f ∈ S} := by
    intro e he
    by_cases h0 : e.1 ∈ S
    · exact Or.inl h0
    · right
      by_contra hall
      apply he
      refine ⟨by simpa only [S, mem_compl_iff, not_not] using h0, ?_⟩
      intro f
      have hf : e.2 f ∉ S := fun hf => hall (mem_iUnion.mpr ⟨f, hf⟩)
      simpa only [S, mem_compl_iff, not_not] using hf
  have hbad := exponential_bad_interval_le (clockBound_pos p)
  calc
    _ ≤ (exponentialRectangleLaw p).real ({e | e.1 ∈ S} ∪ ⋃ f : Face p, {e | e.2 f ∈ S}) :=
      measureReal_mono hs
    _ ≤ (exponentialRectangleLaw p).real {e | e.1 ∈ S} +
        (exponentialRectangleLaw p).real (⋃ f : Face p, {e | e.2 f ∈ S}) :=
      measureReal_union_le _ _
    _ ≤ (exponentialRectangleLaw p).real {e | e.1 ∈ S} +
        ∑ f : Face p, (exponentialRectangleLaw p).real {e | e.2 f ∈ S} :=
      add_le_add_left (measureReal_iUnion_fintype_le _) _
    _ = (1 + 2 * (p : ℝ)) * unitExponential.real S := by
      simp only [clock_fst_real, clock_face_real, Finset.sum_const, Finset.card_univ,
        Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, Nat.cast_mul,
        Nat.cast_ofNat, nsmul_eq_mul]
      ring
    _ ≤ (1 + 2 * (p : ℝ)) * (2 / clockBound p) :=
      mul_le_mul_of_nonneg_left hbad (by positivity)
    _ ≤ 1 / 4 := by
      unfold clockBound
      have hp : 0 < 2 * (p : ℝ) + 1 := by positivity
      have he : (1 + 2 * (p : ℝ)) * (2 / (16 * (2 * (p : ℝ) + 1))) = 1 / 8 := by
        field_simp
        ring
      rw [he]
      norm_num

theorem clockRadius_pos {p : ℕ} {h : ℝ} (hh : 0 < h) : 0 < clockRadius p h := by
  exact mul_pos (mul_pos (by norm_num) hh) (Real.log_pos (one_lt_clockBound p))

theorem clockGood_shift_abs_le {p : ℕ} {h : ℝ} (hh : 0 < h)
    {e : ℝ × (Face p → ℝ)} (he : e ∈ clockGood p) (f : Face p) :
    |h * Real.log (e.2 f / e.1)| ≤ clockRadius p h := by
  have hB := clockBound_pos p
  have h0 : 0 < e.1 := lt_of_lt_of_le (inv_pos.mpr hB) he.1.1
  have hf : 0 < e.2 f := lt_of_lt_of_le (inv_pos.mpr hB) (he.2 f).1
  have hlo0 := Real.log_le_log (inv_pos.mpr hB) he.1.1
  have hhi0 := Real.log_le_log h0 he.1.2
  have hlof := Real.log_le_log (inv_pos.mpr hB) (he.2 f).1
  have hhif := Real.log_le_log hf (he.2 f).2
  rw [Real.log_inv] at hlo0 hlof
  rw [abs_mul, abs_of_pos hh, Real.log_div hf.ne' h0.ne']
  have hab : |Real.log (e.2 f) - Real.log e.1| ≤ 2 * Real.log (clockBound p) :=
    abs_le.mpr ⟨by linarith, by linarith⟩
  calc
    _ ≤ h * (2 * Real.log (clockBound p)) := mul_le_mul_of_nonneg_left hab hh.le
    _ = clockRadius p h := by unfold clockRadius; ring

theorem clockRadius_le {p : ℕ} (hp : 1 ≤ p) {h : ℝ} (hh : 0 < h) :
    clockRadius p h ≤ 12 * h * dimensionLog p := by
  have hL := log_exp_mul_nat_ge_one hp
  have hlog := log_two_mul_nat_add_one_le_two_log_exp_mul hp
  have h16 : Real.log (16 : ℝ) ≤ 4 := by
    have he : (16 : ℝ) ≤ Real.exp 4 := by
      have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
      calc
        16 = (2 : ℝ) ^ 4 := by norm_num
        _ ≤ (Real.exp 1) ^ 4 := pow_le_pow_left₀ (by norm_num) he2 4
        _ = Real.exp 4 := by rw [← Real.exp_nat_mul]; norm_num
    simpa only [Real.log_exp] using Real.log_le_log (by norm_num : (0 : ℝ) < 16) he
  have heq : Real.log (clockBound p) = Real.log 16 + Real.log (2 * (p : ℝ) + 1) := by
    unfold clockBound
    rw [Real.log_mul (by norm_num) (by positivity)]
  have hb : Real.log (clockBound p) ≤ 6 * dimensionLog p := by
    rw [heq]
    change _ ≤ 6 * Real.log (Real.exp 1 * (p : ℝ))
    linarith
  unfold clockRadius
  nlinarith [mul_le_mul_of_nonneg_left hb hh.le]

end
end RectangleCLT.Companion.SplitV4
