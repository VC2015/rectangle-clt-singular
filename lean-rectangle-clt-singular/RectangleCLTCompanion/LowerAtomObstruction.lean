import RectangleCLTCompanion.LowerProductArray
import RectangleCLTCompanion.ConsistencyStatement
import RectangleCLT.GaussianMarginalCoupling

/-! An actual atom obstruction when the normalized envelope does not vanish.
The all-negative event already suffices for the necessary envelope condition
in Theorem 5; no sharp rank-one minimax assertion is made here. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped BigOperators Topology

namespace RectangleCLT.Companion

noncomputable section

theorem lowerTwoPointLaw_negative_atom {B : ℝ} (hB : 0 < B) :
    lowerTwoPointLaw B {-B⁻¹} = ENNReal.ofReal (B ^ 2 / (B ^ 2 + 1)) := by
  have hne : B ≠ -B⁻¹ := by linarith [inv_pos.mpr hB]
  simp [lowerTwoPointLaw, hne]

def lowerAllNegativeValue (B : ℝ) (n : ℕ) : ℝ :=
  (n : ℝ) * (1 / Real.sqrt n) * (-B⁻¹)

def lowerCoordinateAtomRectangle {p : ℕ} (j : Fin p) (v : ℝ) : Rect p where
  interval := fun k => if k = j then Icc v v else univ
  ordConnected := fun k => by split_ifs <;> first | exact ordConnected_Icc | exact ordConnected_univ
  measurable := fun k => by split_ifs <;> first | exact measurableSet_Icc | exact MeasurableSet.univ

theorem lowerCoordinateAtomRectangle_carrier {p : ℕ} (j : Fin p) (v : ℝ) :
    (lowerCoordinateAtomRectangle j v).carrier = {x | x j = v} := by
  ext x
  change (∀ k ∈ univ, x k ∈ if k = j then Icc v v else univ) ↔ x j = v
  constructor
  · intro hx
    have hh := hx j (mem_univ j)
    simpa using hh
  · intro hx k _
    by_cases hkj : k = j
    · subst k
      simp [hx]
    · simp [hkj]

theorem lowerCoordinateAtomRectangle_gaussian_zero {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (j : Fin p) (v : ℝ) :
    (gaussianLaw A).real (lowerCoordinateAtomRectangle j v).carrier = 0 := by
  rw [lowerCoordinateAtomRectangle_carrier]
  have hs : {x : Vector p | x j = v} = {x | v ≤ x j ∧ x j ≤ v} := by
    ext x
    change x j = v ↔ v ≤ x j ∧ x j ≤ v
    constructor
    · rintro rfl
      exact ⟨le_rfl, le_rfl⟩
    · intro hx
      exact le_antisymm hx.2 hx.1
  rw [hs]
  exact le_antisymm (by simpa only [sub_self] using
    gaussianLaw_coordinate_strip_le A hdiag j v v le_rfl) measureReal_nonneg

theorem lowerArrayLaw_all_negative_mass {B : ℝ} (hB : 0 < B)
    {n p : ℕ} (j : Fin p) :
    (lowerArrayLaw B n p).real {z | ∀ i, z i j = -B⁻¹} =
      (B ^ 2 / (B ^ 2 + 1)) ^ n := by
  have hrow : lowerRowLaw B p {x | x j = -B⁻¹} =
      ENNReal.ofReal (B ^ 2 / (B ^ 2 + 1)) := by
    have hm := lowerRowLaw_map_coordinate B j
    have hh := congrArg (fun ν : Measure ℝ => ν {-B⁻¹}) hm
    change ((lowerRowLaw B p).map (fun x => x j)) {-B⁻¹} =
      lowerTwoPointLaw B {-B⁻¹} at hh
    rw [Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton _),
      lowerTwoPointLaw_negative_atom hB] at hh
    exact hh
  have hevent : {z : Fin n → Vector p | ∀ i, z i j = -B⁻¹} =
      Set.pi univ (fun _ : Fin n => {x : Vector p | x j = -B⁻¹}) := by
    ext z
    simp
  simp only [Measure.real, hevent, lowerArrayLaw, Measure.pi_pi, hrow,
    Finset.prod_const, Finset.card_univ, Fintype.card_fin, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal (by positivity : 0 ≤ B ^ 2 / (B ^ 2 + 1))]

theorem lowerArrayLaw_atom_error {B : ℝ} (hB : 1 ≤ B)
    {n p : ℕ} (j : Fin p) :
    (B ^ 2 / (B ^ 2 + 1)) ^ n ≤
      rectangleError (lowerArrayLaw B n p)
        (sumVector (lowerNormalizedRows (n := n) (p := p))) 1
        (lowerCoordinateAtomRectangle j (lowerAllNegativeValue B n)) := by
  have hBp : 0 < B := by linarith
  have hsubset : {z : Fin n → Vector p | ∀ i, z i j = -B⁻¹} ⊆
      sumVector (lowerNormalizedRows (n := n) (p := p)) ⁻¹'
        (lowerCoordinateAtomRectangle j (lowerAllNegativeValue B n)).carrier := by
    intro z hz
    change ∀ i, z i j = -B⁻¹ at hz
    rw [lowerCoordinateAtomRectangle_carrier]
    change sumVector lowerNormalizedRows z j = lowerAllNegativeValue B n
    simp only [sumVector, lowerNormalizedRows, lowerRawRows, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, hz, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, lowerAllNegativeValue]
    ring
  have hm := measureReal_mono (μ := lowerArrayLaw B n p) hsubset
  rw [lowerArrayLaw_all_negative_mass hBp] at hm
  have hdiag : ∀ k : Fin p, ((1 : Matrix (Fin p) (Fin p) ℝ) *
      (1 : Matrix (Fin p) (Fin p) ℝ).transpose) k k = 1 := by simp
  unfold rectangleError
  rw [lowerCoordinateAtomRectangle_gaussian_zero 1 hdiag j (lowerAllNegativeValue B n),
    sub_zero, abs_of_nonneg measureReal_nonneg]
  exact hm

theorem lower_all_negative_mass_ge_exp {B : ℝ} (hB : 0 < B) (n : ℕ) :
    Real.exp (-(n : ℝ) / B ^ 2) ≤ (B ^ 2 / (B ^ 2 + 1)) ^ n := by
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hx : 0 < 1 + 1 / B ^ 2 := by positivity
  have hlog : Real.log (1 + 1 / B ^ 2) ≤ 1 / B ^ 2 := by
    linarith only [Real.log_le_sub_one_of_pos hx]
  have hbase : Real.exp (-1 / B ^ 2) ≤ B ^ 2 / (B ^ 2 + 1) := by
    calc
      _ ≤ Real.exp (-Real.log (1 + 1 / B ^ 2)) :=
        Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hlog)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log hx]
        field_simp <;> ring
  have hh := pow_le_pow_left₀ (Real.exp_pos _).le hbase n
  convert hh using 1
  rw [← Real.exp_nat_mul]
  congr 1
  ring

theorem lower_atom_error_ge_of_envelope {B ε : ℝ} (hB : 1 ≤ B)
    {n p : ℕ} (hn : 1 ≤ n) (hε : 0 < ε)
    (hδ : ε ≤ B / Real.sqrt n) (j : Fin p) :
    Real.exp (-1 / ε ^ 2) ≤
      rectangleError (lowerArrayLaw B n p)
        (sumVector (lowerNormalizedRows (n := n) (p := p))) 1
        (lowerCoordinateAtomRectangle j (lowerAllNegativeValue B n)) := by
  have hBp : 0 < B := by linarith
  have hnR : (0 : ℝ) < n := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hn)
  have hs : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.mpr hnR
  have hmul : ε * Real.sqrt (n : ℝ) ≤ B := (le_div_iff₀ hs).mp hδ
  have hsq := pow_le_pow_left₀ (mul_nonneg hε.le hs.le) hmul 2
  rw [mul_pow, Real.sq_sqrt hnR.le] at hsq
  have hrat : (n : ℝ) / B ^ 2 ≤ 1 / ε ^ 2 := by
    apply (div_le_div_iff₀ (sq_pos_of_pos hBp) (sq_pos_of_pos hε)).mpr
    nlinarith only [hsq]
  exact (Real.exp_le_exp.mpr (by simpa only [neg_div] using neg_le_neg hrat)).trans
    ((lower_all_negative_mass_ge_exp hBp n).trans (lowerArrayLaw_atom_error hB j))

end

end RectangleCLT.Companion
