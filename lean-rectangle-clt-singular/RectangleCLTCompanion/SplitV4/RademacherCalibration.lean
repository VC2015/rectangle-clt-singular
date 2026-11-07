import RectangleCLTCompanion.SplitV4.ModerateTailGeneral
import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaximum

/-! Actual Rademacher scalar and maximum laws, and their uniform relative tails. -/
open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def familySignCells {I J : Type*} (z : I → J → Bool) : I × J → Bool := fun ij => z ij.1 ij.2
def familySignRows {I J : Type*} (z : I × J → Bool) : I → J → Bool := fun i j => z (i,j)

theorem familyBoolean_product_cells_law {I J : Type*} [Fintype I] [Fintype J] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => familyBernoulli familyHalf))).map familySignCells =
      Measure.pi (fun _ : I × J => familyBernoulli familyHalf) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  have hm : Measurable (familySignCells (I := I) (J := J)) := measurable_pi_lambda _ (fun ij =>
    (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have he : familySignCells ⁻¹' (univ.pi s) = univ.pi (fun i : I => univ.pi (fun j : J => s (i,j))) := by
    ext z
    simp [familySignCells]
  rw [he, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type (fun ij : I × J => familyBernoulli familyHalf (s ij))).symm

theorem familyBoolean_product_columns_law {I J : Type*} [Fintype I] [Fintype J] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => familyBernoulli familyHalf))).map (fun z j i => z i j) =
      Measure.pi (fun _ : J => Measure.pi (fun _ : I => familyBernoulli familyHalf)) := by
  let cells := familySignCells (I := I) (J := J)
  let rows := familySignRows (I := J) (J := I)
  have hcells : Measurable cells := measurable_of_finite _
  have hrows : Measurable rows := measurable_of_finite _
  let e := MeasurableEquiv.piCongrLeft (fun _ : J × I => Bool) (Equiv.prodComm I J)
  have he : MeasurePreserving e (Measure.pi (fun _ : I × J => familyBernoulli familyHalf))
      (Measure.pi (fun _ : J × I => familyBernoulli familyHalf)) :=
    measurePreserving_piCongrLeft (fun _ : J × I => familyBernoulli familyHalf) (Equiv.prodComm I J)
  have hrowlaw : (Measure.pi (fun _ : J × I => familyBernoulli familyHalf)).map rows =
      Measure.pi (fun _ : J => Measure.pi (fun _ : I => familyBernoulli familyHalf)) := by
    rw [← familyBoolean_product_cells_law (I := J) (J := I), Measure.map_map hrows (measurable_of_finite _)]
    exact Measure.map_id
  calc
    _ = (((Measure.pi (fun _ : I => Measure.pi (fun _ : J => familyBernoulli familyHalf))).map cells).map e).map rows := by
      rw [Measure.map_map he.measurable hcells, Measure.map_map hrows (he.measurable.comp hcells)]
      rfl
    _ = ((Measure.pi (fun _ : I × J => familyBernoulli familyHalf)).map e).map rows := by
      rw [show (Measure.pi (fun _ : I => Measure.pi (fun _ : J => familyBernoulli familyHalf))).map cells =
        Measure.pi (fun _ : I × J => familyBernoulli familyHalf) from familyBoolean_product_cells_law]
    _ = _ := by rw [he.map_eq, hrowlaw]

def familyRademacherScalarSum {n : ℕ} (z : Fin n → Bool) : ℝ :=
  (1 / Real.sqrt n) * ∑ i, familySign (z i)
def familyRademacherCDF (n : ℕ) (x : ℝ) : ℝ := (familySignLaw n).real {z | familyRademacherScalarSum z ≤ x}
def familyRademacherUpperTail (n : ℕ) (x : ℝ) : ℝ := (familySignLaw n).real {z | x < familyRademacherScalarSum z}

theorem familyRademacherMaximum_cdf (n m : ℕ) [NeZero m] (x : ℝ) :
    (familySignArrayLaw n m).real {z | familyRademacherMaximum z ≤ x} = familyRademacherCDF n x ^ m := by
  have hlaw : (familySignArrayLaw n m).map (fun z j i => z i j) =
      Measure.pi (fun _ : Fin m => familySignLaw n) := familyBoolean_product_columns_law
  have hs : MeasurableSet {z : Fin n → Bool | familyRademacherScalarSum z ≤ x} :=
    measurableSet_le (measurable_of_finite _) measurable_const
  have hprob := congrArg (fun μ : Measure (Fin m → Fin n → Bool) => μ.real
    (univ.pi (fun _ : Fin m => {z | familyRademacherScalarSum z ≤ x}))) hlaw
  dsimp only at hprob
  rw [map_measureReal_apply (measurable_of_finite _) (MeasurableSet.univ_pi (fun _ => hs))] at hprob
  have heq : (fun z : Fin n → FamilySigns m => fun j i => z i j) ⁻¹'
      univ.pi (fun _ : Fin m => {z | familyRademacherScalarSum z ≤ x}) =
      {z | familyRademacherMaximum z ≤ x} := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, mem_setOf_eq, forall_const]
    constructor
    · intro h
      exact finiteMaximum_le _ (fun j => h j)
    · intro h j
      exact (le_finiteMaximum (familyRademacherCoordinate z) j).trans h
  rw [heq] at hprob
  simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod, Finset.prod_const, Finset.card_univ,
    Fintype.card_fin, ENNReal.toReal_pow, familyRademacherCDF] at hprob
  exact hprob

theorem familyRademacherCDF_eq_one_sub (n : ℕ) (x : ℝ) :
    familyRademacherCDF n x = 1 - familyRademacherUpperTail n x := by
  unfold familyRademacherCDF familyRademacherUpperTail
  have hs : MeasurableSet {z : Fin n → Bool | x < familyRademacherScalarSum z} :=
    measurableSet_lt measurable_const (measurable_of_finite _)
  rw [show {z : Fin n → Bool | familyRademacherScalarSum z ≤ x} = {z | x < familyRademacherScalarSum z}ᶜ by ext; simp,
    measureReal_compl hs, measureReal_univ_eq_one]

def rademacherIncrements {n : ℕ} (i : Fin n) (z : Fin n → Bool) : ℝ := (1 / Real.sqrt n) * familySign (z i)

theorem rademacherIncrements_integral (n : ℕ) (i : Fin n) :
    (∫ z, rademacherIncrements i z ∂familySignLaw n) = 0 := by
  unfold rademacherIncrements
  rw [integral_const_mul, integral_familySignLaw_sign, mul_zero]

theorem rademacherIncrements_second {n : ℕ} (hn : 1 ≤ n) :
    (∑ i, ∫ z, rademacherIncrements i z ^ 2 ∂familySignLaw n) = 1 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  simp only [rademacherIncrements, mul_pow, familySign_sq, mul_one, integral_const,
    measureReal_univ_eq_one, one_smul, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul, div_pow, one_pow, Real.sq_sqrt hn0.le]
  exact mul_one_div_cancel hn0.ne'

theorem rademacherIncrements_gamma (n : ℕ) :
    moderateArrayGamma (familySignLaw n) (rademacherIncrements (n := n)) = 0 := by
  have hc (b : Bool) : familySign b ^ 3 = familySign b := by cases b <;> norm_num [familySign]
  unfold moderateArrayGamma rademacherIncrements
  simp_rw [mul_pow, hc, integral_const_mul, integral_familySignLaw_sign, mul_zero]
  simp

theorem familyRademacher_log_tail {n : ℕ} (hn : 1 ≤ n) {x : ℝ} (hx : 0 ≤ x)
    (hsmall : moderateTailSmallConstant * ((1 / Real.sqrt n) * (1 + x)) ≤ 1) :
    0 < familyRademacherUpperTail n x ∧
    |Real.log (familyRademacherUpperTail n x / standardNormalUpperTail x)| ≤
      moderateTailRemainderConstant * ((1 + x) / Real.sqrt n + x ^ 4 / n) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt := Real.sqrt_pos.mpr hn0
  have hb (i : Fin n) : ∀ᵐ z ∂familySignLaw n, |rademacherIncrements i z| ≤ 1 / Real.sqrt n := by
    apply ae_of_all
    intro z
    simp only [rademacherIncrements, abs_mul, abs_familySign, mul_one, abs_of_pos (div_pos zero_lt_one hsqrt)]
    exact le_rfl
  have hind : iIndepFun (rademacherIncrements (n := n)) (familySignLaw n) :=
    (familyPi_iIndepFun (fun _ : Fin n => familyBernoulli familyHalf)).comp
      (fun _ b => (1 / Real.sqrt n) * familySign b) (fun _ => measurable_of_finite _)
  have hh := moderateScalarTail_bound hn (fun _ => measurable_of_finite _) hind (by positivity : 0 ≤ 1 / Real.sqrt (n : ℝ))
    hb (rademacherIncrements_integral n) (rademacherIncrements_second hn) hx hsmall
  have hsum : moderateScalarSum (rademacherIncrements (n := n)) = familyRademacherScalarSum := by
    funext z
    simp only [moderateScalarSum, rademacherIncrements, familyRademacherScalarSum, Finset.mul_sum]
  rw [hsum, rademacherIncrements_gamma] at hh
  simpa only [familyRademacherUpperTail, zero_mul, zero_div, sub_zero,
    show (1 / Real.sqrt (n : ℝ)) * (1 + x) + (1 / Real.sqrt (n : ℝ)) ^ 2 * x ^ 4 =
      (1 + x) / Real.sqrt n + x ^ 4 / n by rw [div_pow, one_pow, Real.sq_sqrt hn0.le]; ring] using hh

end
end RectangleCLT.Companion.SplitV4
