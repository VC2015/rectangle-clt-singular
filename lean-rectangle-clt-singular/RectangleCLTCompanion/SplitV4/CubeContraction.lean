import RectangleCLTCompanion.SplitV4.IntrinsicCubeBoundary

/-! The actual finite-sign contraction used in the conditional variance
argument of Lemma 1. The proof replaces one sign coordinate at a time;
its hypotheses concern coefficient differences, not concentration. -/

open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def finiteFamilyMaximum {J : Type*} [Fintype J] [Nonempty J] (A : J → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty A

theorem finiteFamilyMaximum_attains {J : Type*} [Fintype J] [Nonempty J] (A : J → ℝ) :
    ∃ j, finiteFamilyMaximum A = A j := by
  obtain ⟨j, _, hj⟩ := Finset.exists_mem_eq_sup' (s := Finset.univ) Finset.univ_nonempty A
  exact ⟨j, hj⟩

theorem le_finiteFamilyMaximum {J : Type*} [Fintype J] [Nonempty J] (A : J → ℝ) (j : J) :
    A j ≤ finiteFamilyMaximum A := Finset.le_sup' (f := A) (Finset.mem_univ j)

theorem finiteFamilyMaximum_mono {J : Type*} [Fintype J] [Nonempty J]
    {A B : J → ℝ} (h : ∀ j, A j ≤ B j) : finiteFamilyMaximum A ≤ finiteFamilyMaximum B := by
  obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains A
  rw [hj]
  exact (h j).trans (le_finiteFamilyMaximum B j)

theorem finiteFamilyMaximum_nonneg_scale {J : Type*} [Fintype J] [Nonempty J]
    (A : J → ℝ) (c : ℝ) (hc : 0 ≤ c) :
    finiteFamilyMaximum (fun j => c * A j) = c * finiteFamilyMaximum A := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains (fun j => c * A j)
    rw [hj]
    exact mul_le_mul_of_nonneg_left (le_finiteFamilyMaximum A j) hc
  · obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains A
    rw [hj]
    exact le_finiteFamilyMaximum (fun j => c * A j) j

/-- The one-sign replacement inequality for arbitrary offsets. -/
theorem finiteMaximum_pair_contraction {J : Type*} [Fintype J] [Nonempty J]
    (A Φ Z : J → ℝ) (L : ℝ)
    (hLip : ∀ j k, |Φ j - Φ k| ≤ L * |Z j - Z k|) :
    finiteFamilyMaximum (fun j => A j + Φ j) + finiteFamilyMaximum (fun j => A j - Φ j) ≤
      finiteFamilyMaximum (fun j => A j + L * Z j) +
        finiteFamilyMaximum (fun j => A j - L * Z j) := by
  obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains (fun j => A j + Φ j)
  obtain ⟨k, hk⟩ := finiteFamilyMaximum_attains (fun j => A j - Φ j)
  rw [hj, hk]
  have hφ := (le_abs_self (Φ j - Φ k)).trans (hLip j k)
  by_cases hz : Z k ≤ Z j
  · rw [abs_of_nonneg (sub_nonneg.mpr hz)] at hφ
    have h₁ := le_finiteFamilyMaximum (fun j => A j + L * Z j) j
    have h₂ := le_finiteFamilyMaximum (fun j => A j - L * Z j) k
    nlinarith
  · rw [abs_of_nonpos (sub_nonpos.mpr (le_of_not_ge hz))] at hφ
    have h₁ := le_finiteFamilyMaximum (fun j => A j + L * Z j) k
    have h₂ := le_finiteFamilyMaximum (fun j => A j - L * Z j) j
    nlinarith

theorem cube_avg_coordinate_pair {n : ℕ} (f : Kane.Cube n → ℝ) (i : Fin n) :
    Kane.avg f = Kane.avg (fun x =>
      (f (Function.update x i true) + f (Function.update x i false)) / 2) := by
  have hp (x : Kane.Cube n) : f x + f (Kane.flip x i) =
      f (Function.update x i true) + f (Function.update x i false) := by
    cases hx : x i
    · have hs : Function.update x i false = x := by simpa only [hx] using Function.update_eq_self i x
      simp [Kane.flip, hx, hs, add_comm]
    · have hs : Function.update x i true = x := by simpa only [hx] using Function.update_eq_self i x
      simp [Kane.flip, hx, hs]
  have ha := Kane.avg_congr hp
  rw [Kane.avg_add, Kane.avg_flip] at ha
  have hh := Kane.avg_const_mul (1 / 2 : ℝ)
    (fun x => f (Function.update x i true) + f (Function.update x i false))
  have he : Kane.avg (fun x =>
      (f (Function.update x i true) + f (Function.update x i false)) / 2) =
      (1 / 2 : ℝ) * Kane.avg (fun x =>
        f (Function.update x i true) + f (Function.update x i false)) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hh
  rw [he]
  linarith

theorem cubeLinear_update_coordinate {n : ℕ} (Z : Fin n → ℝ) (x : Kane.Cube n)
    (i : Fin n) (q : Bool) :
    cubeLinear Z (Function.update x i q) =
      (∑ k ∈ Finset.univ.erase i, Z k * cubeSign x k) + Z i * (if q then 1 else -1) := by
  classical
  unfold cubeLinear
  rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  congr 1
  · apply Finset.sum_congr rfl
    intro k hk
    simp only [cubeSign, Function.update_of_ne (Finset.ne_of_mem_erase hk)]
  · simp [cubeSign]

/-- Replace one coefficient column under the true cube average. -/
theorem cube_average_one_column_contraction
    {J : Type*} [Fintype J] [Nonempty J] {n : ℕ}
    (P Q : J → Fin n → ℝ) (i : Fin n)
    (hsame : ∀ j k, k ≠ i → P j k = Q j k)
    (hLip : ∀ j k, |P j i - P k i| ≤ |Q j i - Q k i|) :
    Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (P j) x)) ≤
      Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (Q j) x)) := by
  rw [cube_avg_coordinate_pair (fun x => finiteFamilyMaximum (fun j => cubeLinear (P j) x)) i,
    cube_avg_coordinate_pair (fun x => finiteFamilyMaximum (fun j => cubeLinear (Q j) x)) i]
  apply Kane.avg_mono
  intro x
  have hsum (j : J) :
      (∑ k ∈ Finset.univ.erase i, P j k * cubeSign x k) =
        ∑ k ∈ Finset.univ.erase i, Q j k * cubeSign x k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsame j k (Finset.ne_of_mem_erase hk)]
  simp_rw [cubeLinear_update_coordinate]
  simp_rw [hsum]
  simp only [Bool.true_eq, Bool.false_eq_true, ↓reduceIte, mul_one, mul_neg_one,
    ← sub_eq_add_neg]
  have hc := finiteMaximum_pair_contraction
    (fun j => ∑ k ∈ Finset.univ.erase i, Q j k * cubeSign x k)
    (fun j => P j i) (fun j => Q j i) 1 (by simpa only [one_mul] using hLip)
  simpa only [one_mul] using (div_le_div_of_nonneg_right hc (by norm_num : (0 : ℝ) ≤ 2))

/-- General contraction of finite sign maxima, proved by finite column
replacement. The coefficient-difference condition allows arbitrary
offsets as additional rows, including the zero row. -/
theorem cube_average_contraction
    {J : Type*} [Fintype J] [Nonempty J] {n : ℕ}
    (P Q : J → Fin n → ℝ)
    (hLip : ∀ i j k, |P j i - P k i| ≤ |Q j i - Q k i|) :
    Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (P j) x)) ≤
      Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (Q j) x)) := by
  classical
  let mix (s : Finset (Fin n)) (j : J) (i : Fin n) := if i ∈ s then P j i else Q j i
  have hall (s : Finset (Fin n)) :
      Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (mix s j) x)) ≤
        Kane.avg (fun x => finiteFamilyMaximum (fun j => cubeLinear (Q j) x)) := by
    induction s using Finset.induction_on with
    | empty => simp only [mix, Finset.not_mem_empty, ↓reduceIte, le_refl]
    | @insert i s hi hs =>
      apply le_trans (cube_average_one_column_contraction (mix (insert i s)) (mix s) i ?_ ?_) hs
      · intro j k hki
        simp only [mix, Finset.mem_insert, hki, false_or]
      · intro j k
        simpa only [mix, Finset.mem_insert_self, ↓reduceIte, hi] using hLip i j k
  simpa only [mix, Finset.mem_univ, ↓reduceIte] using hall Finset.univ

def cubeReflect {n : ℕ} (x : Kane.Cube n) : Kane.Cube n := fun i => !(x i)

theorem cubeReflect_involutive {n : ℕ} : Function.Involutive (cubeReflect (n := n)) := by
  intro x
  funext i
  simp [cubeReflect]

theorem cube_avg_reflect {n : ℕ} (f : Kane.Cube n → ℝ) :
    Kane.avg (fun x => f (cubeReflect x)) = Kane.avg f := by
  let e : Kane.Cube n ≃ Kane.Cube n :=
    ⟨cubeReflect, cubeReflect, cubeReflect_involutive, cubeReflect_involutive⟩
  unfold Kane.avg
  congr 1
  exact e.sum_comp f

theorem cubeLinear_reflect {n : ℕ} (Z : Fin n → ℝ) (x : Kane.Cube n) :
    cubeLinear Z (cubeReflect x) = -cubeLinear Z x := by
  unfold cubeLinear
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [cubeSign, cubeReflect, hx]

def zeroExtendedCubeRows {m n : ℕ} (Z : Fin m → Fin n → ℝ) : Fin (m + 1) → Fin n → ℝ :=
  fun j i => Fin.cases 0 (fun α => Z α i) j

theorem cubeLinear_zeroExtended {m n : ℕ} (Z : Fin m → Fin n → ℝ)
    (x : Kane.Cube n) (j : Fin (m + 1)) :
    cubeLinear (zeroExtendedCubeRows Z j) x = Fin.cases 0 (fun α => cubeLinear (Z α) x) j := by
  refine Fin.cases ?_ (fun α => ?_) j
  · simp [cubeLinear, zeroExtendedCubeRows]
  · rfl

theorem positiveLinearMaximum_eq_finiteMaximum {m n : ℕ}
    (Z : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    positiveLinearMaximum Z x =
      finiteFamilyMaximum (fun j => cubeLinear (zeroExtendedCubeRows Z j) x) := by
  simp only [cubeLinear_zeroExtended]
  rfl

theorem cubeLinear_scale {n : ℕ} (Z : Fin n → ℝ) (c : ℝ) (x : Kane.Cube n) :
    cubeLinear (fun i => c * Z i) x = c * cubeLinear Z x := by
  simp only [cubeLinear, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Squaring is `2η`-Lipschitz on the bounded coefficient interval. -/
theorem square_coefficient_difference_le (z w η : ℝ)
    (hz : |z| ≤ η) (hw : |w| ≤ η) : |z ^ 2 - w ^ 2| ≤ 2 * η * |z - w| := by
  have hsum : |z + w| ≤ 2 * η := (abs_add z w).trans (by linarith)
  calc
    |z ^ 2 - w ^ 2| = |z + w| * |z - w| := by rw [← abs_mul]; congr 1; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right hsum (abs_nonneg _)

theorem intrinsicCubeMean_square_le {m n : ℕ} (Z : Fin m → Fin n → ℝ) (η : ℝ)
    (hη : 0 ≤ η) (hZ : ∀ α i, |Z α i| ≤ η) :
    intrinsicCubeMean (fun α i => (Z α i) ^ 2) ≤ 2 * η * intrinsicCubeMean Z := by
  let ZE := zeroExtendedCubeRows Z
  have hZE (j : Fin (m + 1)) (i : Fin n) : |ZE j i| ≤ η := by
    refine Fin.cases ?_ (fun α => ?_) j
    · simpa [ZE, zeroExtendedCubeRows] using hη
    · exact hZ α i
  have hsq (j : Fin (m + 1)) (i : Fin n) :
      zeroExtendedCubeRows (fun α i => (Z α i) ^ 2) j i = (ZE j i) ^ 2 := by
    refine Fin.cases ?_ (fun α => ?_) j
    · simp [ZE, zeroExtendedCubeRows]
    · rfl
  have hLip (i : Fin n) (j k : Fin (m + 1)) :
      |zeroExtendedCubeRows (fun α i => (Z α i) ^ 2) j i -
          zeroExtendedCubeRows (fun α i => (Z α i) ^ 2) k i| ≤
        |(2 * η * ZE j i) - (2 * η * ZE k i)| := by
    rw [hsq, hsq, ← mul_sub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 2 * η)]
    exact square_coefficient_difference_le _ _ _ (hZE j i) (hZE k i)
  have hc := cube_average_contraction
    (zeroExtendedCubeRows (fun α i => (Z α i) ^ 2)) (fun j i => 2 * η * ZE j i) hLip
  have hr : Kane.avg (fun x => finiteFamilyMaximum (fun j =>
      cubeLinear (fun i => 2 * η * ZE j i) x)) = 2 * η * intrinsicCubeMean Z := by
    simp_rw [cubeLinear_scale, finiteFamilyMaximum_nonneg_scale _ _ (by positivity : 0 ≤ 2 * η)]
    rw [Kane.avg_const_mul]
    congr 1
    apply Kane.avg_congr
    intro x
    exact (positiveLinearMaximum_eq_finiteMaximum Z x).symm
  rw [hr] at hc
  calc
    _ = Kane.avg (fun x => finiteFamilyMaximum (fun j =>
        cubeLinear (zeroExtendedCubeRows (fun α i => (Z α i) ^ 2) j) x)) :=
      Kane.avg_congr (positiveLinearMaximum_eq_finiteMaximum _)
    _ ≤ _ := hc

def absoluteLinearMaximum {m n : ℕ} [NeZero m] (Z : Fin m → Fin n → ℝ) (x : Kane.Cube n) : ℝ :=
  finiteFamilyMaximum (fun α => |cubeLinear (Z α) x|)

theorem absoluteLinearMaximum_le_positive_pair {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    absoluteLinearMaximum Z x ≤ positiveLinearMaximum Z x + positiveLinearMaximum Z (cubeReflect x) := by
  obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains (fun α => |cubeLinear (Z α) x|)
  change finiteFamilyMaximum _ ≤ _
  rw [hj]
  apply abs_le.mpr
  constructor
  · have hn := cubeLinear_le_positiveMaximum Z (cubeReflect x) j
    rw [cubeLinear_reflect] at hn
    linarith [positiveLinearMaximum_nonneg Z x]
  · exact (cubeLinear_le_positiveMaximum Z x j).trans
      (le_add_of_nonneg_right (positiveLinearMaximum_nonneg Z _))

theorem avg_absoluteLinearMaximum_le_twice_intrinsic {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) :
    Kane.avg (absoluteLinearMaximum Z) ≤ 2 * intrinsicCubeMean Z := by
  calc
    _ ≤ Kane.avg (fun x => positiveLinearMaximum Z x + positiveLinearMaximum Z (cubeReflect x)) :=
      Kane.avg_mono (absoluteLinearMaximum_le_positive_pair Z)
    _ = _ := by rw [Kane.avg_add, cube_avg_reflect]; unfold intrinsicCubeMean; ring

/-- The manuscript's square-contraction inequality, with an even stronger
positive-maximum quantity retained on the right. -/
theorem cube_square_contraction_intrinsic {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hZ : ∀ α i, |Z α i| ≤ η) :
    Kane.avg (absoluteLinearMaximum (fun α i => (Z α i) ^ 2)) ≤
      4 * η * intrinsicCubeMean Z := by
  have h₁ := avg_absoluteLinearMaximum_le_twice_intrinsic (fun α i => (Z α i) ^ 2)
  have h₂ := intrinsicCubeMean_square_le Z η hη hZ
  linarith

theorem positiveLinearMaximum_le_absolute {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    positiveLinearMaximum Z x ≤ absoluteLinearMaximum Z x := by
  rcases positiveLinearMaximum_selected Z x with hz | ⟨j, hj⟩
  · rw [hz]
    exact (abs_nonneg (cubeLinear (Z (0 : Fin m)) x)).trans
      (le_finiteFamilyMaximum (fun α => |cubeLinear (Z α) x|) (0 : Fin m))
  · rw [hj]
    exact (le_abs_self _).trans (le_finiteFamilyMaximum (fun α => |cubeLinear (Z α) x|) j)

/-- Exact finite-average form of the square-contraction inequality in
Appendix C. Both sides are actual maxima of signed linear forms. -/
theorem cube_square_contraction {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hZ : ∀ α i, |Z α i| ≤ η) :
    Kane.avg (absoluteLinearMaximum (fun α i => (Z α i) ^ 2)) ≤
      4 * η * Kane.avg (absoluteLinearMaximum Z) :=
  (cube_square_contraction_intrinsic Z η hη hZ).trans
    (mul_le_mul_of_nonneg_left (Kane.avg_mono (positiveLinearMaximum_le_absolute Z)) (by positivity))

/-- Exact probability-space form of square contraction under uniform
independent signs, used inside the paired-copy variance argument. -/
theorem integral_cube_square_contraction {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hZ : ∀ α i, |Z α i| ≤ η) :
    (∫ x, absoluteLinearMaximum (fun α i => (Z α i) ^ 2) x ∂cubeUniformLaw n) ≤
      4 * η * ∫ x, absoluteLinearMaximum Z x ∂cubeUniformLaw n := by
  rw [integral_cubeUniformLaw_eq_avg, integral_cubeUniformLaw_eq_avg]
  exact cube_square_contraction Z η hη hZ

theorem absoluteLinearMaximum_eq_norm {m n : ℕ} [NeZero m]
    (Z : Fin m → Fin n → ℝ) (x : Kane.Cube n) :
    absoluteLinearMaximum Z x = ‖fun α => cubeLinear (Z α) x‖ := by
  apply le_antisymm
  · obtain ⟨j, hj⟩ := finiteFamilyMaximum_attains (fun α => |cubeLinear (Z α) x|)
    change finiteFamilyMaximum _ ≤ _
    rw [hj]
    exact norm_le_pi_norm (fun α => cubeLinear (Z α) x) j
  · have hm : 0 ≤ absoluteLinearMaximum Z x :=
      (abs_nonneg (cubeLinear (Z (0 : Fin m)) x)).trans
        (le_finiteFamilyMaximum (fun α => |cubeLinear (Z α) x|) (0 : Fin m))
    apply (pi_norm_le_iff_of_nonneg hm).mpr
    intro j
    exact le_finiteFamilyMaximum (fun α => |cubeLinear (Z α) x|) j

/-- Vector supremum-norm form of the same genuine sign integral. Internal
dependence among vector coordinates is unrestricted. -/
theorem integral_cube_square_contraction_vector {p n : ℕ} [NeZero p]
    (Y : Fin n → Fin p → ℝ) (η : ℝ) (hη : 0 ≤ η)
    (hY : ∀ i, ‖Y i‖ ≤ η) :
    (∫ x, ‖∑ i, cubeSign x i • (fun j => (Y i j) ^ 2)‖ ∂cubeUniformLaw n) ≤
      4 * η * ∫ x, ‖∑ i, cubeSign x i • Y i‖ ∂cubeUniformLaw n := by
  have hZ : ∀ j i, |Y i j| ≤ η := fun j i =>
    (norm_le_pi_norm (Y i) j).trans (hY i)
  have he (Q : Fin n → Fin p → ℝ) (x : Kane.Cube n) :
      absoluteLinearMaximum (fun j i => Q i j) x = ‖∑ i, cubeSign x i • Q i‖ := by
    rw [absoluteLinearMaximum_eq_norm]
    congr 1
    funext j
    simp only [cubeLinear, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hc := integral_cube_square_contraction (fun j i => Y i j) η hη hZ
  simpa only [he] using hc

end

end RectangleCLT.Companion.SplitV4
