import RectangleCLTCompanion.LowerProductTilt
import RectangleCLTCompanion.NormalQuantileRate

/-! Exact maximum distribution functions for the actual independent
coordinate lower construction. The row-to-column rearrangement is proved
for the genuine finite product measures. -/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion
noncomputable section

private def scalarCells {I J : Type*} (z : I → J → ℝ) : I × J → ℝ :=
  fun ij => z ij.1 ij.2

private def scalarRows {I J : Type*} (z : I × J → ℝ) : I → J → ℝ :=
  fun i j => z (i,j)

private theorem measurable_scalarCells {I J : Type*} :
    Measurable (scalarCells (I := I) (J := J)) := by
  exact measurable_pi_lambda _ (fun ij => (measurable_pi_apply ij.2).comp (measurable_pi_apply ij.1))

private theorem measurable_scalarRows {I J : Type*} :
    Measurable (scalarRows (I := I) (J := J)) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_lambda _ (fun j => measurable_pi_apply (i,j)))

theorem scalar_product_cells_law {I J : Type*} [Fintype I] [Fintype J]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν))).map scalarCells =
      Measure.pi (fun _ : I × J => ν) := by
  classical
  symm
  apply Measure.pi_eq
  intro s hs
  rw [Measure.map_apply measurable_scalarCells (MeasurableSet.univ_pi hs)]
  have heq : scalarCells ⁻¹' (univ.pi s) =
      univ.pi (fun i : I => univ.pi (fun j : J => s (i,j))) := by
    ext z
    simp [scalarCells]
  rw [heq, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  exact (Fintype.prod_prod_type fun ij : I × J => ν (s ij)).symm

theorem scalar_product_columns_law {I J : Type*} [Fintype I] [Fintype J]
    (ν : Measure ℝ) [IsProbabilityMeasure ν] :
    (Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν))).map
      (fun z j i => z i j) =
      Measure.pi (fun _ : J => Measure.pi (fun _ : I => ν)) := by
  let e := MeasurableEquiv.piCongrLeft (fun _ : J × I => ℝ) (Equiv.prodComm I J)
  have he : MeasurePreserving e
      (Measure.pi (fun _ : I × J => ν)) (Measure.pi (fun _ : J × I => ν)) :=
    measurePreserving_piCongrLeft (fun _ : J × I => ν) (Equiv.prodComm I J)
  have hrows : (Measure.pi (fun _ : J × I => ν)).map scalarRows =
      Measure.pi (fun _ : J => Measure.pi (fun _ : I => ν)) := by
    rw [← scalar_product_cells_law (I := J) (J := I) ν,
      Measure.map_map measurable_scalarRows measurable_scalarCells]
    exact Measure.map_id
  calc
    _ = (((Measure.pi (fun _ : I => Measure.pi (fun _ : J => ν))).map scalarCells).map e).map
        scalarRows := by
      rw [Measure.map_map he.measurable measurable_scalarCells,
        Measure.map_map measurable_scalarRows (he.measurable.comp measurable_scalarCells)]
      rfl
    _ = ((Measure.pi (fun _ : I × J => ν)).map e).map scalarRows := by
      rw [scalar_product_cells_law]
    _ = _ := by rw [he.map_eq, hrows]

def lowerScalarNormalizedSum {n : ℕ} (z : Fin n → ℝ) : ℝ :=
  (∑ i, z i) / Real.sqrt (n : ℝ)

def lowerCoordinateCDF (B : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (lowerScalarArrayLaw B n).real {z | lowerScalarNormalizedSum z ≤ x}

theorem lowerArrayLaw_map_columns (B : ℝ) (n p : ℕ) :
    (lowerArrayLaw B n p).map (fun z j i => z i j) =
      Measure.pi (fun _ : Fin p => lowerScalarArrayLaw B n) :=
  scalar_product_columns_law (lowerTwoPointLaw B)

theorem lowerArrayLaw_maximum_CDF (B : ℝ) (n p : ℕ) (x : ℝ) :
    (lowerArrayLaw B n p).real
      {z | ∀ j, sumVector (lowerNormalizedRows (n := n) (p := p)) z j ≤ x} =
      lowerCoordinateCDF B n x ^ p := by
  have hm : Measurable (lowerScalarNormalizedSum (n := n)) := by
    unfold lowerScalarNormalizedSum
    fun_prop
  have hs : MeasurableSet {z : Fin n → ℝ | lowerScalarNormalizedSum z ≤ x} :=
    measurableSet_le hm measurable_const
  have hcols := lowerArrayLaw_map_columns B n p
  have hh := congrArg (fun μ : Measure (Fin p → Fin n → ℝ) =>
    μ.real (univ.pi (fun _ => {z | lowerScalarNormalizedSum z ≤ x}))) hcols
  change ((lowerArrayLaw B n p).map (fun z j i => z i j)).real
      (univ.pi (fun _ : Fin p => {z | lowerScalarNormalizedSum z ≤ x})) = _ at hh
  have htranspose : Measurable (fun z : Fin n → Vector p => fun j i => z i j) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)))
  rw [map_measureReal_apply htranspose (MeasurableSet.univ_pi (fun _ => hs))] at hh
  have heq : (fun z : Fin n → Vector p => fun j i => z i j) ⁻¹'
      (univ.pi (fun _ : Fin p => {z | lowerScalarNormalizedSum z ≤ x})) =
      {z | ∀ j, sumVector (lowerNormalizedRows (n := n) (p := p)) z j ≤ x} := by
    ext z
    simp only [mem_preimage, mem_pi, mem_univ, mem_setOf_eq, forall_const]
    apply forall_congr'
    intro j
    have he : lowerScalarNormalizedSum (fun i => z i j) =
        sumVector (lowerNormalizedRows (n := n) (p := p)) z j := by
      simp [sumVector, lowerNormalizedRows, lowerRawRows, lowerScalarNormalizedSum,
        Finset.sum_apply, Finset.sum_div, div_eq_mul_inv, mul_comm, Finset.mul_sum]
    rw [he]
  rw [heq] at hh
  dsimp only at hh
  simp only [Measure.real, Measure.pi_pi, ENNReal.toReal_prod] at hh
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    lowerCoordinateCDF, Measure.real] using hh

theorem standardGaussian_maximum_CDF (p : ℕ) (x : ℝ) :
    (standardGaussian p).real {z | ∀ j, z j ≤ x} = standardNormalCDF x ^ p := by
  have heq : {z : Vector p | ∀j,z j≤x}=univ.pi (fun _ : Fin p => Iic x) := by
    ext z
    simp only [mem_setOf_eq, mem_pi, mem_univ, mem_Iic, forall_const]
  rw [heq, standardGaussian, Measure.real, Measure.pi_pi, ENNReal.toReal_prod]
  simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin, standardNormalCDF, Measure.real]

theorem gaussianLaw_identity_maximum_CDF (p : ℕ) (x : ℝ) :
    (gaussianLaw (1 : Matrix (Fin p) (Fin p) ℝ)).real {z | ∀j,z j≤x} =
      standardNormalCDF x ^ p := by
  have heq : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec = id := by
    funext z
    exact Matrix.one_mulVec z
  unfold gaussianLaw
  rw [heq, Measure.map_id]
  exact standardGaussian_maximum_CDF p x


/-- A rectangle restricting only the first `q` coordinates. -/
def partialMaximumRectangle (p q : ℕ) (x : ℝ) : Rect p where
  interval j := if j.val<q then Iic x else univ
  ordConnected j := by
    split_ifs
    · exact ordConnected_Iic
    · exact ordConnected_univ
  measurable j := by split_ifs <;> measurability

theorem partialMaximumRectangle_carrier (p q : ℕ) (x : ℝ) :
    (partialMaximumRectangle p q x).carrier = {z | ∀j : Fin p,j.val<q → z j≤x} := by
  ext z
  simp only [Rect.carrier, partialMaximumRectangle, mem_pi, mem_univ, forall_const,
    mem_setOf_eq]
  apply forall_congr'
  intro j
  split_ifs with hj <;> simp [hj]

private theorem prod_first_coordinates {p q : ℕ} (hqp : q≤p) (a : ℝ) :
    (∏j : Fin p, if j.val<q then a else 1)=a^q := by
  classical
  rw [Finset.prod_ite]
  simp only [Finset.prod_const, Finset.prod_const_one, one_pow, mul_one]
  congr 1
  have hh := Fintype.card_fin_lt_of_le hqp
  rw [Fintype.card_subtype] at hh
  exact hh

theorem lowerArrayLaw_column_events (B : ℝ) (n p : ℕ)
    (s : Fin p → Set (Fin n → ℝ)) (hs : ∀j,MeasurableSet (s j)) :
    (lowerArrayLaw B n p).real {z | ∀j,(fun i => z i j)∈s j} =
      ∏j : Fin p,(lowerScalarArrayLaw B n).real (s j) := by
  have htranspose : Measurable (fun z : Fin n → Vector p => fun j i => z i j) :=
    measurable_pi_lambda _ (fun j => measurable_pi_lambda _ (fun i =>
      (measurable_pi_apply j).comp (measurable_pi_apply i)))
  have hh : (Measure.pi (fun _ : Fin p => lowerScalarArrayLaw B n)).real (univ.pi s)=
      ∏j : Fin p,(lowerScalarArrayLaw B n).real (s j) := by
    simp only [Measure.real,Measure.pi_pi,ENNReal.toReal_prod]
  rw [← lowerArrayLaw_map_columns B n p,
    map_measureReal_apply htranspose (MeasurableSet.univ_pi hs)] at hh
  have heq : (fun z : Fin n → Vector p => fun j i => z i j) ⁻¹' (univ.pi s) =
      {z | ∀j,(fun i => z i j)∈s j} := by
    ext z
    simp
  rw [heq] at hh
  exact hh

theorem lowerArrayLaw_partialMaximum_CDF (B : ℝ) (n : ℕ) {p q : ℕ}
    (hqp : q≤p) (x : ℝ) :
    (lowerArrayLaw B n p).real
      {z | ∀j : Fin p,j.val<q → sumVector (lowerNormalizedRows (n := n) (p := p)) z j≤x} =
      lowerCoordinateCDF B n x^q := by
  let s : Fin p → Set (Fin n → ℝ) :=
    fun j => if j.val<q then {z | lowerScalarNormalizedSum z≤x} else univ
  have hs : ∀j,MeasurableSet (s j) := by
    intro j
    dsimp [s]
    split_ifs
    · apply measurableSet_le _ measurable_const
      unfold lowerScalarNormalizedSum
      fun_prop
    · exact MeasurableSet.univ
  have hh := lowerArrayLaw_column_events B n p s hs
  have he : {z : Fin n → Vector p | ∀j,(fun i => z i j)∈s j} =
      {z | ∀j : Fin p,j.val<q → sumVector (lowerNormalizedRows (n := n) (p := p)) z j≤x} := by
    ext z
    simp only [mem_setOf_eq]
    apply forall_congr'
    intro j
    dsimp [s]
    split_ifs with hj
    · simp only [mem_setOf_eq,hj,true_implies]
      have heq : lowerScalarNormalizedSum (fun i => z i j) =
          sumVector (lowerNormalizedRows (n := n) (p := p)) z j := by
        simp [sumVector,lowerNormalizedRows,lowerRawRows,lowerScalarNormalizedSum,
          Finset.sum_apply,Finset.sum_div,div_eq_mul_inv,mul_comm,Finset.mul_sum]
      rw [heq]
    · simp [hj]
  rw [he] at hh
  rw [hh]
  have hi (j : Fin p) : (lowerScalarArrayLaw B n).real (s j)=
      if j.val<q then lowerCoordinateCDF B n x else 1 := by
    dsimp [s]
    split_ifs <;> simp [lowerCoordinateCDF]
  simp_rw [hi]
  exact prod_first_coordinates hqp _

theorem standardGaussian_partialMaximum_CDF {p q : ℕ} (hqp : q≤p) (x : ℝ) :
    (standardGaussian p).real {z | ∀j : Fin p,j.val<q → z j≤x} =
      standardNormalCDF x^q := by
  rw [← partialMaximumRectangle_carrier,Rect.carrier,standardGaussian]
  simp only [Measure.real,Measure.pi_pi,ENNReal.toReal_prod,partialMaximumRectangle]
  have hi (j : Fin p) :
      ((gaussianReal 0 1) (if j.val<q then Iic x else univ)).toReal =
        if j.val<q then standardNormalCDF x else 1 := by
    split_ifs <;> simp [standardNormalCDF,Measure.real]
  simp_rw [hi]
  exact prod_first_coordinates hqp _


def lowerCoordinateUpperTail (B : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  (lowerScalarArrayLaw B n).real {z | x<lowerScalarNormalizedSum z}

theorem lowerCoordinateCDF_eq_one_sub_upperTail (B : ℝ) (n : ℕ) (x : ℝ) :
    lowerCoordinateCDF B n x=1-lowerCoordinateUpperTail B n x := by
  have hs : MeasurableSet {z : Fin n → ℝ | lowerScalarNormalizedSum z≤x} := by
    apply measurableSet_le _ measurable_const
    unfold lowerScalarNormalizedSum
    fun_prop
  have heq : {z : Fin n → ℝ | x<lowerScalarNormalizedSum z}=
      {z | lowerScalarNormalizedSum z≤x}ᶜ := by ext z; simp
  rw [lowerCoordinateUpperTail,heq,measureReal_compl hs,measureReal_univ_eq_one]
  dsimp [lowerCoordinateCDF]
  ring

theorem lowerCoordinateUpperTail_eq_raw (B : ℝ) {n : ℕ} (hn : 1≤n) (x : ℝ) :
    lowerCoordinateUpperTail B n x=(lowerScalarArrayLaw B n).real
      {z | Real.sqrt (n:ℝ)*x < ∑i,z i} := by
  have hs : 0<Real.sqrt (n:ℝ) := Real.sqrt_pos.mpr (by exact_mod_cast hn)
  unfold lowerCoordinateUpperTail
  congr 1
  ext z
  simp only [mem_setOf_eq,lowerScalarNormalizedSum,lt_div_iff₀ hs,mul_comm x]

theorem gaussianLaw_identity_partialMaximum_CDF {p q : ℕ} (hqp : q≤p) (x : ℝ) :
    (gaussianLaw (1 : Matrix (Fin p) (Fin p) ℝ)).real
      {z | ∀j : Fin p,j.val<q → z j≤x}=standardNormalCDF x^q := by
  have heq : (1 : Matrix (Fin p) (Fin p) ℝ).mulVec=id := by
    funext z
    exact Matrix.one_mulVec z
  unfold gaussianLaw
  rw [heq,Measure.map_id]
  exact standardGaussian_partialMaximum_CDF hqp x

/-- Exact discrepancy on a genuine rectangle of the actual lower array. -/
theorem lowerArrayLaw_partialMaximum_rectangleError (B : ℝ) (n : ℕ) {p q : ℕ}
    (hqp : q≤p) (x : ℝ) :
    rectangleError (lowerArrayLaw B n p)
      (sumVector (lowerNormalizedRows (n := n) (p := p))) 1 (partialMaximumRectangle p q x)=
      |(1-lowerCoordinateUpperTail B n x)^q-standardNormalCDF x^q| := by
  unfold rectangleError
  rw [partialMaximumRectangle_carrier]
  change |(lowerArrayLaw B n p).real
    {z | ∀j : Fin p,j.val<q → sumVector (lowerNormalizedRows (n := n) (p := p)) z j≤x} -
    (gaussianLaw (1 : Matrix (Fin p) (Fin p) ℝ)).real
      {z | ∀j : Fin p,j.val<q → z j≤x}| = _
  rw [lowerArrayLaw_partialMaximum_CDF B n hqp x,
    gaussianLaw_identity_partialMaximum_CDF hqp x,lowerCoordinateCDF_eq_one_sub_upperTail]

end
end RectangleCLT.Companion
