import RectangleCLTCompanion.LowerProductArray

/-! The canonical observations in Theorem 4 really are iid with independent
coordinates, exact unit covariance, and an attained envelope. -/

open MeasureTheory ProbabilityTheory Set

namespace RectangleCLT.Companion

noncomputable section

lemma lowerRowLaw_attains_envelope {B : ℝ} (hB : 1 ≤ B) {p : ℕ} (hp : 1 ≤ p) :
    0 < (lowerRowLaw B p).real {x | ‖x‖ = B} := by
  let j : Fin p := ⟨0, by omega⟩
  have hBp : 0 < B := by linarith
  have hatom : (lowerRowLaw B p).real {x | x j = B} = (lowerTwoPointLaw B).real {B} := by
    rw [← lowerRowLaw_map_coordinate B j]
    have hh : ((lowerRowLaw B p).map (fun x : Vector p => x j)) {B} =
        (lowerRowLaw B p) ((fun x : Vector p => x j) ⁻¹' {B}) :=
      Measure.map_apply (measurable_pi_apply j) (measurableSet_singleton B)
    exact (congrArg ENNReal.toReal hh).symm
  have hfull : ({x : Vector p | x j = B} ∩ {x | ‖x‖ ≤ B} : Set (Vector p)) =ᵐ[lowerRowLaw B p]
      ({x | x j = B} : Set (Vector p)) := by
    filter_upwards [lowerRowLaw_bounded hB p] with x hx
    change (x j = B ∧ ‖x‖ ≤ B) = (x j = B)
    simp only [hx, and_true]
  have hsub : {x : Vector p | x j = B} ∩ {x | ‖x‖ ≤ B} ⊆ {x | ‖x‖ = B} := by
    intro x hx
    have hxj : x j = B := hx.1
    have hn : B ≤ ‖x‖ := by
      simpa only [Real.norm_eq_abs, hxj, abs_of_pos hBp] using norm_le_pi_norm x j
    exact le_antisymm hx.2 hn
  have hh := measureReal_mono (μ := lowerRowLaw B p) hsub
  rw [measureReal_congr hfull, hatom] at hh
  exact (lowerTwoPointLaw_attains_envelope hBp).trans_le hh

lemma lowerRawRows_attains_envelope {B : ℝ} (hB : 1 ≤ B) {n p : ℕ}
    (hp : 1 ≤ p) (i : Fin n) :
    0 < (lowerArrayLaw B n p).real {z | ‖lowerRawRows i z‖ = B} := by
  have hh := lowerRowLaw_attains_envelope hB hp
  rw [← lowerArrayLaw_map_row B i] at hh
  have hm : MeasurableSet {x : Vector p | ‖x‖ = B} := measurableSet_eq_fun measurable_norm measurable_const
  have hmi : Measurable (lowerRawRows (n := n) (p := p) i) := measurable_pi_apply i
  simpa only [Measure.real, Measure.map_apply hmi hm] using hh

lemma lowerRawRows_coordinate_map (B : ℝ) {n p : ℕ} (i : Fin n) (j : Fin p) :
    (lowerArrayLaw B n p).map (fun z => lowerRawRows i z j) = lowerTwoPointLaw B := by
  change (lowerArrayLaw B n p).map ((fun x : Vector p => x j) ∘ lowerRawRows i) = _
  rw [← Measure.map_map (measurable_pi_apply j) (show Measurable (lowerRawRows i) from measurable_pi_apply i),
    lowerArrayLaw_map_row B i, lowerRowLaw_map_coordinate B j]

lemma lowerRawRows_independent_coordinates (B : ℝ) {n p : ℕ} (i : Fin n) :
    iIndepFun (fun j (z : Fin n → Vector p) => lowerRawRows i z j) (lowerArrayLaw B n p) := by
  have hm (j : Fin p) : AEMeasurable (fun z : Fin n → Vector p => lowerRawRows i z j)
      (lowerArrayLaw B n p) :=
    ((measurable_pi_apply j).comp (measurable_pi_apply i)).aemeasurable
  apply (iIndepFun_iff_map_fun_eq_pi_map hm).mpr
  simp_rw [lowerRawRows_coordinate_map B i]
  exact lowerArrayLaw_map_row B i

lemma lowerRawRows_covariance {B : ℝ} (hB : 1 ≤ B) {n p : ℕ} (i : Fin n) :
    covariance (lowerArrayLaw B n p) (lowerRawRows i) = 1 := by
  have hdata := lowerRawRows_boundedIndependent hB n p
  have hBp : 0 < B := by linarith
  ext j k
  rw [covariance, hdata.centered i j, hdata.centered i k, mul_zero, sub_zero,
    lowerRawRows_second hBp.ne']
  exact Matrix.one_apply.symm

/-- All construction properties used by Theorem 4, for the genuine
finite product probability model. The iid law is itself a coordinate
product of the displayed two-point law. -/
structure LowerConstructionProperties (B : ℝ) (n p : ℕ) : Prop where
  data : BoundedIndependentHypotheses (lowerArrayLaw B n p) lowerRawRows B
  iid : ∀ i : Fin n, (lowerArrayLaw B n p).map (lowerRawRows i) =
    Measure.pi (fun _ : Fin p => lowerTwoPointLaw B)
  independent_coordinates : ∀ i : Fin n,
    iIndepFun (fun j (z : Fin n → Vector p) => lowerRawRows i z j) (lowerArrayLaw B n p)
  row_covariance : ∀ i : Fin n, covariance (lowerArrayLaw B n p) (lowerRawRows i) = 1
  attained : ∀ i : Fin n, 0 < (lowerArrayLaw B n p).real {z | ‖lowerRawRows i z‖ = B}
  normalized_covariance : covariance (lowerArrayLaw B n p)
    (sumVector (lowerNormalizedRows (n := n) (p := p))) = 1

theorem lowerConstructionProperties {B : ℝ} (hB : 1 ≤ B) {n p : ℕ}
    (hn : 1 ≤ n) (hp : 1 ≤ p) : LowerConstructionProperties B n p where
  data := lowerRawRows_boundedIndependent hB n p
  iid := lowerArrayLaw_map_row B
  independent_coordinates := lowerRawRows_independent_coordinates B
  row_covariance := lowerRawRows_covariance hB
  attained := lowerRawRows_attains_envelope hB hp
  normalized_covariance := lowerNormalizedRows_covariance hB hn

end

end RectangleCLT.Companion
