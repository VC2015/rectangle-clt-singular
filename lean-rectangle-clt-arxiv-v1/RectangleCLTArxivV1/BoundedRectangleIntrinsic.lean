import RectangleCLTArxivV1.ActiveFaceCoordinates
import RectangleCLTArxivV1.IntrinsicBoundedConcentration

namespace RectangleCLTArxivV1

open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators

noncomputable def activeObservations {Ω : Type*} {p n : ℕ} (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (i : Fin n) (ω : Ω) : Vector s.faces.card :=
  activeFaceProjection s (ξ i ω)

theorem sum_activeObservations {Ω : Type*} {p n : ℕ} (s : FaceSmoother p)
    (ξ : Fin n → Ω → Vector p) (ω : Ω) :
    sumVector (activeObservations s ξ) ω = activeFaceProjection s (sumVector ξ ω) :=
  (activeFaceProjection_sum s (fun i => ξ i ω)).symm

theorem activeObservations_bounded {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {δ : ℝ}
    (h : BoundedIndependentHypotheses μ ξ δ) (s : FaceSmoother p) :
    BoundedIndependentHypotheses μ (activeObservations s ξ) δ := by
  refine ⟨fun i => (measurable_activeFaceProjection s).comp (h.measurable i),
    h.independent.comp (fun _ => activeFaceProjection s) (fun _ => measurable_activeFaceProjection s),
    ?_, ?_, h.delta_nonneg⟩
  · intro i j
    dsimp [activeObservations, activeFaceProjection, FaceSmoother.normalDot]
    split_ifs
    · exact h.centered i _
    · simpa [integral_neg] using congrArg Neg.neg (h.centered i (activeFaceEquiv s j).1.1)
  · intro i
    filter_upwards [h.bounded i] with ω hω
    exact (activeFaceProjection_norm_le s _).trans hω

theorem activeObservations_covariance_diagonal {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p) (s : FaceSmoother p) {v : ℝ}
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v) (j : Fin s.faces.card) :
    covariance μ (sumVector (activeObservations s ξ)) j j = v := by
  have hsum : sumVector (activeObservations s ξ) =
      (fun ω => activeFaceProjection s (sumVector ξ ω)) := funext (sum_activeObservations s ξ)
  rw [hsum]
  dsimp [covariance, activeFaceProjection, FaceSmoother.normalDot]
  split_ifs
  · exact hdiag _
  · simpa only [covariance, neg_mul_neg, integral_neg] using hdiag (activeFaceEquiv s j).1.1

/-- The intrinsic bounded layer estimate applies to every archived rectangle
smoother, including arbitrary independent shifts and an empty face list. -/
theorem boundedRectangleBoundary_product_intrinsic
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ v : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (s : FaceSmoother p) {d : ℝ} (hd : 0 ≤ d) :
    (μ.prod ν).real {z | sumVector ξ z.1 + R z.2 ∈ s.boundaryLayer d} ≤
      64 * ((d+δ)/v * ∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
  by_cases hfaces : s.faces = ∅
  · rw [boundaryLayer_empty_of_faces_empty s hfaces]
    simp only [Set.mem_empty_iff_false, Set.setOf_false, measureReal_empty]
    exact mul_nonneg (by norm_num) (mul_nonneg
      (div_nonneg (add_nonneg hd h.delta_nonneg) hv.le)
      (integral_nonneg (fun ω => norm_nonneg _)))
  · letI : NeZero s.faces.card := ⟨by simpa using hfaces⟩
    have hproj := activeObservations_bounded h s
    have hh := coordinateLayer_product_printed μ (activeObservations s ξ) hproj hv
      (activeObservations_covariance_diagonal μ ξ s hdiag) ν (fun z => activeFaceProjection s (R z))
      ((measurable_activeFaceProjection s).comp hR) (activeFaceOffsets s) hd
    have hevent : {z : Ω × Γ | sumVector ξ z.1 + R z.2 ∈ s.boundaryLayer d} =
        {z | ((∑ i, activeObservations s ξ i z.1) + activeFaceProjection s (R z.2)) ∈
          projectedFaceLayer (activeFaceOffsets s) d} := by
      ext z
      simp only [Set.mem_setOf_eq]
      rw [mem_boundaryLayer_iff_activeProjected, activeFaceProjection_add]
      change _ ↔ sumVector (activeObservations s ξ) z.1 + _ ∈ _
      rw [sum_activeObservations]
    rw [hevent]
    have hmean : (∫ ω, ‖∑ i, activeObservations s ξ i ω‖ ∂μ) ≤
        ∫ ω, ‖sumVector ξ ω‖ ∂μ := by
      apply integral_mono hproj.integrable_norm_sum h.integrable_norm_sum
      intro ω
      change ‖sumVector (activeObservations s ξ) ω‖ ≤ _
      rw [sum_activeObservations]
      exact activeFaceProjection_norm_le s _
    exact hh.trans (mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_left hmean (div_nonneg (add_nonneg hd h.delta_nonneg) hv.le)) (by norm_num))

/-- Independent noise may be retained in the actual vector law. -/
theorem boundedRectangleBoundary_map_product_intrinsic
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ v : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    ((μ.prod ν).map (fun q : Ω × Γ => sumVector ξ q.1 + R q.2)).real
      {x | x+z ∈ s.boundaryLayer d} ≤
        64 * ((d+δ)/v * ∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
  have hV : Measurable (fun q : Ω × Γ => sumVector ξ q.1 + R q.2) :=
    (h.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd)
  have hE : MeasurableSet {x : Vector p | x+z ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
  rw [Measure.real, Measure.map_apply hV hE]
  change (μ.prod ν).real {q | (sumVector ξ q.1 + R q.2)+z ∈ s.boundaryLayer d} ≤ _
  simpa only [add_assoc] using boundedRectangleBoundary_product_intrinsic μ ξ h hv hdiag ν
    (fun q => R q+z) (hR.add_const z) s hd.le

theorem boundedRectangleBoundary_map_intrinsic
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ v : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    (μ.map (sumVector ξ)).real {x | x+z ∈ s.boundaryLayer d} ≤
      64 * ((d+δ)/v * ∫ ω, ‖sumVector ξ ω‖ ∂μ) := by
  have hh := boundedRectangleBoundary_product_intrinsic μ ξ h hv hdiag μ
    (fun _ => z) measurable_const s hd.le
  have he : (μ.prod μ) {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d} =
      μ {ω | sumVector ξ ω+z ∈ s.boundaryLayer d} := by
    have heS : {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d} =
        {ω | sumVector ξ ω+z ∈ s.boundaryLayer d} ×ˢ Set.univ := by ext q; simp
    rw [heS, Measure.prod_prod]
    simp
  have hE : MeasurableSet {x : Vector p | x+z ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
  rw [Measure.real, Measure.map_apply h.measurable_sum hE]
  change (μ {ω | sumVector ξ ω+z ∈ s.boundaryLayer d}).toReal ≤ _
  change ((μ.prod μ) {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d}).toReal ≤ _ at hh
  rwa [he] at hh

/-- The logarithmic alternative is obtained from the scalar MGF maximum
bound and the printed intrinsic estimate, splitting on the envelope scale. -/
theorem boundedRectangleBoundary_product_logarithmic
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} (hp : 1 ≤ p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {η v : ℝ} (h : BoundedIndependentHypotheses μ ξ η)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (a : FaceSmoother p) {s : ℝ} (hs : 0 ≤ s) :
    (μ.prod ν).real {z | sumVector ξ z.1 + R z.2 ∈ a.boundaryLayer s} ≤
      256 * ((s + η) * Real.sqrt (dimensionLog p / v)) := by
  have hη : 0 ≤ η := h.delta_nonneg
  have hL : 0 ≤ dimensionLog p := zero_le_one.trans (log_exp_mul_nat_ge_one hp)
  let q := Real.sqrt (dimensionLog p / v)
  have hq : 0 ≤ q := Real.sqrt_nonneg _
  have hsη : 0 ≤ s + η := add_nonneg hs hη
  have hqq : q ^ 2 = dimensionLog p / v := Real.sq_sqrt (div_nonneg hL hv.le)
  have hLq : dimensionLog p = v * q ^ 2 := by
    apply (eq_div_iff (ne_of_gt hv)).mp at hqq
    nlinarith [hqq]
  have hsq : Real.sqrt v * Real.sqrt (dimensionLog p) = v * q := by
    have hsq₀ : Real.sqrt (dimensionLog p) = Real.sqrt v * q := by
      dsimp [q]
      rw [Real.sqrt_div hL]
      field_simp
    rw [hsq₀]
    nlinarith [Real.sq_sqrt hv.le]
  by_cases hsmall : η * q ≤ 1
  · have hnorm := h.integral_norm_sum_le_of_variance hp hv hdiag
    change (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ _ at hnorm
    have hbudget : (∫ ω, ‖∑ i, ξ i ω‖ ∂μ) ≤ 4 * v * q := by
      rw [show 2 * Real.sqrt v * Real.sqrt (dimensionLog p) =
        2 * (Real.sqrt v * Real.sqrt (dimensionLog p)) by ring, hsq, hLq] at hnorm
      have hm := mul_le_mul_of_nonneg_right hsmall (mul_nonneg hv.le hq)
      nlinarith
    have hbase := boundedRectangleBoundary_product_intrinsic μ ξ h hv hdiag ν R hR a hs
    apply hbase.trans
    calc
      _ ≤ 64 * ((s + η) / v * (4 * v * q)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbudget (div_nonneg hsη hv.le)) (by norm_num)
      _ = _ := by dsimp [q]; field_simp [ne_of_gt hv]; ring
  · have hlarge : 1 < (s + η) * q := by nlinarith [lt_of_not_ge hsmall]
    exact (measureReal_le_one (μ := μ.prod ν)).trans (by dsimp [q] at *; nlinarith)


theorem boundedRectangleBoundary_map_product_logarithmic
    {Ω Γ : Type*} [MeasurableSpace Ω] [MeasurableSpace Γ]
    {p n : ℕ} (hp : 1 ≤ p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ v : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (ν : Measure Γ) [IsProbabilityMeasure ν] (R : Γ → Vector p) (hR : Measurable R)
    (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    ((μ.prod ν).map (fun q : Ω × Γ => sumVector ξ q.1 + R q.2)).real
      {x | x+z ∈ s.boundaryLayer d} ≤
        256 * ((d+δ)*Real.sqrt (dimensionLog p / v)) := by
  have hV : Measurable (fun q : Ω × Γ => sumVector ξ q.1 + R q.2) :=
    (h.measurable_sum.comp measurable_fst).add (hR.comp measurable_snd)
  have hE : MeasurableSet {x : Vector p | x+z ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
  rw [Measure.real, Measure.map_apply hV hE]
  change (μ.prod ν).real {q | (sumVector ξ q.1 + R q.2)+z ∈ s.boundaryLayer d} ≤ _
  simpa only [add_assoc] using boundedRectangleBoundary_product_logarithmic hp μ ξ h hv hdiag ν
    (fun q => R q+z) (hR.add_const z) s hd.le
theorem boundedRectangleBoundary_map_logarithmic
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ} (hp : 1 ≤ p)
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) {δ v : ℝ} (h : BoundedIndependentHypotheses μ ξ δ)
    (hv : 0 < v) (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (s : FaceSmoother p) (z : Vector p) {d : ℝ} (hd : 0 < d) :
    (μ.map (sumVector ξ)).real {x | x+z ∈ s.boundaryLayer d} ≤
      256 * ((d+δ)*Real.sqrt (dimensionLog p/v)) := by
  have hh := boundedRectangleBoundary_product_logarithmic hp μ ξ h hv hdiag μ
    (fun _ => z) measurable_const s hd.le
  have he : (μ.prod μ) {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d} =
      μ {ω | sumVector ξ ω+z ∈ s.boundaryLayer d} := by
    have heS : {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d} =
        {ω | sumVector ξ ω+z ∈ s.boundaryLayer d} ×ˢ Set.univ := by ext q; simp
    rw [heS, Measure.prod_prod]
    simp
  have hE : MeasurableSet {x : Vector p | x+z ∈ s.boundaryLayer d} :=
    (s.measurableSet_boundaryLayer d).preimage (measurable_id.add_const z)
  rw [Measure.real, Measure.map_apply h.measurable_sum hE]
  change (μ {ω | sumVector ξ ω+z ∈ s.boundaryLayer d}).toReal ≤ _
  change ((μ.prod μ) {q : Ω × Ω | sumVector ξ q.1+z ∈ s.boundaryLayer d}).toReal ≤ _ at hh
  rwa [he] at hh


end RectangleCLTArxivV1
