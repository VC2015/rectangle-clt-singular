import RectangleCLTCompanion.RectangleDistance
import RectangleCLTCompanion.SplitV4.RectangularGaussianLaw
import RectangleCLT.LocalCovariance

/-! Coordinate duplication preserves the full measurable rectangle distance.
Empty, unbounded, open and mixed intervals are all retained by finite
intersections. A repeated unit coordinate gives correlation gap zero. -/

open MeasureTheory Set
open scoped BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section

 def duplicateCoordinates {p q : ℕ} (r : Fin q → Fin p) (x : Vector p) : Vector q := x ∘ r

theorem measurable_duplicateCoordinates {p q : ℕ} (r : Fin q → Fin p) : Measurable (duplicateCoordinates r) :=
  measurable_pi_lambda _ (fun j => measurable_pi_apply (r j))

def rectangleDuplicationPreimage {p q : ℕ} (r : Fin q → Fin p) (R : Rect q) : Rect p where
  interval := fun j => ⋂ k : Fin q, ⋂ (_ : r k = j), R.interval k
  ordConnected := fun j => ordConnected_iInter (fun k => ordConnected_iInter (fun _ => R.ordConnected k))
  measurable := fun j => MeasurableSet.iInter (fun k => MeasurableSet.iInter (fun _ => R.measurable k))

def rectangleDuplicationLift {p q : ℕ} (r : Fin q → Fin p) (R : Rect p) : Rect q where
  interval := fun k => R.interval (r k)
  ordConnected := fun k => R.ordConnected (r k)
  measurable := fun k => R.measurable (r k)

theorem duplicateCoordinates_preimage_rectangle {p q : ℕ} (r : Fin q → Fin p) (R : Rect q) :
    duplicateCoordinates r ⁻¹' R.carrier = (rectangleDuplicationPreimage r R).carrier := by
  ext x
  simp only [mem_preimage, Rect.carrier, mem_pi, mem_univ, true_implies,
    rectangleDuplicationPreimage, mem_iInter, duplicateCoordinates, Function.comp_apply]
  constructor
  · intro h j k hkj
    simpa only [hkj] using h k
  · intro h k
    exact h (r k) k rfl

theorem duplicateCoordinates_preimage_lift {p q : ℕ} (r : Fin q → Fin p)
    (hr : Function.Surjective r) (R : Rect p) :
    duplicateCoordinates r ⁻¹' (rectangleDuplicationLift r R).carrier = R.carrier := by
  ext x
  simp only [mem_preimage, Rect.carrier, mem_pi, mem_univ, true_implies,
    rectangleDuplicationLift, duplicateCoordinates, Function.comp_apply]
  constructor
  · intro h j
    obtain ⟨k, hk⟩ := hr j
    simpa only [hk] using h k
  · intro h k
    exact h (r k)

theorem norm_duplicateCoordinates {p q : ℕ} (r : Fin q → Fin p)
    (hr : Function.Surjective r) (x : Vector p) : ‖duplicateCoordinates r x‖ = ‖x‖ := by
  apply le_antisymm
  · exact (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr (fun k => norm_le_pi_norm x (r k))
  · apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
    intro j
    obtain ⟨k, hk⟩ := hr j
    simpa only [duplicateCoordinates, Function.comp_apply, hk] using norm_le_pi_norm (duplicateCoordinates r x) k

/-- Exact full rectangle distance equality from the actual Gaussian image
law. Surjectivity ensures every original coordinate is retained. -/
theorem rectangleDistance_duplicateCoordinates {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (r : Fin q → Fin p) (hr : Function.Surjective r)
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin q) (Fin q) ℝ)
    (hG : gaussianLaw B = (gaussianLaw A).map (duplicateCoordinates r)) :
    rectangleDistance μ (duplicateCoordinates r ∘ W) B = rectangleDistance μ W A := by
  have herr (R : Rect q) : rectangleError μ (duplicateCoordinates r ∘ W) B R =
      rectangleError μ W A (rectangleDuplicationPreimage r R) := by
    unfold rectangleError
    rw [hG]
    have hg : ((gaussianLaw A).map (duplicateCoordinates r)).real R.carrier =
        (gaussianLaw A).real (duplicateCoordinates r ⁻¹' R.carrier) := by
      simp only [Measure.real, Measure.map_apply (measurable_duplicateCoordinates r) R.measurableSet_carrier]
    rw [hg, duplicateCoordinates_preimage_rectangle]
    have he : (duplicateCoordinates r ∘ W) ⁻¹' R.carrier =
        W ⁻¹' (rectangleDuplicationPreimage r R).carrier := by
      rw [Set.preimage_comp, duplicateCoordinates_preimage_rectangle]
    rw [he]
  apply le_antisymm
  · apply rectangleDistance_le
    intro R
    rw [herr]
    exact rectangleError_le_rectangleDistance μ W A _
  · apply rectangleDistance_le
    intro R
    have hh := rectangleError_le_rectangleDistance μ (duplicateCoordinates r ∘ W) B
      (rectangleDuplicationLift r R)
    have he : rectangleError μ (duplicateCoordinates r ∘ W) B (rectangleDuplicationLift r R) =
        rectangleError μ W A R := by
      unfold rectangleError
      rw [hG]
      have hg : ((gaussianLaw A).map (duplicateCoordinates r)).real (rectangleDuplicationLift r R).carrier =
          (gaussianLaw A).real R.carrier := by
        simp only [Measure.real, Measure.map_apply (measurable_duplicateCoordinates r)
          (rectangleDuplicationLift r R).measurableSet_carrier, duplicateCoordinates_preimage_lift r hr]
      rw [hg]
      have he' : (duplicateCoordinates r ∘ W) ⁻¹' (rectangleDuplicationLift r R).carrier = W ⁻¹' R.carrier := by
        rw [Set.preimage_comp, duplicateCoordinates_preimage_lift r hr]
      rw [he']
    rwa [he] at hh

theorem gaussianLaw_duplicateCoordinates {p q : ℕ} (r : Fin q → Fin p)
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin q) (Fin q) ℝ)
    (hcov : B*B.transpose = fun j k => (A*A.transpose) (r j) (r k)) :
    gaussianLaw B = (gaussianLaw A).map (duplicateCoordinates r) := by
  let C : Matrix (Fin q) (Fin p) ℝ := fun j k => A (r j) k
  have hc : C*C.transpose = B*B.transpose := by
    rw [hcov]
    ext j k
    rfl
  have hl := rectangularGaussianLaw_eq_gaussianLaw C B hc
  rw [← hl]
  unfold rectangularGaussianLaw gaussianLaw
  rw [Measure.map_map (measurable_duplicateCoordinates r) (measurable_mulVec A)]
  rfl

theorem rectangleDistance_duplicateCoordinates_of_covariance {Ω : Type*} [MeasurableSpace Ω]
    {p q : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ] (W : Ω → Vector p)
    (r : Fin q → Fin p) (hr : Function.Surjective r)
    (A : Matrix (Fin p) (Fin p) ℝ) (B : Matrix (Fin q) (Fin q) ℝ)
    (hcov : B*B.transpose = fun j k => (A*A.transpose) (r j) (r k)) :
    rectangleDistance μ (duplicateCoordinates r ∘ W) B = rectangleDistance μ W A :=
  rectangleDistance_duplicateCoordinates μ W r hr A B (gaussianLaw_duplicateCoordinates r A B hcov)

theorem duplicateCoordinates_covariance {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (μ : Measure Ω) (W : Ω → Vector p) (r : Fin q → Fin p) :
    covariance μ (duplicateCoordinates r ∘ W) = fun j k => covariance μ W (r j) (r k) := rfl

theorem pairGap_duplicateCoordinates_zero {p q : ℕ} (Q : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, Q j j = 1) (habs : ∀ j k, |Q j k| ≤ 1)
    (r : Fin q → Fin p) {j k : Fin q} (hjk : j ≠ k) (hrjk : r j = r k) :
    pairGap (fun a b => Q (r a) (r b)) = 0 := by
  classical
  have hm : maxOffDiagonal (fun a b => Q (r a) (r b)) = 1 := by
    apply le_antisymm
    · apply (Finset.fold_max_le _).mpr
      refine ⟨by norm_num, ?_⟩
      intro ab _
      split_ifs with hab
      · norm_num
      · exact habs _ _
    · apply (Finset.le_fold_max _).mpr
      refine Or.inr ⟨(j,k), Finset.mem_univ _, ?_⟩
      simp [hjk, hrjk, hdiag]
  rw [pairGap, hm, sub_self]

/-- The standard padding map retains the first p coordinates and copies
coordinate zero into every added position. -/
def coordinatePaddingMap {p q : ℕ} (hp : 1 ≤ p) (j : Fin q) : Fin p :=
  if h : j.val < p then ⟨j.val,h⟩ else ⟨0,by omega⟩

theorem coordinatePaddingMap_surjective {p q : ℕ} (hp : 1 ≤ p) (hpq : p ≤ q) :
    Function.Surjective (coordinatePaddingMap (q := q) hp) := by
  intro j
  refine ⟨⟨j.val, lt_of_lt_of_le j.isLt hpq⟩, ?_⟩
  simp only [coordinatePaddingMap, dif_pos j.isLt]

theorem coordinatePadding_pairGap_zero {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q)
    (Q : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, Q j j = 1) (habs : ∀ j k, |Q j k| ≤ 1) :
    pairGap (fun j k => Q (coordinatePaddingMap (q := q) hp j) (coordinatePaddingMap hp k)) = 0 := by
  let j : Fin q := ⟨0, by omega⟩
  let k : Fin q := ⟨p, hpq⟩
  have hjk : j ≠ k := by
    intro hh
    have hv := congrArg Fin.val hh
    dsimp [j,k] at hv
    omega
  apply pairGap_duplicateCoordinates_zero Q hdiag habs (coordinatePaddingMap hp) hjk
  simp [j,k,coordinatePaddingMap, Nat.pos_of_ne_zero (by omega : p ≠ 0)]

theorem gram_abs_entry_le_one {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A*A.transpose) j j = 1) (j k : Fin p) : |(A*A.transpose) j k| ≤ 1 := by
  have hj : ∑ l, A j l^2 = 1 := by simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag j
  have hk : ∑ l, A k l^2 = 1 := by simpa [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hdiag k
  have hplus : 0 ≤ ∑ l, (A j l+A k l)^2 := Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have hminus : 0 ≤ ∑ l, (A j l-A k l)^2 := Finset.sum_nonneg (fun l _ => sq_nonneg _)
  have hp : (∑ l, (A j l+A k l)^2) = 2+2*(∑ l, A j l*A k l) := by
    simp_rw [add_sq]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, hj,hk]
    have he : (∑ l, 2*A j l*A k l) = 2*(∑ l, A j l*A k l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  have hm : (∑ l, (A j l-A k l)^2) = 2-2*(∑ l, A j l*A k l) := by
    simp_rw [sub_sq]
    rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, hj,hk]
    have he : (∑ l, 2*A j l*A k l) = 2*(∑ l, A j l*A k l) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro l _
      ring
    rw [he]
    ring
  rw [hp] at hplus
  rw [hm] at hminus
  simp only [Matrix.mul_apply, Matrix.transpose_apply]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem coordinatePadding_pairGap_zero_of_unit_gram {p q : ℕ} (hp : 1 ≤ p) (hpq : p < q)
    (A : Matrix (Fin p) (Fin p) ℝ) (hdiag : ∀ j, (A*A.transpose) j j = 1) :
    pairGap (fun j k => (A*A.transpose) (coordinatePaddingMap (q := q) hp j) (coordinatePaddingMap hp k)) = 0 :=
  coordinatePadding_pairGap_zero hp hpq _ hdiag (gram_abs_entry_le_one A hdiag)

theorem sumVector_duplicateCoordinates {Ω : Type*} {p q n : ℕ}
    (ξ : Fin n → Ω → Vector p) (r : Fin q → Fin p) (ω : Ω) :
    sumVector (fun i ω => duplicateCoordinates r (ξ i ω)) ω = duplicateCoordinates r (sumVector ξ ω) := by
  ext j
  simp [sumVector,duplicateCoordinates,Finset.sum_apply]

end
end RectangleCLT.Companion.SplitV4
