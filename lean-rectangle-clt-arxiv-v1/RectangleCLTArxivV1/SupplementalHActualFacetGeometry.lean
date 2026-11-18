import RectangleCLTArxivV1.SupplementalHResidualGreen

/-! Actual facets have witnesses when their inequality is removed.
Together with a strict interior point, these witnesses exclude consistent
affine dependencies among two or three distinct facet inequalities. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

def HasStrictFacetInterior {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∃ x : Vector r,∀ j,faceDot (u j) x<b j

def HasIrredundantFacetWitnesses {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : Prop :=
  ∀ j,∃ x : Vector r,(∀ k,k≠j → faceDot (u k) x≤b k) ∧ b j<faceDot (u j) x

theorem actualFacet_pair_affine_inconsistent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) (hwitness : HasIrredundantFacetWitnesses u b)
    (j k : Fin m) (hkj : k≠j) (a : ℝ) (hnormal : u k=a • u j) :
    b k≠a*b j := by
  intro hb
  have hd (x : Vector r) : b k-faceDot (u k) x=a*(b j-faceDot (u j) x) := by
    rw [hnormal,threshold_faceDot_smul_left,hb]
    ring
  obtain ⟨x,hx⟩ := hinterior
  have ha : 0<a := by
    have hk : 0<b k-faceDot (u k) x := sub_pos.mpr (hx k)
    rw [hd] at hk
    exact (mul_pos_iff.mp hk).resolve_right (fun h => (not_lt_of_ge (sub_pos.mpr (hx j)).le) h.2) |>.1
  obtain ⟨y,hy,hyj⟩ := hwitness k
  have hj : 0≤b j-faceDot (u j) y := sub_nonneg.mpr (hy j (Ne.symm hkj))
  have hk : b k-faceDot (u k) y<0 := sub_neg.mpr hyj
  rw [hd] at hk
  exact (not_lt_of_ge (mul_nonneg ha.le hj)) hk

theorem actualFacet_triple_affine_inconsistent {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (hinterior : HasStrictFacetInterior u b) (hwitness : HasIrredundantFacetWitnesses u b)
    (j k l : Fin m) (hjk : j≠k) (hlj : l≠j) (hlk : l≠k) (a c : ℝ)
    (hnormal : u l=a • u j+c • u k) : b l≠a*b j+c*b k := by
  intro hb
  have hd (x : Vector r) : b l-faceDot (u l) x=
      a*(b j-faceDot (u j) x)+c*(b k-faceDot (u k) x) := by
    rw [hnormal,gaussianPair_faceDot_add_left,threshold_faceDot_smul_left,
      threshold_faceDot_smul_left,hb]
    ring
  by_cases ha : 0≤a
  · by_cases hc : 0≤c
    · obtain ⟨x,hx,hxl⟩ := hwitness l
      have hj := sub_nonneg.mpr (hx j (Ne.symm hlj))
      have hk := sub_nonneg.mpr (hx k (Ne.symm hlk))
      have hh := add_nonneg (mul_nonneg ha hj) (mul_nonneg hc hk)
      rw [← hd] at hh
      exact (not_lt_of_ge hh) (sub_neg.mpr hxl)
    · have hc' : c<0 := lt_of_not_ge hc
      by_cases hap : 0<a
      · obtain ⟨x,hx,hxj⟩ := hwitness j
        have hj : b j-faceDot (u j) x<0 := sub_neg.mpr hxj
        have hk : 0≤b k-faceDot (u k) x := sub_nonneg.mpr (hx k (Ne.symm hjk))
        have hl : 0≤b l-faceDot (u l) x := sub_nonneg.mpr (hx l hlj)
        have hneg := add_neg_of_neg_of_nonpos (mul_neg_of_pos_of_neg hap hj)
          (mul_nonpos_of_nonpos_of_nonneg hc'.le hk)
        rw [← hd] at hneg
        exact (not_lt_of_ge hl) hneg
      · obtain ⟨x,hx⟩ := hinterior
        have hnon := add_nonpos
          (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hap) (sub_pos.mpr (hx j)).le)
          (mul_nonpos_of_nonpos_of_nonneg hc'.le (sub_pos.mpr (hx k)).le)
        rw [← hd] at hnon
        exact (not_lt_of_ge hnon) (sub_pos.mpr (hx l))
  · have ha' : a<0 := lt_of_not_ge ha
    by_cases hcp : 0<c
    · obtain ⟨x,hx,hxk⟩ := hwitness k
      have hj : 0≤b j-faceDot (u j) x := sub_nonneg.mpr (hx j hjk)
      have hk : b k-faceDot (u k) x<0 := sub_neg.mpr hxk
      have hl : 0≤b l-faceDot (u l) x := sub_nonneg.mpr (hx l hlk)
      have hneg := add_neg_of_nonpos_of_neg (mul_nonpos_of_nonpos_of_nonneg ha'.le hj)
        (mul_neg_of_pos_of_neg hcp hk)
      rw [← hd] at hneg
      exact (not_lt_of_ge hl) hneg
    · obtain ⟨x,hx⟩ := hinterior
      have hnon := add_nonpos
        (mul_nonpos_of_nonpos_of_nonneg ha'.le (sub_pos.mpr (hx j)).le)
        (mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt hcp) (sub_pos.mpr (hx k)).le)
      rw [← hd] at hnon
      exact (not_lt_of_ge hnon) (sub_pos.mpr (hx l))

end
end RectangleCLTArxivV1
