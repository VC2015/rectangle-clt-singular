import RectangleCLTArxivV1.SupplementalHActualFacetSelection

/-! One fixed actual facet selection works under every translation and
positive rescaling. Its strict-interior and deletion witnesses are
transported explicitly, rather than chosen again for each sampled base. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000

theorem actualFacet_affine_faceDot {r : ℕ} (u x y : Vector r) (σ : ℝ) :
    faceDot u (σ⁻¹ • (y-x))=(faceDot u y-faceDot u x)/σ := by
  rw [threshold_faceDot_smul_right,threshold_faceDot_sub_right]
  rw [div_eq_mul_inv,mul_comm]

theorem HasStrictFacetInterior.affine {m r : ℕ} {u : Fin m → Vector r} {b : Vector m}
    (h : HasStrictFacetInterior u b) (x : Vector r) {σ : ℝ} (hσ : 0<σ) :
    HasStrictFacetInterior u (fun k => (b k-faceDot (u k) x)/σ) := by
  obtain ⟨y,hy⟩ := h
  refine ⟨σ⁻¹ • (y-x),fun k => ?_⟩
  rw [actualFacet_affine_faceDot _ _ _ σ]
  exact (div_lt_div_iff_of_pos_right hσ).mpr (sub_lt_sub_right (hy k) _)

theorem HasIrredundantFacetWitnesses.affine {m r : ℕ} {u : Fin m → Vector r} {b : Vector m}
    (h : HasIrredundantFacetWitnesses u b) (x : Vector r) {σ : ℝ} (hσ : 0<σ) :
    HasIrredundantFacetWitnesses u (fun k => (b k-faceDot (u k) x)/σ) := by
  intro j
  obtain ⟨y,hy,hyj⟩ := h j
  refine ⟨σ⁻¹ • (y-x),?_,?_⟩
  · intro k hkj
    rw [actualFacet_affine_faceDot _ _ _ σ]
    exact (div_le_div_iff_of_pos_right hσ).mpr (sub_le_sub_right (hy k hkj) _)
  · rw [actualFacet_affine_faceDot _ _ _ σ]
    exact (div_lt_div_iff_of_pos_right hσ).mpr (sub_lt_sub_right hyj _)

theorem actualFacet_presentation_equivalence_affine {m q r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e : Fin q → Fin m)
    (hequiv : ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤b (e i)) ↔ ∀ k,faceDot (u k) y≤b k)
    (x : Vector r) {σ : ℝ} (hσ : 0<σ) :
    ∀ y : Vector r,(∀ i,faceDot (u (e i)) y≤(b (e i)-faceDot (u (e i)) x)/σ) ↔
      ∀ k,faceDot (u k) y≤(b k-faceDot (u k) x)/σ := by
  intro y
  have hc (k : Fin m) : faceDot (u k) y≤(b k-faceDot (u k) x)/σ ↔
      faceDot (u k) (x+σ • y)≤b k := by
    rw [le_div_iff₀ hσ,threshold_faceDot_add_right,threshold_faceDot_smul_right]
    constructor <;> intro h <;> nlinarith
  simp only [hc]
  exact hequiv (x+σ • y)

theorem actualFacet_residualThresholdRegularity_affine {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (hinterior : HasStrictFacetInterior u b)
    (hwitness : HasIrredundantFacetWitnesses u b) (x : Vector r) {σ : ℝ} (hσ : 0<σ) :
    ∀ j,ResidualThresholdRegularity u (fun k => (b k-faceDot (u k) x)/σ) j :=
  actualFacet_residualThresholdRegularity u _ (hinterior.affine x hσ) (hwitness.affine x hσ)

end
end RectangleCLTArxivV1
