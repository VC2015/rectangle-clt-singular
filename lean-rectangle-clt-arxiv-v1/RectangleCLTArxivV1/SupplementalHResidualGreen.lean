import RectangleCLTArxivV1.SupplementalHGenericThreshold
import RectangleCLTArxivV1.SupplementalHLocalFiniteThreshold
import RectangleCLTArxivV1.SupplementalHSectionTrace
import RectangleCLTArxivV1.SupplementalHHardFacetGreen

/-! Actual hard-facet Green identity at generic affine thresholds. The
normals may be dependent and may contain opposite signed faces. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def ResidualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j : Fin m) : Prop :=
  LocalFiniteThresholdRegularity (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j))

/-- The finite first derivative in the actual residual hard-polyhedron
law, multiplied by the exact scalar normal Gaussian density. -/
def hardFacetResidualDensity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  gaussianPDFReal 0 1 (b j)*gaussianFiniteThresholdFirst (Finset.univ.erase j)
    (fun k => gaussianNormalProjection (u j) (u k))
    (fun k => b k-b j*faceDot (u k) (u j)) l

/-- Every hard facet has the genuine signed Green formula under ordinary
local affine slack. No whole-family independence is assumed. -/
theorem hardGaussianFacet_Green_residual_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hreg : ResidualThresholdRegularity u b j) :
    hardGaussianFacetIntegral u b j=
      (b j^2-1)*gaussianThresholdFirst u b j-
      ∑ l∈Finset.univ.erase j,
        (b l-faceDot (u j) (u l)*b j)*hardFacetResidualDensity u b j l := by
  have hfirst := gaussianThresholdFirst_eq_section_of_slack u b j hu
    (fun l hlj => (hreg l (Finset.mem_erase.mpr ⟨hlj,Finset.mem_univ _⟩)).1)
  rw [hardGaussianFacetIntegral_eq_signedSection u b j hu,
    thresholdSignedSection_eq_residual_trace u b j hu (b j)]
  have ht := gaussianFiniteThreshold_radialTrace_retained_of_slack
    (Finset.univ.erase j) (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j)) hreg
  change gaussianFiniteThresholdRadialTrace (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l => b l-b j*faceDot (u l) (u j))=_ at ht
  rw [ht,hfirst,mul_add,mul_neg,Finset.mul_sum]
  have hs : (∑ l∈Finset.univ.erase j,
      gaussianPDFReal 0 1 (b j)*((b l-b j*faceDot (u l) (u j))*
        gaussianFiniteThresholdFirst (Finset.univ.erase j)
          (fun k => gaussianNormalProjection (u j) (u k))
          (fun k => b k-b j*faceDot (u k) (u j)) l))=
      ∑ l∈Finset.univ.erase j,
        (b l-faceDot (u j) (u l)*b j)*hardFacetResidualDensity u b j l := by
    apply Finset.sum_congr rfl
    intro l _
    rw [faceDot_comm (u l) (u j)]
    unfold hardFacetResidualDensity
    ring
  rw [hs]
  ring

/-- The ordinary local residual slack condition holds simultaneously on
all facets for almost every threshold, for every fixed normal family. -/
theorem ae_residualThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume, ∀ j, ResidualThresholdRegularity u b j := by
  let V := fun j l => gaussianNormalProjection (u j) (u l)
  let B := fun j k l => faceDot (V j l) (localFiniteThresholdDirection (V j) k)/
    localFiniteThresholdScale (V j) k
  let A := fun j k l => faceDot (u l) (u j)-B j k l*faceDot (u k) (u j)
  have hp := ae_threshold_all_two_coordinate_combinations
    (fun j _ l => faceDot (u l) (u j)) (fun _ _ _ => 0)
  have ht := ae_threshold_all_two_coordinate_combinations A B
  filter_upwards [hp,ht] with b hb htriple
  intro j k hk
  have hkj : k≠j := (Finset.mem_erase.mp hk).1
  refine ⟨Or.inr ?_, ?_⟩
  · change b k-b j*faceDot (u k) (u j)≠0
    simpa only [zero_mul,mul_zero,sub_zero,mul_comm] using hb j j k hkj hkj
  · intro l hl
    have hlk : l≠k := (Finset.mem_erase.mp hl).1
    have hlj : l≠j := (Finset.mem_erase.mp (Finset.mem_erase.mp hl).2).1
    refine Or.inr ?_
    have h := htriple j k l hlj hlk
    have he : b l-b j*faceDot (u l) (u j)-
        ((b k-b j*faceDot (u k) (u j))/localFiniteThresholdScale (V j) k)*
          faceDot (V j l) (localFiniteThresholdDirection (V j) k)=
        b l-A j k l*b j-B j k l*b k := by
      dsimp only [A,B]
      simp only [div_eq_mul_inv]
      ring
    change b l-b j*faceDot (u l) (u j)-
        ((b k-b j*faceDot (u k) (u j))/localFiniteThresholdScale (V j) k)*
          faceDot (V j l) (localFiniteThresholdDirection (V j) k)≠0
    rwa [he]

/-- The hard-facet signed Green formula holds at almost every threshold
for arbitrary fixed dependent unit normals, including signed pairs. -/
theorem ae_hardGaussianFacet_Green_residual {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume, ∀ j,
      hardGaussianFacetIntegral u b j=
        (b j^2-1)*gaussianThresholdFirst u b j-
        ∑ l∈Finset.univ.erase j,
          (b l-faceDot (u j) (u l)*b j)*hardFacetResidualDensity u b j l := by
  filter_upwards [ae_residualThresholdRegularity u] with b hb
  exact fun j => hardGaussianFacet_Green_residual_of_slack u b j (hu j) (hb j)

end
end RectangleCLTArxivV1
