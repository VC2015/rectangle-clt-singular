import RectangleCLTArxivV1.SupplementalHResidualGreen
import RectangleCLTArxivV1.SupplementalHResidualPairMass

/-! Finite signed pairing for the actual hard-facet Green formula.
The two conormal contributions are combined before taking absolute values. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

theorem sum_erase_eq_full_sub_diagonal {m : ℕ} (A : Fin m → Fin m → ℝ) :
    (∑ j, ∑ l∈Finset.univ.erase j, A j l)=(∑ j, ∑ l, A j l)-∑ j, A j j := by
  classical
  rw [←Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  have h := Finset.sum_erase_add Finset.univ (fun l => A j l) (Finset.mem_univ j)
  linarith

theorem sum_erase_transpose {m : ℕ} (A : Fin m → Fin m → ℝ) :
    (∑ j, ∑ l∈Finset.univ.erase j, A l j)=(∑ j, ∑ l∈Finset.univ.erase j, A j l) := by
  rw [sum_erase_eq_full_sub_diagonal,sum_erase_eq_full_sub_diagonal]
  rw [Finset.sum_comm]

theorem sum_erase_pairing {m : ℕ} (A : Fin m → Fin m → ℝ) :
    (∑ j, ∑ l∈Finset.univ.erase j, A j l)=
      (1/2:ℝ)*(∑ j, ∑ l∈Finset.univ.erase j, (A j l+A l j)) := by
  simp_rw [Finset.sum_add_distrib]
  rw [sum_erase_transpose]
  ring

/-- The weighted signed hard-facet quantity in Supplemental H.1. -/
def hardGaussianWeightedFacetIntegral {m n : ℕ} (u : Fin m → Vector (n+1)) (b : Vector m) : ℝ :=
  ∑ j, |b j| *hardGaussianFacetIntegral u b j

/-- The actual two oriented Green terms combine to the paired numerator.
The symmetry premise is an ordinary density symmetry; it is discharged
by the geometric two-normal section identity separately. -/
theorem hardGaussianWeightedFacetIntegral_pairing {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j, vectorNormSq (u j)=1)
    (hreg : ∀ j, ResidualThresholdRegularity u b j)
    (hsym : ∀ j l, hardFacetResidualDensity u b j l=hardFacetResidualDensity u b l j) :
    hardGaussianWeightedFacetIntegral u b=
      (∑ j, |b j| *(b j^2-1)*gaussianThresholdFirst u b j)-
      (1/2:ℝ)*(∑ j, ∑ l∈Finset.univ.erase j,
        (|b j| *(b l-faceDot (u j) (u l)*b j)+
          |b l| *(b j-faceDot (u j) (u l)*b l))*hardFacetResidualDensity u b j l) := by
  let A := fun j l => |b j| *(b l-faceDot (u j) (u l)*b j)*hardFacetResidualDensity u b j l
  have he : hardGaussianWeightedFacetIntegral u b=
      (∑ j, |b j| *(b j^2-1)*gaussianThresholdFirst u b j)-
        ∑ j, ∑ l∈Finset.univ.erase j, A j l := by
    unfold hardGaussianWeightedFacetIntegral
    simp_rw [hardGaussianFacet_Green_residual_of_slack u b _ (hu _) (hreg _),mul_sub,
      Finset.mul_sum]
    rw [Finset.sum_sub_distrib]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      ring
    · apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro l _
      dsimp only [A]
      ring
  rw [he,sum_erase_pairing A]
  congr 2
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro l _
  dsimp only [A]
  rw [←hsym j l,faceDot_comm (u l) (u j)]
  ring


/-- Actual signed weighted facet pairing with its density symmetry
proved from genuine two-normal Gaussian sections. -/
theorem hardGaussianWeightedFacetIntegral_pairing_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (hu : ∀ j, vectorNormSq (u j)=1)
    (hreg : ∀ j, ResidualThresholdRegularity u b j) :
    hardGaussianWeightedFacetIntegral u b=
      (∑ j, |b j| *(b j^2-1)*gaussianThresholdFirst u b j)-
      (1/2:ℝ)*(∑ j, ∑ l∈Finset.univ.erase j,
        (|b j| *(b l-faceDot (u j) (u l)*b j)+
          |b l| *(b j-faceDot (u j) (u l)*b l))*hardFacetResidualDensity u b j l) :=
  hardGaussianWeightedFacetIntegral_pairing u b hu hreg
    (fun j l => hardFacetResidualDensity_symm u b j l (hu j) (hu l) (hreg j) (hreg l))

/-- The actual signed weighted pairing holds for almost every threshold
for arbitrary dependent fixed unit normals and arbitrary face count. -/
theorem ae_hardGaussianWeightedFacetIntegral_pairing {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume,
    hardGaussianWeightedFacetIntegral u b=
      (∑ j, |b j| *(b j^2-1)*gaussianThresholdFirst u b j)-
      (1/2:ℝ)*(∑ j, ∑ l∈Finset.univ.erase j,
        (|b j| *(b l-faceDot (u j) (u l)*b j)+
          |b l| *(b j-faceDot (u j) (u l)*b l))*hardFacetResidualDensity u b j l) := by
  filter_upwards [ae_residualThresholdRegularity u] with b hb
  exact hardGaussianWeightedFacetIntegral_pairing_of_slack u b hu hb

end
end RectangleCLTArxivV1
