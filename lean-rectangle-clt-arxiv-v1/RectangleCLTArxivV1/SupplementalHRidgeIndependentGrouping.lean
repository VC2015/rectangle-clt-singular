import RectangleCLTArxivV1.SupplementalHIndependentTriples
import RectangleCLTArxivV1.SupplementalHTripleIncidenceAtoms

/-! The native signed ridge remainder is genuinely supported on the
finite family of independent normal triples at generic thresholds. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT
open scoped BigOperators
noncomputable section

theorem ae_all_tripleIncidenceRegularity {m r : ℕ} (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume, ∀ F : Fin 3 → Fin m, TripleIncidenceRegularity u b F := by
  apply Filter.eventually_all.mpr
  intro F
  exact ae_tripleIncidenceRegularity u F

/-- The actual signed remainder is exactly the independent-triple sum;
no conditioning frame is requested for any dependent or empty stratum. -/
theorem ae_hardGaussianRidgeThirdBoundaryIntegral_independent_sum {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, RectangleCLT.vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume,
      hardGaussianRidgeThirdBoundaryIntegral u b=
        (1/6:ℝ)*(∑ F : IndependentNormalTriple u,
          hardGaussianRidgeThirdIncidenceGroup u b (F.val 0) (F.val 1) (F.val 2)) := by
  filter_upwards [ae_all_tripleIncidenceRegularity u] with b hb
  rw [hardGaussianRidgeThirdBoundaryIntegral_grouping]
  change (1/6:ℝ)*(∑ j, ∑ l, ∑ k, hardGaussianRidgeThirdIncidenceGroup u b j l k)=_
  congr 1
  apply sum_cube_eq_independent_triples
  intro F hdep
  exact hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent u b F hdep (fun i => hu (F i)) (hb F)

/-- Absolute values are taken on each actual three-incidence group after
all dependent contributions have been proved to vanish. -/
theorem ae_abs_hardGaussianRidgeThirdBoundaryIntegral_le_independent_groups {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, RectangleCLT.vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume,
      abs (hardGaussianRidgeThirdBoundaryIntegral u b)≤
        (1/6:ℝ)*(∑ F : IndependentNormalTriple u,
          abs (hardGaussianRidgeThirdIncidenceGroup u b (F.val 0) (F.val 1) (F.val 2))) := by
  filter_upwards [ae_all_tripleIncidenceRegularity u] with b hb
  have hz (F : Fin 3 → Fin m) (hdep : ¬LinearIndependent ℝ (fun i => u (F i))) :
      abs (hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2))=0 := by
    rw [hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent u b F hdep (fun i => hu (F i)) (hb F),abs_zero]
  have hs := sum_cube_eq_independent_triples u
    (fun j l k => abs (hardGaussianRidgeThirdIncidenceGroup u b j l k)) hz
  exact (abs_hardGaussianRidgeThirdBoundaryIntegral_le_groups u b).trans_eq (by rw [hs])

end
end RectangleCLTArxivV1
