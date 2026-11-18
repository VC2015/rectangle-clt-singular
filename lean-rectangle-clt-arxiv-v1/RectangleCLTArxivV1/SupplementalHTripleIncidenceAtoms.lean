import RectangleCLTArxivV1.SupplementalHTripleIncidenceMass
import RectangleCLTArxivV1.SupplementalHRidgeTripleGrouping

/-! Actual signed ridge-atom grouping for one selected normal tuple.
Rank-three tuples share one genuine mass; dependent tuple atoms vanish
under ordinary local slack. No tuple counting premise is imposed. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators InnerProductSpace
noncomputable section
attribute [local instance] Classical.propDecidable

theorem hardGaussianRidgeThirdAtom_eq_tripleIncidence {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m) (i : Fin 3)
    (hp : hardGaussianRidgeNonparallel u (tripleIncidenceLeft F i) (tripleIncidenceRight F i))
    (hk : F i∈tripleIncidencePairFaces F i) :
    hardGaussianRidgeThirdAtom u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i) (F i)=
      tripleIncidenceAngle u F i*(tripleIncidenceShift u b F i*tripleIncidenceBoundaryDensity u b F i) := by
  classical
  dsimp only [tripleIncidencePairFaces] at hk
  unfold hardGaussianRidgeThirdAtom
  rw [if_pos hp,if_pos hk]
  unfold hardGaussianRidgeNormalWeight tripleIncidenceAngle tripleIncidenceShift
    tripleIncidenceBoundaryDensity hardGaussianPairThirdBoundaryDensity tripleIncidencePairFaces
    tripleIncidenceFirst tripleIncidenceSecond tripleIncidenceAlpha tripleIncidenceBeta
  ring

theorem hardGaussianRidgeThirdAtom_eq_tripleIncidence_of_independent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a))) (i : Fin 3) :
    hardGaussianRidgeThirdAtom u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i) (F i)=
      tripleIncidenceAngle u F i*(tripleIncidenceShift u b F i*tripleIncidenceBoundaryDensity u b F i) :=
  hardGaussianRidgeThirdAtom_eq_tripleIncidence u b F i
    (tripleIncidence_pair_nondegenerate u F hi i) (tripleIncidence_third_mem_pairFaces u F hi i)

/-- Every dependent triple atom is genuinely zero: either its selected
pair/face guard fails, or its third residual is zero and has nonzero
ordinary slack. The converse rank classification discharges the latter. -/
theorem hardGaussianRidgeThirdAtom_zero_of_dependent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hdep : ¬LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (hreg : TripleIncidenceRegularity u b F) (i : Fin 3) :
    hardGaussianRidgeThirdAtom u b (tripleIncidenceLeft F i) (tripleIncidenceRight F i) (F i)=0 := by
  classical
  by_cases hp : hardGaussianRidgeNonparallel u (tripleIncidenceLeft F i) (tripleIncidenceRight F i)
  · by_cases hk : F i∈tripleIncidencePairFaces F i
    · have hz : hardPairResidualNormal (tripleIncidenceFirst u F i)
          (tripleIncidenceSecond u F i) (u (F i))=0 := by
        by_contra hn
        exact hdep (tripleIncidence_independent_of_third_residual_ne_zero u F hu i hp.1 hp.2 hn)
      have hzero : tripleIncidenceBoundaryDensity u b F i=0 :=
        hardGaussianPairThirdBoundaryDensity_zero_of_zero_residual _ _ _ _ _ _ _ _ hk hz (hreg i)
      rw [hardGaussianRidgeThirdAtom_eq_tripleIncidence u b F i hp hk,hzero,mul_zero,mul_zero]
    · unfold hardGaussianRidgeThirdAtom
      dsimp only [tripleIncidencePairFaces] at hk
      rw [if_pos hp,if_neg hk]
  · unfold hardGaussianRidgeThirdAtom
    rw [if_neg hp]

theorem hardGaussianRidgeThirdIncidenceGroup_eq_tuple_sum {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m) :
    hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=
      ∑ i : Fin 3, hardGaussianRidgeThirdAtom u b
        (tripleIncidenceLeft F i) (tripleIncidenceRight F i) (F i) := by
  rw [Fin.sum_univ_three]
  rfl

/-- The actual guarded ridge incidence group is the common codimension-
three mass times the actual signed angle-weighted residual-normal vector. -/
theorem hardGaussianRidgeThirdIncidenceGroup_eq_common_vector {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (hreg : TripleIncidenceRegularity u b F) :
    hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=
      tripleIncidenceCommonMass u b F*⟪tripleIncidenceNormalPoint u b F 0,
        ∑ i, tripleIncidenceAngle u F i •
          (WithLp.equiv 2 (Vector (n+1))).symm (tripleIncidenceThird u F i)⟫_ℝ := by
  rw [hardGaussianRidgeThirdIncidenceGroup_eq_tuple_sum]
  simp_rw [hardGaussianRidgeThirdAtom_eq_tripleIncidence_of_independent u b F hi]
  exact tripleIncidence_signed_grouping u b F hi hu hreg

theorem hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (F : Fin 3 → Fin m)
    (hdep : ¬LinearIndependent ℝ (fun a => u (F a)))
    (hu : ∀ a, vectorNormSq (u (F a))=1) (hreg : TripleIncidenceRegularity u b F) :
    hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=0 := by
  rw [hardGaussianRidgeThirdIncidenceGroup_eq_tuple_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact hardGaussianRidgeThirdAtom_zero_of_dependent u b F hdep hu hreg i

/-- Complete rank classification of an actual ordered triple group at
almost every threshold. Dependent triples contribute zero. -/
theorem ae_hardGaussianRidgeThirdIncidenceGroup_classification {m n : ℕ}
    (u : Fin m → Vector (n+1)) (F : Fin 3 → Fin m)
    (hu : ∀ a, vectorNormSq (u (F a))=1) :
    ∀ᵐ b : Vector m ∂volume, hardGaussianRidgeThirdIncidenceGroup u b (F 0) (F 1) (F 2)=
      if LinearIndependent ℝ (fun a => u (F a)) then
        tripleIncidenceCommonMass u b F*⟪tripleIncidenceNormalPoint u b F 0,
          ∑ i, tripleIncidenceAngle u F i •
            (WithLp.equiv 2 (Vector (n+1))).symm (tripleIncidenceThird u F i)⟫_ℝ
      else 0 := by
  classical
  filter_upwards [ae_tripleIncidenceRegularity u F] with b hb
  by_cases hi : LinearIndependent ℝ (fun a => u (F a))
  · rw [if_pos hi]
    exact hardGaussianRidgeThirdIncidenceGroup_eq_common_vector u b F hi hu hb
  · rw [if_neg hi]
    exact hardGaussianRidgeThirdIncidenceGroup_zero_of_dependent u b F hi hu hb

end
end RectangleCLTArxivV1
