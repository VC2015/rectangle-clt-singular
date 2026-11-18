import RectangleCLTArxivV1.SupplementalHTripleIncidenceGeometry

/-! One actual codimension-three hard Gaussian mass for the three ridge
conditioning choices of an actually selected independent normal tuple. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

def tripleIncidencePairFaces {m : ℕ} (F : Fin 3 → Fin m) (i : Fin 3) : Finset (Fin m) :=
  (Finset.univ.erase (tripleIncidenceLeft F i)).erase (tripleIncidenceRight F i)

def tripleIncidenceRemaining {m : ℕ} (F : Fin 3 → Fin m) : Finset (Fin m) :=
  Finset.univ.filter (fun k => ∀ a : Fin 3, k≠F a)

theorem tripleIncidence_remaining_eq {m : ℕ} (F : Fin 3 → Fin m) (i : Fin 3) :
    (tripleIncidencePairFaces F i).erase (F i)=tripleIncidenceRemaining F := by
  classical
  ext k
  simp only [tripleIncidencePairFaces,tripleIncidenceRemaining,Finset.mem_erase,
    Finset.mem_univ,Finset.mem_filter,true_and,and_true]
  constructor
  · rintro ⟨hi,hr,hl⟩ a
    by_cases hai : a=i
    · subst a
      exact hi
    · obtain ⟨t,rfl⟩ := Fin.exists_succAbove_eq hai
      fin_cases t
      · exact hl
      · exact hr
  · intro h
    exact ⟨h i,h (i.succAbove 1),h (i.succAbove 0)⟩

theorem tripleIncidence_third_mem_pairFaces {m r : ℕ} (u : Fin m → Vector r)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i))) (i : Fin 3) :
    F i∈tripleIncidencePairFaces F i := by
  have hinj : Function.Injective F := fun a b h => hi.injective (by rw [h])
  apply Finset.mem_erase.mpr
  refine ⟨?_,Finset.mem_erase.mpr ⟨?_,Finset.mem_univ _⟩⟩
  · exact fun h => (Fin.succAbove_ne i 1) (hinj h).symm
  · exact fun h => (Fin.succAbove_ne i 0) (hinj h).symm

def tripleIncidenceCommonMass {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) : ℝ :=
  gaussianFrameHardMass (tripleIncidenceRemaining F) u b (tripleIncidenceFrame u F 0)
    (tripleIncidenceLevels u b F 0)

theorem tripleIncidenceCommonMass_nonneg {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (F : Fin 3 → Fin m) : 0≤tripleIncidenceCommonMass u b F :=
  gaussianFrameHardMass_nonneg _ _ _ _ _

/-- All three actual conditioning choices share one actual hard mass at
every threshold, retaining every additional inactive inequality. -/
theorem tripleIncidence_mass_eq_common {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    gaussianFrameHardMass (tripleIncidenceRemaining F) u b (tripleIncidenceFrame u F i)
      (tripleIncidenceLevels u b F i)=tripleIncidenceCommonMass u b F := by
  exact gaussianFrameHardMass_frame_independent _ u b _ _
    (tripleIncidenceFrame_orthonormal u F hi hu i) (tripleIncidenceFrame_orthonormal u F hi hu 0) _ _
    ((tripleIncidenceFrame_span u F hi hu i).trans (tripleIncidenceFrame_span u F hi hu 0).symm)
    (tripleIncidenceNormalPoint_eq u b F hi hu i 0)

def tripleIncidenceBoundaryDensity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  hardGaussianPairThirdBoundaryDensity (tripleIncidencePairFaces F i) u b
    (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)
    (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i) (F i)

def TripleIncidenceRegularity {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) : Prop :=
  ∀ i, LocalFiniteThresholdRegularity (tripleIncidencePairFaces F i)
    (hardPairResidualNormals u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i))
    (hardPairResidualLevels u b (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)
      (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i))

theorem ae_tripleIncidenceRegularity {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) :
    ∀ᵐ b : Vector m ∂volume, TripleIncidenceRegularity u b F := by
  filter_upwards [ae_pairResidualThresholdRegularity u] with b hb
  exact fun i => hb (tripleIncidenceLeft F i) (tripleIncidenceRight F i)

/-- The actual raw third boundary densities carry precisely their
selected residual Jacobian, and share the same original-tuple mass. -/
theorem tripleIncidence_scaled_density_eq_common {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (hreg : TripleIncidenceRegularity u b F) (i : Fin 3) :
    tripleIncidenceScale u F i*tripleIncidenceBoundaryDensity u b F i=tripleIncidenceCommonMass u b F := by
  obtain ⟨he,hf,hef⟩ := tripleIncidence_pair_geometry u F hi hu i
  have hh := hardGaussianPairThirdBoundaryDensity_scale_eq_mass (tripleIncidencePairFaces F i) u b
    (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) he hf hef
    (tripleIncidenceAlpha u b F i) (tripleIncidenceBeta u b F i) (F i)
    (tripleIncidence_third_mem_pairFaces u F hi i)
    (tripleIncidence_third_residual_ne_zero u F hi hu i) (hreg i)
  change tripleIncidenceScale u F i*tripleIncidenceBoundaryDensity u b F i=
    gaussianFrameHardMass ((tripleIncidencePairFaces F i).erase (F i)) u b
      (tripleIncidenceFrame u F i) (tripleIncidenceLevels u b F i) at hh
  rw [tripleIncidence_remaining_eq,tripleIncidence_mass_eq_common u b F hi hu i] at hh
  exact hh

theorem tripleIncidence_weighted_density_eq_common {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (F : Fin 3 → Fin m)
    (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (hreg : TripleIncidenceRegularity u b F) (i : Fin 3) :
    tripleIncidenceShift u b F i*tripleIncidenceBoundaryDensity u b F i=
      (tripleIncidenceShift u b F i/tripleIncidenceScale u F i)*tripleIncidenceCommonMass u b F := by
  have hσ := hardPairThirdScale_pos u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i)
    (F i) (tripleIncidence_third_residual_ne_zero u F hi hu i)
  rw [← tripleIncidence_scaled_density_eq_common u b F hi hu hreg i]
  change _=(_/hardPairThirdScale u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (F i))*
    (hardPairThirdScale u (tripleIncidenceFirst u F i) (tripleIncidenceSecond u F i) (F i)*_)
  field_simp
  ring

theorem tripleIncidence_normal_distance_pairing {m r : ℕ} (u : Fin m → Vector r) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (i : Fin 3) :
    ⟪tripleIncidenceNormalPoint u b F 0,(WithLp.equiv 2 (Vector r)).symm (tripleIncidenceThird u F i)⟫_ℝ=
      tripleIncidenceShift u b F i/tripleIncidenceScale u F i := by
  have hh := (tripleIncidenceFrame_orthonormal u F hi hu i).inner_left_fintype
    (tripleIncidenceLevels u b F i) (2 : Fin 3)
  change ⟪tripleIncidenceNormalPoint u b F i,
    (WithLp.equiv 2 (Vector r)).symm (tripleIncidenceThird u F i)⟫_ℝ=
      tripleIncidenceShift u b F i/tripleIncidenceScale u F i at hh
  rw [tripleIncidenceNormalPoint_eq u b F hi hu i 0] at hh
  exact hh

def tripleIncidenceAngle {m r : ℕ} (u : Fin m → Vector r) (F : Fin 3 → Fin m) (i : Fin 3) : ℝ :=
  Real.arccos (faceDot (u (tripleIncidenceLeft F i)) (u (tripleIncidenceRight F i)))

/-- Exact signed grouping of the three actual ridge Green boundary
atoms of one selected rank-three tuple. There is one common Gaussian
mass and one actual angle-weighted residual-normal vector. -/
theorem tripleIncidence_signed_grouping {m n : ℕ} (u : Fin m → Vector (n+1)) (b : Vector m)
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) (hreg : TripleIncidenceRegularity u b F) :
    (∑ i, tripleIncidenceAngle u F i*(tripleIncidenceShift u b F i*tripleIncidenceBoundaryDensity u b F i))=
      tripleIncidenceCommonMass u b F*⟪tripleIncidenceNormalPoint u b F 0,
        ∑ i, tripleIncidenceAngle u F i •
          (WithLp.equiv 2 (Vector (n+1))).symm (tripleIncidenceThird u F i)⟫_ℝ := by
  have hp : ⟪tripleIncidenceNormalPoint u b F 0,
      ∑ i, tripleIncidenceAngle u F i •
        (WithLp.equiv 2 (Vector (n+1))).symm (tripleIncidenceThird u F i)⟫_ℝ=
      ∑ i, tripleIncidenceAngle u F i*(tripleIncidenceShift u b F i/tripleIncidenceScale u F i) := by
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_smul_right,tripleIncidence_normal_distance_pairing u b F hi hu i]
  rw [hp,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [tripleIncidence_weighted_density_eq_common u b F hi hu hreg i]
  ring

theorem ae_tripleIncidence_scaled_densities_common {m n : ℕ} (u : Fin m → Vector (n+1))
    (F : Fin 3 → Fin m) (hi : LinearIndependent ℝ (fun i => u (F i)))
    (hu : ∀ i, vectorNormSq (u (F i))=1) :
    ∀ᵐ b : Vector m ∂volume, ∀ i,
      tripleIncidenceScale u F i*tripleIncidenceBoundaryDensity u b F i=tripleIncidenceCommonMass u b F := by
  filter_upwards [ae_tripleIncidenceRegularity u F] with b hb
  exact fun i => tripleIncidence_scaled_density_eq_common u b F hi hu hb i

end
end RectangleCLTArxivV1
