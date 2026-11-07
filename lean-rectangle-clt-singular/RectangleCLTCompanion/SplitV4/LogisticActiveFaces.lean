import RectangleCLTCompanion.SplitV4.LogisticProjectedBound
import RectangleCLTCompanion.SplitV4.NuclearTraceDual
import Mathlib.Data.Fintype.EquivFin

/-! Exact enumeration of the active signed faces of the original smoother.
Omitted faces have zero selector weight. -/

open MeasureTheory Set
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

def activeFaceEquiv {p : ℕ} (s : FaceSmoother p) : Fin s.faces.card ≃ s.faces :=
  s.faces.equivFin.symm

def activeFaceProjection {p : ℕ} (s : FaceSmoother p) (x : Vector p) : Vector s.faces.card :=
  fun j => FaceSmoother.normalDot (activeFaceEquiv s j).1 x

def activeFaceOffsets {p : ℕ} (s : FaceSmoother p) : Vector s.faces.card :=
  fun j => s.offsets (activeFaceEquiv s j).1

def activeFaceNormals {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) : Fin s.faces.card → Vector r :=
  fun j => if (activeFaceEquiv s j).1.2 then A (activeFaceEquiv s j).1.1 else -A (activeFaceEquiv s j).1.1

@[fun_prop] theorem measurable_activeFaceProjection {p : ℕ} (s : FaceSmoother p) :
    Measurable (activeFaceProjection s) := by
  apply measurable_pi_lambda
  intro j
  unfold activeFaceProjection FaceSmoother.normalDot
  split_ifs <;> fun_prop

theorem activeFaceProjection_affine {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (g : Vector r) (v : Vector p) (σ : ℝ) :
    activeFaceProjection s (Matrix.mulVec (σ • A) g + v) =
      Matrix.mulVec (σ • activeFaceNormals s A) g + activeFaceProjection s v := by
  funext j
  by_cases hj : (activeFaceEquiv s j).1.2 = true
  all_goals
    simp [activeFaceProjection, activeFaceNormals, FaceSmoother.normalDot, hj,
      Matrix.mulVec, dotProduct, Matrix.smul_apply, Pi.smul_apply, smul_eq_mul,
      mul_neg, neg_mul, Finset.sum_neg_distrib] <;> ring

theorem activeFaceNormals_unit {p r : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (hA : ∀ j, vectorNormSq (A j) = 1) (j : Fin s.faces.card) :
    vectorNormSq (activeFaceNormals s A j) = 1 := by
  unfold activeFaceNormals
  split_ifs
  · exact hA _
  · simpa only [vectorNormSq, Pi.neg_apply, neg_sq] using hA (activeFaceEquiv s j).1.1

theorem activeFace_upper_total {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    ((upperFaceSmoother (activeFaceOffsets s) s.bandwidth s.bandwidth_pos).weights
      (activeFaceProjection s x)).T = (s.weights x).T := by
  have hu : ((upperFaceSmoother (activeFaceOffsets s) s.bandwidth s.bandwidth_pos).weights
      (activeFaceProjection s x)).T = ∑ j : Fin s.faces.card,
        Real.exp ((FaceSmoother.normalDot (activeFaceEquiv s j).1 x -
          s.offsets (activeFaceEquiv s j).1) / s.bandwidth) := by
    simp [FaceWeights.T, FaceSmoother.weights, upperFaceSmoother, Fintype.sum_prod_type,
      Fintype.sum_bool, FaceSmoother.faceScore, FaceSmoother.normalDot,
      activeFaceOffsets, activeFaceProjection]
  rw [hu]
  have he := (activeFaceEquiv s).sum_comp (fun f : s.faces =>
    Real.exp ((FaceSmoother.normalDot f.1 x - s.offsets f.1) / s.bandwidth))
  rw [he]
  simp only [FaceWeights.T, FaceSmoother.weights]
  change (∑ f : s.faces, Real.exp (s.faceScore f.1 x / s.bandwidth)) = _
  rw [← Finset.sum_subtype s.faces (fun _ => Iff.rfl)
    (fun f => Real.exp (s.faceScore f x / s.bandwidth))]
  simp [FaceSmoother.faceScore, Finset.sum_filter]

theorem activeFace_upper_F {p : ℕ} (s : FaceSmoother p) (x : Vector p) :
    (upperFaceSmoother (activeFaceOffsets s) s.bandwidth s.bandwidth_pos).F
      (activeFaceProjection s x) = s.F x := by
  change 1 / (1 + _) = 1 / (1 + _)
  rw [activeFace_upper_total]

theorem activeFace_upper_pi {p : ℕ} (s : FaceSmoother p) (x : Vector p) (j : Fin s.faces.card) :
    (upperFaceSmoother (activeFaceOffsets s) s.bandwidth s.bandwidth_pos).pi
      (activeFaceProjection s x) (j, true) = s.pi x (activeFaceEquiv s j).1 := by
  change _ / (1 + _) = _ / (1 + _)
  rw [activeFace_upper_total]
  congr 1
  simp [FaceSmoother.weights, upperFaceSmoother, FaceSmoother.faceScore, FaceSmoother.normalDot,
    activeFaceOffsets, activeFaceProjection, (activeFaceEquiv s j).2]

theorem activeFace_selectorWeight {p k : ℕ} (s : FaceSmoother p)
    (α : Fin k → Fin s.faces.card) (x : Vector p) :
    selectorWeight (upperFaceSmoother (activeFaceOffsets s) s.bandwidth s.bandwidth_pos)
      (fun i => (α i, true)) (activeFaceProjection s x) =
      selectorWeight s (fun i => (activeFaceEquiv s (α i)).1) x := by
  simp only [selectorWeight, activeFace_upper_F, activeFace_upper_pi]

theorem activeFace_projected_score {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (α : Fin k → Fin s.faces.card) (v : Vector p) :
    projectedLogisticGaussianScore (activeFaceNormals s A) (activeFaceOffsets s)
      s.bandwidth s.bandwidth_pos σ α (activeFaceProjection s v) =
      selectorGaussianScore s (σ • A) id (fun i => (activeFaceEquiv s (α i)).1) v := by
  unfold projectedLogisticGaussianScore selectorGaussianScore
  apply congrArg (fun w : Vector r → ℝ => weightedScore (standardGaussian r) id w)
  funext g
  change selectorWeight _ _ _ = selectorWeight _ _ _
  simp only [id_eq]
  rw [← activeFaceProjection_affine s A g v σ, activeFace_selectorWeight]

theorem selectorGaussianScore_inactive {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (α : Fin k → Face p) (v : Vector p)
    (hα : ¬ ∀ i, α i ∈ s.faces) : selectorGaussianScore s A id α v = 0 := by
  push_neg at hα
  obtain ⟨i, hi⟩ := hα
  have hw (g : Vector r) : selectorWeight s α (A.mulVec g + v) = 0 := by
    unfold selectorWeight
    have hpi : s.pi (A.mulVec g + v) (α i) = 0 := by
      simp [FaceSmoother.pi, FaceWeights.pi, FaceSmoother.weights, hi]
    rw [Finset.prod_eq_zero (Finset.mem_univ i) hpi, mul_zero]
  ext j l
  change (∫ g, (g j * g l - if j = l then 1 else 0) *
    selectorWeight s α (A.mulVec g + v) ∂standardGaussian r) = 0
  simp only [hw, mul_zero, integral_zero]

theorem sum_activeFace_tuples {p k : ℕ} (s : FaceSmoother p)
    (f : (Fin k → Face p) → ℝ) (hz : ∀ α, (¬ ∀ i, α i ∈ s.faces) → f α = 0) :
    (∑ α : Fin k → Face p, f α) =
      ∑ β : Fin k → Fin s.faces.card, f (fun i => (activeFaceEquiv s (β i)).1) := by
  classical
  have hf : (∑ α : Fin k → Face p, f α) =
      ∑ α ∈ Finset.univ.filter (fun α : Fin k → Face p => ∀ i, α i ∈ s.faces), f α := by
    symm
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro α _ hn
    apply hz
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hn
  rw [hf]
  apply Finset.sum_bij (fun (α : Fin k → Face p)
    (hα : α ∈ Finset.univ.filter (fun α : Fin k → Face p => ∀ i, α i ∈ s.faces)) (i : Fin k) => s.faces.equivFin
    ⟨α i, (Finset.mem_filter.mp hα).2 i⟩)
  · intro α hα
    exact Finset.mem_univ _
  · intro α hα β hβ he
    funext i
    have hh := congrFun he i
    exact congrArg Subtype.val (s.faces.equivFin.injective hh)
  · intro β _
    refine ⟨fun i => (activeFaceEquiv s (β i)).1, ?_, ?_⟩
    · simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      intro i
      exact (activeFaceEquiv s (β i)).2
    · funext i
      simp [activeFaceEquiv]
  · intro α hα
    congr 1
    funext i
    simp [activeFaceEquiv]

theorem sum_selector_nuclear_eq_active {p r k : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin r) ℝ) (σ : ℝ) (v : Vector p) :
    (∑ α : Fin k → Face p, symmetricNuclearNorm (selectorGaussianScore s (σ • A) id α v)) =
      ∑ α : Fin k → Fin s.faces.card, symmetricNuclearNorm
        (projectedLogisticGaussianScore (activeFaceNormals s A) (activeFaceOffsets s)
          s.bandwidth s.bandwidth_pos σ α (activeFaceProjection s v)) := by
  rw [sum_activeFace_tuples s _ (fun α hα => by
    rw [selectorGaussianScore_inactive s _ α v hα, symmetricNuclearNorm_zero])]
  apply Finset.sum_congr rfl
  intro α _
  rw [activeFace_projected_score]

end

end RectangleCLT.Companion.SplitV4
