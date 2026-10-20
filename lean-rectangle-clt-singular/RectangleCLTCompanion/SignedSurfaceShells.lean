import RectangleCLTCompanion.SignedSurfaceRadius
import RectangleCLTCompanion.SignedSurfaceTubeDomains
import Mathlib.Data.Nat.Find

/-! A disjoint measurable dyadic partition of the actual Gaussian source.
The same partition is used for singleton and paired-face tubes. -/

open MeasureTheory RectangleCLT.GaussianTube
open scoped BigOperators

namespace RectangleCLT.Companion.SignedSurface

noncomputable section

def dyadicShell {Ω : Type*} (K : Ω → ℝ) (n : ℕ) : Set Ω :=
  {z | K z ≤ dyadicRadius n ∧ (n = 0 ∨ dyadicRadius n / 2 < K z)}

theorem measurableSet_dyadicShell {Ω : Type*} [MeasurableSpace Ω]
    (K : Ω → ℝ) (hK : Measurable K) (n : ℕ) : MeasurableSet (dyadicShell K n) := by
  unfold dyadicShell
  exact (measurableSet_le hK measurable_const).inter
    (MeasurableSet.union (by
      by_cases h : n = 0
      · simp only [h]; exact MeasurableSet.univ
      · simp only [h]; exact MeasurableSet.empty)
      (measurableSet_lt measurable_const hK))

lemma dyadicRadius_mono : Monotone dyadicRadius := by
  intro n m hnm
  exact pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.succ_le_succ hnm)

lemma dyadicRadius_next (n : ℕ) : dyadicRadius (n + 1) = 2 * dyadicRadius n := by
  unfold dyadicRadius
  rw [pow_succ]
  ring

lemma dyadicShell_disjoint_of_lt {Ω : Type*} (K : Ω → ℝ) {n m : ℕ} (hnm : n < m) :
    Disjoint (dyadicShell K n) (dyadicShell K m) := by
  rw [Set.disjoint_left]
  intro z hz hnz
  have hm : m ≠ 0 := Nat.ne_of_gt (lt_of_le_of_lt (Nat.zero_le _) hnm)
  have hlower : dyadicRadius m / 2 < K z := hnz.2.resolve_left hm
  have hstep := dyadicRadius_mono (Nat.succ_le_iff.mpr hnm)
  rw [dyadicRadius_next] at hstep
  have hu := hz.1
  linarith

theorem dyadicShell_pairwise_disjoint {Ω : Type*} (K : Ω → ℝ) :
    Pairwise (fun n m => Disjoint (dyadicShell K n) (dyadicShell K m)) := by
  intro n m hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact dyadicShell_disjoint_of_lt K hlt
  · exact (dyadicShell_disjoint_of_lt K hgt).symm

theorem iUnion_dyadicShell {Ω : Type*} (K : Ω → ℝ) :
    (⋃ n : ℕ, dyadicShell K n) = Set.univ := by
  classical
  apply Set.eq_univ_of_forall
  intro z
  have hex : ∃ n : ℕ, K z ≤ dyadicRadius n := by
    obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt (K z) (by norm_num : (1 : ℝ) < 2)
    exact ⟨n, hn.le.trans (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (Nat.le_succ n))⟩
  let n := Nat.find hex
  apply Set.mem_iUnion.mpr
  refine ⟨n, Nat.find_spec hex, ?_⟩
  by_cases hn : n = 0
  · exact Or.inl hn
  · right
    obtain ⟨m, hm⟩ := Nat.exists_eq_succ_of_ne_zero hn
    have hprev : ¬K z ≤ dyadicRadius m := Nat.find_min hex (by change m < n; omega)
    have hrad : dyadicRadius n / 2 = dyadicRadius m := by rw [hm, dyadicRadius_next]; ring
    rw [hrad]
    exact lt_of_not_ge hprev

/-- The source integrals form an actual convergent sum, rather than an
assumed summability statement. -/
theorem hasSum_integral_dyadicShell {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (K : Ω → ℝ) (hK : Measurable K) (f : Ω → ℝ) (hf : Integrable f μ) :
    HasSum (fun n => ∫ z in dyadicShell K n, f z ∂μ) (∫ z, f z ∂μ) := by
  have hh := hasSum_integral_iUnion (measurableSet_dyadicShell K hK)
    (dyadicShell_pairwise_disjoint K)
    (show IntegrableOn f (⋃ n : ℕ, dyadicShell K n) μ by
      rw [iUnion_dyadicShell]
      simpa only [IntegrableOn, Measure.restrict_univ] using hf)
  simpa only [iUnion_dyadicShell, Measure.restrict_univ] using hh

/-- Every image from a source shell is in the needed Gaussian output tail.
The proof uses physical displacement only, even if individual normal
coefficients are large. -/
theorem imageEventOf_dyadicShell_tail {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (n : ℕ)
    (D : Set (Fin q → ℝ))
    (hD : ∀ c ∈ D, ‖projectionEuclideanVector ((normalMatrix S A).mulVec c)‖ ≤ 1)
    {ze : CommonSamples p}
    (hz : ze ∈ imageEventOf S s A r (dyadicShell (fourFaceProjectionRadius A) n) D) :
    dyadicRadius n / 2 - 1 ≤ fourFaceProjectionRadius A ze.1 := by
  by_cases hn : n = 0
  · subst n
    simpa only [dyadicRadius, Nat.zero_add, pow_one, show (2 : ℝ) / 2 - 1 = 0 by norm_num]
      using fourFaceProjectionRadius_nonneg A ze.1
  · obtain ⟨_h0, _he, w, hw, hm⟩ := hz
    have hs : dyadicRadius n / 2 ≤ fourFaceProjectionRadius A (base w) :=
      (hw.1.2.resolve_left hn).le
    have hh := output_projection_tail_of_displacement A (base w)
      ((normalMatrix S A).mulVec (tube w)) hs (hD _ hw.2.1)
    have hy := congrArg (base : Coordinates p q → Vector p) hm
    rw [base_map] at hy
    change base w + (normalMatrix S A).mulVec (tube w) = ze.1 at hy
    rw [hy] at hh
    exact hh

end
end RectangleCLT.Companion.SignedSurface
