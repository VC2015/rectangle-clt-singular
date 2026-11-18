import RectangleCLTArxivV1.SupplementalHGenericStrata
import RectangleCLTArxivV1.SupplementalHLocalFiniteThreshold

/-! Generic residual regularity after finitely many affine threshold
conditionings. The retained coordinate always has coefficient one. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def affineResidualThresholds {m q : ℕ} (f : Fin q → Fin m)
    (A : Fin m → Fin q → ℝ) (b : Vector m) : Vector m :=
  fun k => b k-∑ i, A k i*b (f i)

/-- Ordinary finite residual threshold regularity holds almost everywhere
when the conditioned coordinates are excluded from the retained family. -/
theorem ae_affineResidualThresholdRegularity {m r q : ℕ}
    (s : Finset (Fin m)) (v : Fin m → Vector r) (f : Fin q → Fin m)
    (A : Fin m → Fin q → ℝ) (hout : ∀ k∈s, ∀ i, k≠f i) :
    ∀ᵐ b : Vector m ∂volume,
      LocalFiniteThresholdRegularity s v (affineResidualThresholds f A b) := by
  apply Filter.eventually_all.mpr
  intro k
  by_cases hk : k∈s
  · have hfirst := ae_threshold_ne_finite_coordinate_combination f k (hout k hk) (A k)
    have hsecond : ∀ᵐ b : Vector m ∂volume, ∀ l∈s.erase k,
        affineResidualThresholds f A b l-
          (affineResidualThresholds f A b k/localFiniteThresholdScale v k)*
            faceDot (v l) (localFiniteThresholdDirection v k)≠0 := by
      apply Filter.eventually_all.mpr
      intro l
      by_cases hl : l∈s.erase k
      · let D : ℝ := faceDot (v l) (localFiniteThresholdDirection v k)/localFiniteThresholdScale v k
        let g : Fin (q+1) → Fin m := Fin.cons k f
        let B : Fin (q+1) → ℝ := Fin.cons D (fun i => A l i-D*A k i)
        have hlg : ∀ i, l≠g i := by
          intro i
          refine Fin.cases ?_ (fun i => ?_) i
          · exact (Finset.mem_erase.mp hl).1
          · exact hout l (Finset.mem_erase.mp hl).2 i
        have ha := ae_threshold_ne_finite_coordinate_combination g l hlg B
        have he (b : Vector m) : affineResidualThresholds f A b l-
            (affineResidualThresholds f A b k/localFiniteThresholdScale v k)*
              faceDot (v l) (localFiniteThresholdDirection v k)=b l-∑ i, B i*b (g i) := by
          simp only [affineResidualThresholds,g,B,Fin.sum_univ_succ,Fin.cons_zero,Fin.cons_succ]
          simp only [sub_mul,Finset.sum_sub_distrib,Finset.mul_sum,div_eq_mul_inv,D]
          ring_nf
          simp only [Finset.mul_sum]
          congr 1
          apply Finset.sum_congr rfl
          intro i _
          ring
        exact ha.mono (fun b h _ => by rwa [he])
      · exact ae_of_all _ (fun _ h => False.elim (hl h))
    filter_upwards [hfirst,hsecond] with b hb hs
    intro _
    exact ⟨Or.inr hb,fun l hl => Or.inr (hs l hl)⟩
  · exact ae_of_all _ (fun _ h => False.elim (hk h))

end
end RectangleCLTArxivV1
