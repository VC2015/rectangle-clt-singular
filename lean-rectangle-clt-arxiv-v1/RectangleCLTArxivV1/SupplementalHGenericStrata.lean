import RectangleCLTArxivV1.SupplementalHGenericThreshold
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-! At almost every threshold, a rank-three active normal space has
exactly its three independent active generators. This is derived from
ordinary affine null sets, not imposed as simplicity of the input. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- A threshold outside a fixed tuple cannot identically agree with
any prescribed finite combination of its coordinate thresholds. -/
theorem ae_threshold_ne_finite_coordinate_combination {m q : ℕ}
    (f : Fin q → Fin m) (l : Fin m) (hl : ∀ i, l≠f i) (a : Fin q → ℝ) :
    ∀ᵐ b : Vector m ∂volume, b l-(∑ i, a i*b (f i))≠0 := by
  let w : Vector m := (Pi.single l (1:ℝ) : Vector m)-
    ∑ i, a i • (Pi.single (f i) (1:ℝ) : Vector m)
  have hw : w≠0 := by
    intro h
    have hh := congrFun h l
    simp [w,Finset.sum_apply,Pi.single_apply,hl] at hh
  have he (b : Vector m) : faceDot w b=b l-∑ i, a i*b (f i) := by
    rw [show w=(Pi.single l (1:ℝ) : Vector m)-∑ i, a i • (Pi.single (f i) (1:ℝ) : Vector m) from rfl,
      threshold_faceDot_sub_left]
    have hs (i : Fin m) : faceDot (Pi.single i 1) b=b i := by
      simp [faceDot,Pi.single_apply,ite_mul]
    rw [hs]
    congr 1
    unfold faceDot
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    simp_rw [mul_assoc]
    rw [←Finset.mul_sum]
    have hh : (∑ k, (Pi.single (f i) (1:ℝ) : Vector m) k*b k)=b (f i) := hs (f i)
    simpa only [mul_assoc] using congrArg (fun x => a i*x) hh
  simpa only [he] using ae_volume_faceDot_ne w hw 0

/-- A fixed choice of actual linear coefficients whenever a normal lies
in a selected three-normal span. -/
def threeNormalSpanCoefficients {m r : ℕ} (u : Fin m → Vector r)
    (f : Fin 3 → Fin m) (l : Fin m) : Fin 3 → ℝ := by
  classical
  exact if h : u l∈Submodule.span ℝ (Set.range (fun i => u (f i))) then
    Classical.choose ((Submodule.mem_span_range_iff_exists_fun ℝ).mp h)
  else 0

theorem threeNormalSpanCoefficients_spec {m r : ℕ} (u : Fin m → Vector r)
    (f : Fin 3 → Fin m) (l : Fin m)
    (h : u l∈Submodule.span ℝ (Set.range (fun i => u (f i)))) :
    (∑ i, threeNormalSpanCoefficients u f l i • u (f i))=u l := by
  unfold threeNormalSpanCoefficients
  rw [dif_pos h]
  exact Classical.choose_spec ((Submodule.mem_span_range_iff_exists_fun ℝ).mp h)

/-- Every extra normal in a selected rank-three span misses the common
three supporting hyperplanes at almost every threshold. -/
theorem ae_no_extra_active_normal_in_three_span {m r : ℕ} (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume, ∀ (f : Fin 3 → Fin m) (l : Fin m),
      (∀ i, l≠f i) → u l∈Submodule.span ℝ (Set.range (fun i => u (f i))) →
      ∀ x : Vector r, (∀ i, faceDot (u (f i)) x=b (f i)) → faceDot (u l) x≠b l := by
  have ha : ∀ᵐ b : Vector m ∂volume, ∀ (f : Fin 3 → Fin m) (l : Fin m),
      (∀ i, l≠f i) → b l-(∑ i, threeNormalSpanCoefficients u f l i*b (f i))≠0 := by
    apply Filter.eventually_all.mpr
    intro f
    apply Filter.eventually_all.mpr
    intro l
    by_cases hl : ∀ i, l≠f i
    · exact (ae_threshold_ne_finite_coordinate_combination f l hl (threeNormalSpanCoefficients u f l)).mono
        (fun _ h _ => h)
    · exact ae_of_all _ (fun _ h => False.elim (hl h))
  filter_upwards [ha] with b hb
  intro f l hl hspan x hx heq
  have hs := threeNormalSpanCoefficients_spec u f l hspan
  have hdot := congrArg (fun v => faceDot v x) hs
  have hsum : faceDot (∑ i, threeNormalSpanCoefficients u f l i • u (f i)) x=
      ∑ i, threeNormalSpanCoefficients u f l i*b (f i) := by
    unfold faceDot
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    have hh := hx i
    change (∑ k, u (f i) k*x k)=b (f i) at hh
    calc
      _ = threeNormalSpanCoefficients u f l i*(∑ k, u (f i) k*x k) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k _
        ring
      _ = _ := by rw [hh]
  change faceDot (∑ i, threeNormalSpanCoefficients u f l i • u (f i)) x=faceDot (u l) x at hdot
  rw [hsum,heq] at hdot
  exact hb f l hl (by linarith)

end
end RectangleCLTArxivV1
