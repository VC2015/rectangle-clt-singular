import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Continuous genuine coordinate derivatives give a genuine Fréchet derivative.
The proof changes one coordinate at a time and applies the scalar mean value
bound to each edge of the resulting finite path. -/

open Filter Set
open scoped BigOperators Topology

namespace RectangleCLT.Companion.SplitV4
noncomputable section

private def coordinateHybrid {m : ℕ} (s : Finset (Fin m)) (x y : Fin m → ℝ) : Fin m → ℝ :=
  fun j => if j ∈ s then y j else x j

private theorem coordinateHybrid_empty {m : ℕ} (x y : Fin m → ℝ) :
    coordinateHybrid ∅ x y = x := by ext j; simp [coordinateHybrid]

private theorem coordinateHybrid_univ {m : ℕ} (x y : Fin m → ℝ) :
    coordinateHybrid Finset.univ x y = y := by ext j; simp [coordinateHybrid]

private theorem coordinateHybrid_insert {m : ℕ} (s : Finset (Fin m)) (x y : Fin m → ℝ)
    (j : Fin m) : coordinateHybrid (insert j s) x y = Function.update (coordinateHybrid s x y) j (y j) := by
  classical
  ext k
  by_cases hk : k = j
  · subst k; simp [coordinateHybrid]
  · simp [coordinateHybrid, hk]

private theorem coordinateHybrid_path_norm {m : ℕ} (s : Finset (Fin m))
    (x y : Fin m → ℝ) (j : Fin m) (hj : j ∉ s) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖Function.update (coordinateHybrid s x y) j (x j + t*(y j-x j)) - x‖ ≤ ‖y-x‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  by_cases hk : k = j
  · subst k
    simp only [Pi.sub_apply, Function.update_self, add_sub_cancel_left, norm_mul]
    have ht' : ‖t‖ ≤ 1 := by simpa [Real.norm_eq_abs, abs_of_nonneg ht.1] using ht.2
    exact (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans (by
      simpa only [one_mul, Pi.sub_apply] using norm_le_pi_norm (y-x) j)
  · rw [Pi.sub_apply, Function.update_of_ne hk]
    by_cases hks : k ∈ s
    · simpa [coordinateHybrid, hks, Pi.sub_apply] using norm_le_pi_norm (y-x) k
    · simp [coordinateHybrid, hks]

private theorem coordinate_edge_error {m : ℕ} (f : (Fin m → ℝ) → ℝ)
    (d : (Fin m → ℝ) → Fin m → ℝ)
    (hd : ∀ b j c, HasDerivAt (fun t => f (Function.update b j t)) (d (Function.update b j c) j) c)
    (s : Finset (Fin m)) (x y : Fin m → ℝ) (j : Fin m) (hj : j ∉ s)
    (η : ℝ) (hη : 0 ≤ η)
    (hb : ∀ z, ‖z-x‖ ≤ ‖y-x‖ → ∀ k, |d z k-d x k| ≤ η) :
    |f (coordinateHybrid (insert j s) x y) - f (coordinateHybrid s x y) -
      d x j * (y j-x j)| ≤ η*‖y-x‖ := by
  let b := coordinateHybrid s x y
  let a := y j-x j
  let g (t : ℝ) := f (Function.update b j (x j+t*a)) - (d x j)*(t*a)
  have hg (t : ℝ) : HasDerivAt g ((d (Function.update b j (x j+t*a)) j-d x j)*a) t := by
    have ha : HasDerivAt (fun t : ℝ => x j+t*a) a t := by
      simpa using ((hasDerivAt_id t).mul_const a).const_add (x j)
    convert ((hd b j (x j+t*a)).comp t ha).sub
      (((hasDerivAt_id t).mul_const a).const_mul (d x j)) using 1 <;> dsimp [g] <;> ring
  have hgBound (t : ℝ) (ht : t ∈ Ico (0 : ℝ) 1) :
      ‖(d (Function.update b j (x j+t*a)) j-d x j)*a‖ ≤ η*‖y-x‖ := by
    rw [norm_mul, Real.norm_eq_abs (d _ _-d _ _)]
    exact mul_le_mul (hb _ (coordinateHybrid_path_norm s x y j hj ⟨ht.1, ht.2.le⟩) j)
      (by simpa [a, Pi.sub_apply] using norm_le_pi_norm (y-x) j) (norm_nonneg _) hη
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (_ : t ∈ Icc (0 : ℝ) 1) => (hg t).hasDerivWithinAt) hgBound 1 (by simp)
  have hx : Function.update b j (x j) = b := by
    have he : b j = x j := by simp [b, coordinateHybrid, hj]
    rw [← he, Function.update_eq_self]
  have hh' : |f (Function.update b j (y j)) - d x j*(y j-x j) - f b| ≤ η*‖y-x‖ := by
    simpa [g, a, hx, Real.norm_eq_abs] using hh
  rw [coordinateHybrid_insert]
  change |f (Function.update b j (y j)) - f b - d x j*(y j-x j)| ≤ _
  convert hh' using 1 <;> congr 1 <;> ring

/-- Genuine coordinate derivatives and continuity of their values imply a
Fréchet derivative. The conclusion is the actual finite sum of partials. -/
theorem hasFDerivAt_of_continuous_coordinate_derivatives {m : ℕ}
    (f : (Fin m → ℝ) → ℝ) (d : (Fin m → ℝ) → Fin m → ℝ)
    (hd : ∀ b j c, HasDerivAt (fun t => f (Function.update b j t)) (d (Function.update b j c) j) c)
    (hc : ∀ j, Continuous (fun b => d b j)) (x : Fin m → ℝ) :
    HasFDerivAt f (∑ j, (d x j) • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
  apply HasFDerivAtFilter.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let η := ε / (m+1)
  have hm : (0 : ℝ) < m+1 := by positivity
  have hη : 0 < η := div_pos hε hm
  have hn : ∀ᶠ z in 𝓝 x, ∀ j, |d z j-d x j| < η := by
    rw [Filter.eventually_all]
    intro j
    exact ((hc j).continuousAt.sub continuousAt_const).abs.eventually_lt_const
      (by simpa using hη)
  obtain ⟨r, hr, hball⟩ := Metric.eventually_nhds_iff.mp hn
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hb : ∀ z, ‖z-x‖ ≤ ‖y-x‖ → ∀ j, |d z j-d x j| ≤ η := by
    intro z hz j
    have hy' : ‖y-x‖ < r := by simpa [Metric.mem_ball, dist_eq_norm] using hy
    have hz' : dist z x < r := by simpa [dist_eq_norm] using hz.trans_lt hy'
    exact (hball hz' j).le
  have hs (s : Finset (Fin m)) :
      |f (coordinateHybrid s x y)-f x-∑ j ∈ s, d x j*(y j-x j)| ≤ (s.card : ℝ)*η*‖y-x‖ := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [coordinateHybrid_empty]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj, Finset.card_insert_of_not_mem hj, Nat.cast_add, Nat.cast_one]
      have he := coordinate_edge_error f d hd s x y j hj η hη.le hb
      have ha : f (coordinateHybrid (insert j s) x y)-f x-
          (d x j*(y j-x j)+∑ k ∈ s, d x k*(y k-x k)) =
          (f (coordinateHybrid (insert j s) x y)-f (coordinateHybrid s x y)-d x j*(y j-x j)) +
          (f (coordinateHybrid s x y)-f x-∑ k ∈ s, d x k*(y k-x k)) := by ring
      rw [ha]
      exact (abs_add _ _).trans ((add_le_add he ih).trans_eq (by ring))
  have hh := hs Finset.univ
  simp only [coordinateHybrid_univ, Finset.card_univ, Fintype.card_fin] at hh
  have hcoef : (m : ℝ)*η ≤ ε := by dsimp [η]; rw [← mul_div_assoc]; apply (div_le_iff₀ hm).mpr; nlinarith
  have hmul := hh.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  simpa only [Real.norm_eq_abs, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul, Pi.sub_apply, Fintype.card_fin] using hmul

end
end RectangleCLT.Companion.SplitV4
