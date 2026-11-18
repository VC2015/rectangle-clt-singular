import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.FDeriv.Pi
import Mathlib.Analysis.Calculus.FDeriv.Prod

/-! Local genuine coordinate derivatives imply a genuine Fréchet derivative.
The finite hybrid-coordinate path stays in a ball contained in the given
open neighborhood. Derivative values need only be continuous at the base
point. No extension of the function or derivative is constructed. -/

namespace RectangleCLTArxivV1
open Filter Set
open scoped BigOperators Topology
noncomputable section

private def localCoordinateHybrid {m : ℕ} (s : Finset (Fin m))
    (x y : Fin m → ℝ) : Fin m → ℝ := fun j => if j ∈ s then y j else x j

private theorem localCoordinateHybrid_empty {m : ℕ} (x y : Fin m → ℝ) :
    localCoordinateHybrid ∅ x y=x := by ext j; simp [localCoordinateHybrid]

private theorem localCoordinateHybrid_univ {m : ℕ} (x y : Fin m → ℝ) :
    localCoordinateHybrid Finset.univ x y=y := by ext j; simp [localCoordinateHybrid]

private theorem localCoordinateHybrid_insert {m : ℕ} (s : Finset (Fin m))
    (x y : Fin m → ℝ) (j : Fin m) :
    localCoordinateHybrid (insert j s) x y=
      Function.update (localCoordinateHybrid s x y) j (y j) := by
  classical
  ext k
  by_cases hk : k=j
  · subst k
    simp [localCoordinateHybrid]
  · simp [localCoordinateHybrid,hk]

private theorem localCoordinateHybrid_path_norm {m : ℕ} (s : Finset (Fin m))
    (x y : Fin m → ℝ) (j : Fin m)
    {t : ℝ} (ht : t∈Icc (0 : ℝ) 1) :
    ‖Function.update (localCoordinateHybrid s x y) j (x j+t*(y j-x j))-x‖ ≤ ‖y-x‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg _)).mpr
  intro k
  by_cases hk : k=j
  · subst k
    simp only [Pi.sub_apply,Function.update_self,add_sub_cancel_left,norm_mul]
    have ht' : ‖t‖≤1 := by simpa [Real.norm_eq_abs,abs_of_nonneg ht.1] using ht.2
    exact (mul_le_mul_of_nonneg_right ht' (norm_nonneg _)).trans (by
      simpa only [one_mul,Pi.sub_apply] using norm_le_pi_norm (y-x) j)
  · rw [Pi.sub_apply,Function.update_of_ne hk]
    by_cases hks : k∈s
    · simpa [localCoordinateHybrid,hks,Pi.sub_apply] using norm_le_pi_norm (y-x) k
    · simp [localCoordinateHybrid,hks]

private theorem localCoordinate_edge_error {m : ℕ}
    (f : (Fin m → ℝ) → ℝ) (d : (Fin m → ℝ) → Fin m → ℝ)
    (U : Set (Fin m → ℝ))
    (hd : ∀ b∈U, ∀ j, HasDerivAt (fun t => f (Function.update b j t)) (d b j) (b j))
    (s : Finset (Fin m)) (x y : Fin m → ℝ) (j : Fin m) (hj : j∉s)
    (η : ℝ) (hη : 0≤η)
    (hU : ∀ z, ‖z-x‖≤‖y-x‖ → z∈U)
    (hb : ∀ z, ‖z-x‖≤‖y-x‖ → ∀ k, |d z k-d x k|≤η) :
    |f (localCoordinateHybrid (insert j s) x y)-f (localCoordinateHybrid s x y)-
      d x j*(y j-x j)| ≤ η*‖y-x‖ := by
  let b := localCoordinateHybrid s x y
  let a := y j-x j
  let g (t : ℝ) := f (Function.update b j (x j+t*a))-(d x j)*(t*a)
  have hg (t : ℝ) (ht : t∈Icc (0 : ℝ) 1) :
      HasDerivAt g ((d (Function.update b j (x j+t*a)) j-d x j)*a) t := by
    have hq : Function.update b j (x j+t*a)∈U :=
      hU _ (localCoordinateHybrid_path_norm s x y j ht)
    have hlocal : HasDerivAt (fun c => f (Function.update b j c))
        (d (Function.update b j (x j+t*a)) j) (x j+t*a) := by
      simpa only [Function.update_self,Function.update_idem] using
        hd (Function.update b j (x j+t*a)) hq j
    have ha : HasDerivAt (fun t : ℝ => x j+t*a) a t := by
      simpa using ((hasDerivAt_id t).mul_const a).const_add (x j)
    convert (hlocal.comp t ha).sub
      (((hasDerivAt_id t).mul_const a).const_mul (d x j)) using 1 <;> dsimp [g] <;> ring
  have hgBound (t : ℝ) (ht : t∈Ico (0 : ℝ) 1) :
      ‖(d (Function.update b j (x j+t*a)) j-d x j)*a‖ ≤ η*‖y-x‖ := by
    rw [norm_mul,Real.norm_eq_abs (d _ _-d _ _)]
    exact mul_le_mul (hb _ (localCoordinateHybrid_path_norm s x y j ⟨ht.1,ht.2.le⟩) j)
      (by simpa [a,Pi.sub_apply] using norm_le_pi_norm (y-x) j) (norm_nonneg _) hη
  have hh := norm_image_sub_le_of_norm_deriv_le_segment'
    (fun t (ht : t∈Icc (0 : ℝ) 1) => (hg t ht).hasDerivWithinAt) hgBound 1 (by simp)
  have hx : Function.update b j (x j)=b := by
    have he : b j=x j := by simp [b,localCoordinateHybrid,hj]
    rw [← he,Function.update_eq_self]
  have hh' : |f (Function.update b j (y j))-d x j*(y j-x j)-f b| ≤ η*‖y-x‖ := by
    simpa [g,a,hx,Real.norm_eq_abs] using hh
  rw [localCoordinateHybrid_insert]
  change |f (Function.update b j (y j))-f b-d x j*(y j-x j)| ≤ _
  convert hh' using 1 <;> congr 1 <;> ring

/-- Local coordinate derivatives and continuity of their values at `x`
give the actual Fréchet derivative at `x`. Every derivative invoked in
the proof is at a point of the supplied open neighborhood `U`. -/
theorem hasFDerivAt_of_local_continuous_coordinate_derivatives {m : ℕ}
    (f : (Fin m → ℝ) → ℝ) (d : (Fin m → ℝ) → Fin m → ℝ)
    (x : Fin m → ℝ) (U : Set (Fin m → ℝ)) (hU : IsOpen U) (hx : x∈U)
    (hd : ∀ b∈U, ∀ j, HasDerivAt (fun t => f (Function.update b j t)) (d b j) (b j))
    (hc : ∀ j, ContinuousAt (fun b => d b j) x) :
    HasFDerivAt f
      (∑ j, d x j • (ContinuousLinearMap.proj j : (Fin m → ℝ) →L[ℝ] ℝ)) x := by
  apply HasFDerivAtFilter.of_isLittleO
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  let η := ε/(m+1)
  have hm : (0 : ℝ)<m+1 := by positivity
  have hη : 0<η := div_pos hε hm
  have hn : ∀ᶠ z in 𝓝 x, ∀ j, |d z j-d x j|<η := by
    rw [Filter.eventually_all]
    intro j
    exact ((hc j).sub continuousAt_const).abs.eventually_lt_const (by simpa using hη)
  have hnU : ∀ᶠ z in 𝓝 x, z∈U := hU.mem_nhds hx
  obtain ⟨r,hr,hball⟩ := Metric.eventually_nhds_iff.mp (hnU.and hn)
  filter_upwards [Metric.ball_mem_nhds x hr] with y hy
  have hlocal : ∀ z, ‖z-x‖≤‖y-x‖ → z∈U ∧ ∀ j, |d z j-d x j|≤η := by
    intro z hz
    have hy' : ‖y-x‖<r := by simpa [Metric.mem_ball,dist_eq_norm] using hy
    have hz' : dist z x<r := by simpa [dist_eq_norm] using hz.trans_lt hy'
    exact ⟨(hball hz').1,fun j => ((hball hz').2 j).le⟩
  have hs (s : Finset (Fin m)) :
      |f (localCoordinateHybrid s x y)-f x-∑ j∈s, d x j*(y j-x j)| ≤
        (s.card : ℝ)*η*‖y-x‖ := by
    classical
    induction s using Finset.induction_on with
    | empty => simp [localCoordinateHybrid_empty]
    | @insert j s hj ih =>
      rw [Finset.sum_insert hj,Finset.card_insert_of_not_mem hj,Nat.cast_add,Nat.cast_one]
      have he := localCoordinate_edge_error f d U hd s x y j hj η hη.le
        (fun z hz => (hlocal z hz).1) (fun z hz => (hlocal z hz).2)
      have ha : f (localCoordinateHybrid (insert j s) x y)-f x-
          (d x j*(y j-x j)+∑ k∈s, d x k*(y k-x k)) =
          (f (localCoordinateHybrid (insert j s) x y)-f (localCoordinateHybrid s x y)-d x j*(y j-x j))+
          (f (localCoordinateHybrid s x y)-f x-∑ k∈s, d x k*(y k-x k)) := by ring
      rw [ha]
      exact (abs_add _ _).trans ((add_le_add he ih).trans_eq (by ring))
  have hh := hs Finset.univ
  simp only [localCoordinateHybrid_univ,Finset.card_univ,Fintype.card_fin] at hh
  have hcoef : (m : ℝ)*η≤ε := by
    dsimp [η]
    rw [← mul_div_assoc]
    apply (div_le_iff₀ hm).mpr
    nlinarith
  have hmul := hh.trans (mul_le_mul_of_nonneg_right hcoef (norm_nonneg _))
  simpa only [Real.norm_eq_abs,ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.proj_apply,smul_eq_mul,Pi.sub_apply,Fintype.card_fin] using hmul

end
end RectangleCLTArxivV1
