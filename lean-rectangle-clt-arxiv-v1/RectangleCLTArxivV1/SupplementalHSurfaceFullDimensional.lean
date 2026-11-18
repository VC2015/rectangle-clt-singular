import RectangleCLTArxivV1.SupplementalHSurfaceMain

/-! The geometric full-dimensional hypothesis is exactly a strict
interior witness for a finite family of unit-normal inequalities. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped Topology
noncomputable section

theorem hasStrictFacetInterior_of_nonempty_interior {m r : ℕ} (u : Fin m → Vector r)
    (b : Vector m) (hu : ∀ j,vectorNormSq (u j)=1)
    (hint : (interior (gaussianFiniteThresholdEvent Finset.univ u b)).Nonempty) :
    HasStrictFacetInterior u b := by
  obtain ⟨x,hx⟩ := hint
  have hnear : gaussianFiniteThresholdEvent Finset.univ u b∈𝓝 x := mem_interior_iff_mem_nhds.mp hx
  refine ⟨x,fun j => ?_⟩
  have ht : Tendsto (fun t : ℝ => x+t • u j) (𝓝 0) (𝓝 x) := by
    simpa only [id_eq,zero_smul,add_zero] using
      (((continuous_const.add (continuous_id.smul continuous_const)).continuousAt :
        ContinuousAt (fun t : ℝ => x+t • u j) 0).tendsto)
  have he := ht.eventually hnear
  obtain ⟨ε,hε,hball⟩ := Metric.eventually_nhds_iff.mp he
  have hp : ε/2>0 := by positivity
  have hg : x+(ε/2) • u j∈gaussianFiniteThresholdEvent Finset.univ u b := hball
    (by simpa only [dist_zero_right,Real.norm_eq_abs,abs_of_pos hp] using (show ε/2<ε by linarith))
  have hj := hg j (Finset.mem_univ _)
  have hself : faceDot (u j) (u j)=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hu j
  rw [threshold_faceDot_add_right,threshold_faceDot_smul_right,hself,mul_one] at hj
  linarith

theorem HasStrictFacetInterior.nonempty_interior {m r : ℕ} {u : Fin m → Vector r} {b : Vector m}
    (h : HasStrictFacetInterior u b) :
    (interior (gaussianFiniteThresholdEvent Finset.univ u b)).Nonempty := by
  obtain ⟨x,hx⟩ := h
  let O := {y : Vector r | ∀ j,faceDot (u j) y<b j}
  have hO : IsOpen O := by
    simp only [O,setOf_forall]
    exact isOpen_iInter_of_finite (fun j => isOpen_lt (continuous_faceDot_left _) continuous_const)
  refine ⟨x,mem_interior_iff_mem_nhds.mpr ?_⟩
  apply Filter.mem_of_superset (hO.mem_nhds hx)
  intro y hy j _
  exact (hy j).le

end
end RectangleCLTArxivV1
