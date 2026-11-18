import RectangleCLTArxivV1.SupplementalHSphericalPolygonSupport
import RectangleCLTArxivV1.SupplementalHSphericalPolygonChart

/-! Arbitrary-edge generated normal-cone balance. Actual support incidences
determine every planar edge and its angle. Pairwise nonparallelism follows
from distinct endpoint pairs and strict support signs. The remaining cone
presentation premise is geometric, with no area or balance premise. -/
namespace RectangleCLTArxivV1
open MeasureTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section
set_option autoImplicit false
set_option maxHeartbeats 1000000
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Actual inward spherical conormals, expressed as outward halfspace
normals in the archived coordinate model. -/
def sphericalPolygonOutwardNormals {q : ℕ} (n : Fin q → E3) (e : Fin q) : Vector 3 :=
  WithLp.equiv 2 (Vector 3) (-n e)

theorem sphericalPolygonOutwardNormals_dot {q : ℕ} (n : Fin q → E3)
    (e : Fin q) (x : E3) :
    faceDot (sphericalPolygonOutwardNormals n e) (WithLp.equiv 2 (Vector 3) x)=
      -⟪n e,x⟫_ℝ := by
  rw [faceDot_eq_euclidean_inner]
  exact inner_neg_left (n e) x

theorem sphericalPolygonOutwardNormals_unit {q : ℕ} (n : Fin q → E3)
    (hn : ∀ e,‖n e‖=1) (e : Fin q) :
    vectorNormSq (sphericalPolygonOutwardNormals n e)=1 := by
  rw [sphericalPolygonOutwardNormals,supplementalH_vectorNormSq_equiv,norm_neg,hn,one_pow]

/-- Genuine strict relative-interior facet points rule out parallel or
duplicate supporting normals; ambient full dimension by itself would not. -/
theorem sphericalPolygon_nonparallel_of_strict_facets {q r : ℕ}
    (u : Fin q → Vector r)
    (hfacet : ∀ e,∃ x : Vector r,faceDot (u e) x=0 ∧
      ∀ f,f≠e → faceDot (u f) x<0) : PairwiseNonparallelNormals u := by
  intro e f hfe hz
  obtain ⟨x,he,hf⟩ := hfacet e
  have hh := congrArg (fun w : Vector r => faceDot w x) (sub_eq_zero.mp hz)
  dsimp only at hh
  rw [threshold_faceDot_smul_left,he,mul_zero] at hh
  exact (hf f hfe).ne hh

theorem sphericalPolygon_distinct_endpoint_pair {m q : ℕ}
    (a b : Fin q → Fin m) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (e f : Fin q) (hef : e≠f) :
    (a e≠a f ∧ a e≠b f) ∨ (b e≠a f ∧ b e≠b f) := by
  classical
  by_cases haa : a e=a f
  · by_cases hbb : b e=b f
    · exact False.elim (hef (hinj (by simp [haa,hbb])))
    · exact Or.inr ⟨fun h => hab e (haa.trans h.symm),hbb⟩
  · by_cases hab' : a e=b f
    · by_cases hba : b e=a f
      · exact False.elim (hef (hinj (by simp [hab',hba,Finset.pair_comm])))
      · exact Or.inr ⟨hba,fun h => hab e (hab'.trans h.symm)⟩
    · exact Or.inl ⟨haa,hab'⟩

/-- Support signs at all generators produce an actual relative-interior
point on every facet: the sum of its two endpoint rays. -/
theorem sphericalPolygon_strict_facets_of_incidence {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ) :
    ∀ e,∃ x : Vector 3,faceDot (sphericalPolygonOutwardNormals n e) x=0 ∧
      ∀ f,f≠e → faceDot (sphericalPolygonOutwardNormals n f) x<0 := by
  have hnonneg (f : Fin q) (i : Fin m) : 0≤⟪n f,v i⟫_ℝ := by
    by_cases ha : i=a f
    · simp [ha,(hzero f).1]
    by_cases hb : i=b f
    · simp [hb,(hzero f).2]
    exact (hstrict f i ha hb).le
  intro e
  refine ⟨WithLp.equiv 2 (Vector 3) (v (a e)+v (b e)),?_,?_⟩
  · rw [sphericalPolygonOutwardNormals_dot,inner_add_right,(hzero e).1,(hzero e).2]
    ring
  · intro f hfe
    rw [sphericalPolygonOutwardNormals_dot,inner_add_right]
    have hp : 0<⟪n f,v (a e)⟫_ℝ+⟪n f,v (b e)⟫_ℝ := by
      rcases sphericalPolygon_distinct_endpoint_pair a b hab hinj e f hfe.symm with h | h
      · exact add_pos_of_pos_of_nonneg (hstrict f _ h.1 h.2) (hnonneg f _)
      · exact add_pos_of_nonneg_of_pos (hnonneg f _) (hstrict f _ h.1 h.2)
    exact neg_neg_of_pos hp

theorem sphericalPolygonOutwardNormals_nonparallel {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ) :
    PairwiseNonparallelNormals (sphericalPolygonOutwardNormals n) :=
  sphericalPolygon_nonparallel_of_strict_facets _
    (sphericalPolygon_strict_facets_of_incidence v a b n hab hinj hzero hstrict)

/-- The actual support-face equality is proved by coefficient positivity,
then the actual tangent chart supplies the ordinary endpoint angle. -/
theorem sphericalPolygon_generated_facet_angular_area {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1)
    (hab : ∀ e,a e≠b e)
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (e : Fin q) :
    (volume : Measure (EuclideanSpace ℝ (Fin 2))).toSphere.real
      (supplementalHSphericalSection (sphericalPolygonFacetChart
        (sphericalPolygonGeneratedCone v) (sphericalPolygonOutwardNormals n e)))=
      Real.arccos ⟪v (a e),v (b e)⟫_ℝ := by
  let L : E3 →ₗ[ℝ] ℝ := (innerSL ℝ (n e)).toLinearMap
  have hface := sphericalPolygonGeneratedCone_zero_face_eq_wedge v L (a e) (b e) (hab e)
    (hzero e).1 (hzero e).2 (hstrict e)
  have hface' : {x : E3 | x∈sphericalPolygonGeneratedCone v ∧
      faceDot (sphericalPolygonOutwardNormals n e) (WithLp.equiv 2 (Vector 3) x)=0}=
      positivePlanarWedge (v (a e)) (v (b e)) := by
    simpa only [sphericalPolygonOutwardNormals_dot,neg_eq_zero] using hface
  apply sphericalPolygonFacetChart_angular_area _ _
    (sphericalPolygonOutwardNormals_unit n hn e) _ _ (hv _) (hv _)
    (by rw [sphericalPolygonOutwardNormals_dot,(hzero e).1,neg_zero])
    (by rw [sphericalPolygonOutwardNormals_dot,(hzero e).2,neg_zero])
    (hp e) (hm e) hface'

/-- A proved geometric halfspace description identifies the actual finite
generated cone with the cone used in the Gaussian/spherical balance. -/
theorem sphericalPolygonGeneratedCone_eq_halfspaces {m q : ℕ}
    (v : Fin m → E3) (n : Fin q → E3)
    (hhalf : ∀ x,x∈sphericalPolygonGeneratedCone v ↔ ∀ e,0≤⟪n e,x⟫_ℝ) :
    sphericalPolygonGeneratedCone v=
      supplementalHPolyhedralCone (sphericalPolygonOutwardNormals n) := by
  ext x
  rw [hhalf]
  change (∀ e,0≤⟪n e,x⟫_ℝ) ↔ ∀ e∈Finset.univ,
    faceDot (sphericalPolygonOutwardNormals n e) (WithLp.equiv 2 (Vector 3) x)≤0
  simp only [Finset.mem_univ,forall_const,sphericalPolygonOutwardNormals_dot,neg_nonpos]

theorem sphericalPolygon_generated_facet_angle {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hhalf : ∀ x,x∈sphericalPolygonGeneratedCone v ↔ ∀ e,0≤⟪n e,x⟫_ℝ)
    (e : Fin q) :
    supplementalHFacetAngle (sphericalPolygonOutwardNormals n) e=
      Real.arccos ⟪v (a e),v (b e)⟫_ℝ := by
  have hchart : sphericalPolygonFacetChart (sphericalPolygonGeneratedCone v)
      (sphericalPolygonOutwardNormals n e)=
      supplementalHFacetCone (sphericalPolygonOutwardNormals n) e := by
    rw [sphericalPolygonGeneratedCone_eq_halfspaces v n hhalf]
    rfl
  unfold supplementalHFacetAngle
  rw [←hchart]
  exact sphericalPolygon_generated_facet_angular_area v a b n hv hn hab hzero hstrict hp hm e

theorem sphericalPolygonOutwardNormals_inward {q : ℕ} (n : Fin q → E3) (e : Fin q) :
    -((WithLp.equiv 2 (Vector 3)).symm (sphericalPolygonOutwardNormals n e))=n e := by
  unfold sphericalPolygonOutwardNormals
  rw [Equiv.symm_apply_apply,neg_neg]

/-- Actual spherical polygon balance for any finite number of edges.
The ordinary endpoint angles and signed inward conormals are retained.
The hypotheses are actual generator/facet incidence and the complete
geometric halfspace presentation; no balance, angular mass, or area bound
is assumed. -/
theorem sphericalPolygon_generated_balance {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hhalf : ∀ x,x∈sphericalPolygonGeneratedCone v ↔ ∀ e,0≤⟪n e,x⟫_ℝ) :
    (∑ e,Real.arccos ⟪v (a e),v (b e)⟫_ℝ • n e)=
      (2 : ℝ) • ∫ ω in supplementalHSphericalSection (sphericalPolygonGeneratedCone v),
        ω.1 ∂(volume : Measure E3).toSphere := by
  have hh := supplementalH_spherical_balance_inward (sphericalPolygonOutwardNormals n)
    (sphericalPolygonOutwardNormals_unit n hn)
    (sphericalPolygonOutwardNormals_nonparallel v a b n hab hinj hzero hstrict)
  simp_rw [sphericalPolygon_generated_facet_angle v a b n hv hn hab hzero hstrict hp hm hhalf,
    sphericalPolygonOutwardNormals_inward] at hh
  rw [←sphericalPolygonGeneratedCone_eq_halfspaces v n hhalf] at hh
  exact hh

theorem sphericalPolygon_generated_balance_norm_le {m q : ℕ}
    (v : Fin m → E3) (a b : Fin q → Fin m) (n : Fin q → E3)
    (hv : ∀ i,‖v i‖=1) (hn : ∀ e,‖n e‖=1) (hab : ∀ e,a e≠b e)
    (hinj : Function.Injective (fun e => ({a e,b e} : Finset (Fin m))))
    (hzero : ∀ e,⟪n e,v (a e)⟫_ℝ=0 ∧ ⟪n e,v (b e)⟫_ℝ=0)
    (hstrict : ∀ e i,i≠a e → i≠b e → 0<⟪n e,v i⟫_ℝ)
    (hp : ∀ e,v (a e)+v (b e)≠0) (hm : ∀ e,v (a e)-v (b e)≠0)
    (hhalf : ∀ x,x∈sphericalPolygonGeneratedCone v ↔ ∀ e,0≤⟪n e,x⟫_ℝ) :
    ‖∑ e,Real.arccos ⟪v (a e),v (b e)⟫_ℝ • n e‖≤
      2*(volume : Measure E3).toSphere.real
        (supplementalHSphericalSection (sphericalPolygonGeneratedCone v)) := by
  rw [sphericalPolygon_generated_balance v a b n hv hn hab hinj hzero hstrict hp hm hhalf,
    norm_smul,Real.norm_eq_abs,abs_of_pos (by norm_num : (0 : ℝ)<2)]
  exact mul_le_mul_of_nonneg_left (supplementalH_spherical_vectorIntegral_norm_le volume _)
    (by norm_num)

end
end RectangleCLTArxivV1
