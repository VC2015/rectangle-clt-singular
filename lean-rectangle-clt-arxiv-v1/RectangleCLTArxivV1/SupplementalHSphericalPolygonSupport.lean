import RectangleCLTArxivV1.SupplementalHPositiveWedge
import Mathlib.Analysis.Convex.Cone.Basic

/-! Actual support faces of a finite generated normal cone. The vanishing
coefficients are proved from positivity; no face angle or balance formula is
assumed. The two-endpoint result applies to any number of generators. -/
namespace RectangleCLTArxivV1
open Set
open scoped BigOperators
noncomputable section
set_option autoImplicit false

variable {E : Type*} [AddCommGroup E] [Module ℝ E]
/-- The actual cone of finite nonnegative combinations of the given rays. -/
def sphericalPolygonGeneratedCone {m : ℕ} (v : Fin m → E) : Set E :=
  {x | ∃ a : Fin m → ℝ, (∀ i,0≤a i) ∧ x=∑ i,a i • v i}

theorem sphericalPolygonGeneratedCone_generator_mem {m : ℕ}
    (v : Fin m → E) (j : Fin m) : v j∈sphericalPolygonGeneratedCone v := by
  classical
  refine ⟨Pi.single j 1,?_,?_⟩
  · intro i
    by_cases h : i=j <;> simp [Pi.single_apply,h]
  · simp [Pi.single_apply,ite_smul]

theorem sphericalPolygonGeneratedCone_add_mem {m : ℕ}
    (v : Fin m → E) {x y : E}
    (hx : x∈sphericalPolygonGeneratedCone v) (hy : y∈sphericalPolygonGeneratedCone v) :
    x+y∈sphericalPolygonGeneratedCone v := by
  rcases hx with ⟨a,ha,rfl⟩
  rcases hy with ⟨b,hb,rfl⟩
  refine ⟨fun i => a i+b i,fun i => add_nonneg (ha i) (hb i),?_⟩
  simp only [add_smul,Finset.sum_add_distrib]

theorem sphericalPolygonGeneratedCone_smul_mem {m : ℕ}
    (v : Fin m → E) {x : E} (hx : x∈sphericalPolygonGeneratedCone v)
    (t : ℝ) (ht : 0≤t) : t • x∈sphericalPolygonGeneratedCone v := by
  rcases hx with ⟨a,ha,rfl⟩
  refine ⟨fun i => t*a i,fun i => mul_nonneg ht (ha i),?_⟩
  simp only [Finset.smul_sum,smul_smul]

theorem sphericalPolygonGeneratedCone_linear_nonneg {m : ℕ}
    (v : Fin m → E) (L : E →ₗ[ℝ] ℝ) (hL : ∀ i,0≤L (v i))
    {x : E} (hx : x∈sphericalPolygonGeneratedCone v) : 0≤L x := by
  rcases hx with ⟨a,ha,rfl⟩
  simp only [map_sum,map_smul,smul_eq_mul]
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (ha i) (hL i))

/-- A support face retains exactly coefficients of generators in the
supporting plane. This is a consequence of the actual nonnegative sum. -/
theorem sphericalPolygonGeneratedCone_zero_face_coefficients {m : ℕ}
    (v : Fin m → E) (L : E →ₗ[ℝ] ℝ) (hL : ∀ i,0≤L (v i)) :
    {x | x∈sphericalPolygonGeneratedCone v ∧ L x=0}=
      {x | ∃ a : Fin m → ℝ,(∀ i,0≤a i) ∧
        (∀ i,L (v i)≠0 → a i=0) ∧ x=∑ i,a i • v i} := by
  ext x
  constructor
  · rintro ⟨⟨a,ha,hx⟩,hz⟩
    have hs : (∑ i,a i*L (v i))=0 := by
      rw [hx] at hz
      simpa only [map_sum,map_smul,smul_eq_mul] using hz
    refine ⟨a,ha,?_,hx⟩
    intro i hi
    have hi0 : a i*L (v i)=0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun k _ => mul_nonneg (ha k) (hL k))).mp hs
        i (Finset.mem_univ i)
    exact (mul_eq_zero.mp hi0).resolve_right hi
  · rintro ⟨a,ha,hzero,hx⟩
    refine ⟨⟨a,ha,hx⟩,?_⟩
    rw [hx,map_sum]
    apply Finset.sum_eq_zero
    intro i _
    by_cases hi : L (v i)=0
    · simp [hi]
    · simp [hzero i hi]

/-- If precisely the two actual endpoint generators lie in the
supporting plane, its cone face is their actual positive planar wedge. -/
theorem sphericalPolygonGeneratedCone_zero_face_eq_wedge {m : ℕ}
    (v : Fin m → E) (L : E →ₗ[ℝ] ℝ) (a b : Fin m) (hab : a≠b)
    (ha : L (v a)=0) (hb : L (v b)=0)
    (hstrict : ∀ i,i≠a → i≠b → 0<L (v i)) :
    {x | x∈sphericalPolygonGeneratedCone v ∧ L x=0}=positivePlanarWedge (v a) (v b) := by
  classical
  have hL (i : Fin m) : 0≤L (v i) := by
    by_cases hia : i=a
    · simp [hia,ha]
    by_cases hib : i=b
    · simp [hib,hb]
    exact (hstrict i hia hib).le
  rw [sphericalPolygonGeneratedCone_zero_face_coefficients v L hL]
  ext x
  constructor
  · rintro ⟨c,hc,hzero,hx⟩
    refine ⟨c a,c b,hc a,hc b,?_⟩
    rw [hx]
    calc
      (∑ i,c i • v i)=∑ i∈({a,b} : Finset (Fin m)),c i • v i := by
        symm
        apply Finset.sum_subset (Finset.subset_univ _)
        intro i _ hi
        have hia : i≠a := by
          intro h
          exact hi (by simp [h])
        have hib : i≠b := by
          intro h
          exact hi (by simp [h])
        rw [hzero i (hstrict i hia hib).ne',zero_smul]
      _=c a • v a+c b • v b := by simp [hab]
  · rintro ⟨c,d,hc,hd,rfl⟩
    have hmem := sphericalPolygonGeneratedCone_add_mem v
      (sphericalPolygonGeneratedCone_smul_mem v
        (sphericalPolygonGeneratedCone_generator_mem v a) c hc)
      (sphericalPolygonGeneratedCone_smul_mem v
        (sphericalPolygonGeneratedCone_generator_mem v b) d hd)
    have hz : L (c • v a+d • v b)=0 := by simp [ha,hb]
    exact (Set.ext_iff.mp (sphericalPolygonGeneratedCone_zero_face_coefficients v L hL)
      (c • v a+d • v b)).mp ⟨hmem,hz⟩

end
end RectangleCLTArxivV1
