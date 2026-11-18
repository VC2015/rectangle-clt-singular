import RectangleCLTArxivV1.SupplementalHFrameSections
import RectangleCLTArxivV1.SupplementalHPairSectionTrace
import RectangleCLTArxivV1.SupplementalHResidualPairMass
import RectangleCLTArxivV1.SupplementalHNormalPointUnique

/-! Actual Gaussian hard-section masses in three normal directions.
The raw third-face derivative retains its inverse residual scale; after
that scale is restored, the mass depends only on the normal space and
the actual affine normal point. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion.SplitV4
open RectangleCLT.Companion.SignedSurface
open scoped BigOperators InnerProductSpace
noncomputable section

/-- Actual Gaussian normal density times the actual remaining hard-event
probability on an affine orthonormal frame section. -/
def gaussianFrameHardMass {m r q : ℕ} (s : Finset (Fin m)) (u : Fin m → Vector r)
    (b : Vector m) (v : Fin q → EuclideanSpace ℝ (Fin r)) (a : Fin q → ℝ) : ℝ :=
  (∏ i, gaussianPDFReal 0 1 (a i))*(standardGaussian r).real
    {g | WithLp.equiv 2 (Vector r) (gaussianFrameSectionPoint v a
      ((WithLp.equiv 2 (Vector r)).symm g))∈gaussianFiniteThresholdEvent s u b}

theorem gaussianFrameHardMass_nonneg {m r q : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m)
    (v : Fin q → EuclideanSpace ℝ (Fin r)) (a : Fin q → ℝ) :
    0≤gaussianFrameHardMass s u b v a := by
  unfold gaussianFrameHardMass
  exact mul_nonneg (Finset.prod_nonneg (fun i _ => gaussianPDFReal_nonneg _ _ _)) measureReal_nonneg

/-- An actual hard-section mass is independent of its orthonormal frame
when the normal space and affine normal point agree. -/
theorem gaussianFrameHardMass_frame_independent {m r q : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v w : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (a c : Fin q → ℝ)
    (hspan : Submodule.span ℝ (Set.range v)=Submodule.span ℝ (Set.range w))
    (hz : (∑ i, a i • v i)=∑ i, c i • w i) :
    gaussianFrameHardMass s u b v a=gaussianFrameHardMass s u b w c := by
  unfold gaussianFrameHardMass
  rw [gaussianFrame_density_frame_independent v w hv hw a c hz]
  congr 1
  apply congrArg (fun P : Set (Vector r) => (standardGaussian r).real P)
  ext g
  simp only [mem_setOf_eq]
  rw [gaussianFrameSectionPoint_frame_independent v w hv hw a c hspan hz]

def nativeTripleFrame {r : ℕ} (e f h : Vector r) : Fin 3 → EuclideanSpace ℝ (Fin r) :=
  ![(WithLp.equiv 2 (Vector r)).symm e,(WithLp.equiv 2 (Vector r)).symm f,
    (WithLp.equiv 2 (Vector r)).symm h]

def nativeTripleLevels (a c d : ℝ) : Fin 3 → ℝ := ![a,c,d]

/-- The concrete three successive Gaussian sections are the actual
finite-frame affine section point, pointwise in the ambient Gaussian. -/
theorem gaussianFrameSectionPoint_native_triple {r : ℕ} (e f h : Vector r)
    (hef : faceDot e f=0) (heh : faceDot e h=0) (hfh : faceDot f h=0)
    (a c d : ℝ) (g : Vector r) :
    WithLp.equiv 2 (Vector r) (gaussianFrameSectionPoint (nativeTripleFrame e f h)
      (nativeTripleLevels a c d) ((WithLp.equiv 2 (Vector r)).symm g))=
      gaussianPairSectionPoint e f a c (gaussianSectionPoint h d g) := by
  have hdot (v : Vector r) (hvh : faceDot v h=0) :
      faceDot v (gaussianSectionPoint h d g)=faceDot v g := by
    rw [gaussianSectionPoint_eq,threshold_faceDot_add_right,threshold_faceDot_smul_right,
      hvh,mul_zero,add_zero]
  rw [gaussianPairSectionPoint_orthogonal_formula e f hef,
    hdot e heh,hdot f hfh,gaussianSectionPoint_eq]
  simp only [gaussianFrameSectionPoint,gaussianFrameProjection,nativeTripleFrame,
    nativeTripleLevels,Fin.sum_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,← faceDot_eq_euclidean_inner,
    WithLp.equiv_add,WithLp.equiv_sub,WithLp.equiv_smul,Equiv.apply_symm_apply]
  ext k
  simp only [Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  ring

theorem nativeTripleFrame_orthonormal {r : ℕ} (e f h : Vector r)
    (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hh : vectorNormSq h=1)
    (hef : faceDot e f=0) (heh : faceDot e h=0) (hfh : faceDot f h=0) :
    Orthonormal ℝ (nativeTripleFrame e f h) := by
  have hee : faceDot e e=1 := by simpa only [faceDot,vectorNormSq,pow_two] using he
  have hff : faceDot f f=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hf
  have hhh : faceDot h h=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hh
  have hfe : faceDot f e=0 := by rw [faceDot_comm]; exact hef
  have hhe : faceDot h e=0 := by rw [faceDot_comm]; exact heh
  have hhf : faceDot h f=0 := by rw [faceDot_comm]; exact hfh
  simp only [faceDot] at hee hff hhh hef heh hfh hfe hhe hhf
  rw [orthonormal_iff_ite]
  intro i j
  fin_cases i <;> fin_cases j <;>
    simp [nativeTripleFrame,Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons,
      ← faceDot_eq_euclidean_inner,hee,hff,hhh,hef,heh,hfh,hfe,hhe,hhf]

def hardPairThirdScale {m r : ℕ} (u : Fin m → Vector r) (e f : Vector r) (k : Fin m) : ℝ :=
  localFiniteThresholdScale (hardPairResidualNormals u e f) k

def hardPairThirdDirection {m r : ℕ} (u : Fin m → Vector r)
    (e f : Vector r) (k : Fin m) : Vector r :=
  localFiniteThresholdDirection (hardPairResidualNormals u e f) k

theorem hardPairThirdScale_pos {m r : ℕ} (u : Fin m → Vector r) (e f : Vector r)
    (k : Fin m) (hk : hardPairResidualNormal e f (u k)≠0) :
    0<hardPairThirdScale u e f k := Real.sqrt_pos.mpr (vectorNormSq_pos hk)

/-- Actual Gram--Schmidt of the selected third normal after the selected
orthonormal pair, requiring only that this third residual is nonzero. -/
theorem hardPairThirdDirection_geometry {m r : ℕ} (u : Fin m → Vector r)
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (k : Fin m) (hk : hardPairResidualNormal e f (u k)≠0) :
    vectorNormSq (hardPairThirdDirection u e f k)=1 ∧
      faceDot e (hardPairThirdDirection u e f k)=0 ∧
      faceDot f (hardPairThirdDirection u e f k)=0 := by
  let σ := hardPairThirdScale u e f k
  let w := hardPairResidualNormal e f (u k)
  have hσ : 0<σ := hardPairThirdScale_pos u e f k hk
  have hn : vectorNormSq w=σ^2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hdir : hardPairThirdDirection u e f k=σ⁻¹ • w := rfl
  rw [hdir]
  constructor
  · simp only [vectorNormSq,Pi.smul_apply,smul_eq_mul,mul_pow,← Finset.mul_sum]
    change σ⁻¹^2*vectorNormSq w=1
    rw [hn]
    field_simp
  · have ho := hardPairResidualNormal_orthogonal e f (u k) he hf hef
    constructor
    · rw [faceDot_comm,threshold_faceDot_smul_left,ho.1,mul_zero]
    · rw [faceDot_comm,threshold_faceDot_smul_left,ho.2,mul_zero]

theorem hardPairThirdFrame_orthonormal {m r : ℕ} (u : Fin m → Vector r)
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (k : Fin m) (hk : hardPairResidualNormal e f (u k)≠0) :
    Orthonormal ℝ (nativeTripleFrame e f (hardPairThirdDirection u e f k)) := by
  obtain ⟨hh,heh,hfh⟩ := hardPairThirdDirection_geometry u e f he hf hef k hk
  exact nativeTripleFrame_orthonormal e f _ he hf hh hef heh hfh

theorem hardPairResidualNormal_eq_sub {r : ℕ} (e f v : Vector r) (hef : faceDot e f=0) :
    hardPairResidualNormal e f v=v-faceDot v e • e-faceDot v f • f := by
  have hd : faceDot (gaussianNormalProjection e v) f=faceDot v f := by
    rw [gaussianNormalProjection,threshold_faceDot_sub_left,threshold_faceDot_smul_left,
      hef,mul_zero,sub_zero]
  change gaussianNormalProjection e v-faceDot (gaussianNormalProjection e v) f • f=_
  rw [hd]
  rfl

/-- The actual Gram--Schmidt frame spans exactly the original selected
three-normal space, rather than an unrelated orthonormal space. -/
theorem hardPairThirdFrame_span {m r : ℕ} (u : Fin m → Vector r)
    (e f : Vector r) (hef : faceDot e f=0) (k : Fin m)
    (hk : hardPairResidualNormal e f (u k)≠0) :
    Submodule.span ℝ (Set.range (nativeTripleFrame e f (hardPairThirdDirection u e f k)))=
      Submodule.span ℝ (Set.range (nativeTripleFrame e f (u k))) := by
  let σ := hardPairThirdScale u e f k
  let h := hardPairThirdDirection u e f k
  let S := Submodule.span ℝ (Set.range (nativeTripleFrame e f h))
  let T := Submodule.span ℝ (Set.range (nativeTripleFrame e f (u k)))
  have heS : (WithLp.equiv 2 (Vector r)).symm e∈S := Submodule.subset_span ⟨0,by simp [nativeTripleFrame]⟩
  have hfS : (WithLp.equiv 2 (Vector r)).symm f∈S := Submodule.subset_span ⟨1,by simp [nativeTripleFrame]⟩
  have hhS : (WithLp.equiv 2 (Vector r)).symm h∈S := Submodule.subset_span ⟨2,by simp [nativeTripleFrame]⟩
  have heT : (WithLp.equiv 2 (Vector r)).symm e∈T := Submodule.subset_span ⟨0,by simp [nativeTripleFrame]⟩
  have hfT : (WithLp.equiv 2 (Vector r)).symm f∈T := Submodule.subset_span ⟨1,by simp [nativeTripleFrame]⟩
  have hkT : (WithLp.equiv 2 (Vector r)).symm (u k)∈T := Submodule.subset_span ⟨2,by simp [nativeTripleFrame]⟩
  have hσ : 0<σ := hardPairThirdScale_pos u e f k hk
  have hw : hardPairResidualNormal e f (u k)=σ • h := by
    change hardPairResidualNormal e f (u k)=σ • (σ⁻¹ • hardPairResidualNormal e f (u k))
    rw [smul_smul,mul_inv_cancel₀ hσ.ne',one_smul]
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact heT
    · exact hfT
    · change (WithLp.equiv 2 (Vector r)).symm (σ⁻¹ • hardPairResidualNormal e f (u k))∈T
      rw [WithLp.equiv_symm_smul]
      apply T.smul_mem
      rw [hardPairResidualNormal_eq_sub e f (u k) hef]
      simp only [WithLp.equiv_symm_sub,WithLp.equiv_symm_smul]
      exact T.sub_mem (T.sub_mem hkT (T.smul_mem _ heT)) (T.smul_mem _ hfT)
  · apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    fin_cases i
    · exact heS
    · exact hfS
    · change (WithLp.equiv 2 (Vector r)).symm (u k)∈S
      have hraw : u k=faceDot (u k) e • e+faceDot (u k) f • f+σ • h := by
        rw [←hw,hardPairResidualNormal_eq_sub e f (u k) hef]
        abel
      rw [hraw]
      simp only [WithLp.equiv_symm_add,WithLp.equiv_symm_smul]
      exact S.add_mem (S.add_mem (S.smul_mem _ heS) (S.smul_mem _ hfS)) (S.smul_mem _ hhS)

/-- The actual Gram--Schmidt section lies on all three selected affine
supporting planes, for every residual Gaussian point. -/
theorem hardPairThirdSection_selected_levels {m r : ℕ}
    (u : Fin m → Vector r) (b : Vector m) (e f : Vector r)
    (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (a c : ℝ) (k : Fin m) (hk : hardPairResidualNormal e f (u k)≠0) (g : Vector r) :
    let h := hardPairThirdDirection u e f k
    let t := hardPairResidualLevels u b e f a c k/hardPairThirdScale u e f k
    let x := gaussianPairSectionPoint e f a c (gaussianSectionPoint h t g)
    faceDot e x=a ∧ faceDot f x=c ∧ faceDot (u k) x=b k := by
  let h := hardPairThirdDirection u e f k
  let σ := hardPairThirdScale u e f k
  let t := hardPairResidualLevels u b e f a c k/σ
  have hσ : 0<σ := hardPairThirdScale_pos u e f k hk
  have hg := hardPairThirdDirection_geometry u e f he hf hef k hk
  have hp := gaussianPairSectionPoint_levels e f a c (gaussianSectionPoint h t g) he hf hef
  refine ⟨hp.1,hp.2,?_⟩
  change faceDot (u k) (gaussianPairSectionPoint e f a c (gaussianSectionPoint h t g))=b k
  rw [gaussianPairSectionPoint_faceDot_residual e f (u k) a c _ hef]
  have hw : hardPairResidualNormal e f (u k)=σ • h := by
    change hardPairResidualNormal e f (u k)=σ • (σ⁻¹ • hardPairResidualNormal e f (u k))
    rw [smul_smul,mul_inv_cancel₀ hσ.ne',one_smul]
  rw [hw,threshold_faceDot_smul_left,gaussianSectionPoint_on_hyperplane h t hg.1]
  dsimp only [t,hardPairResidualLevels]
  field_simp [hσ.ne']

/-- The actual third-face density appearing in the Gaussian-weighted
pair-section Green formula. Its finite derivative retains `1/σ`. -/
def hardGaussianPairThirdBoundaryDensity {m r : ℕ} (s : Finset (Fin m))
    (u : Fin m → Vector r) (b : Vector m) (e f : Vector r) (a c : ℝ) (k : Fin m) : ℝ :=
  (gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c)*
    gaussianFiniteThresholdFirst s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c) k

theorem hardGaussianPairThirdBoundaryDensity_nonneg {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (a c : ℝ) (k : Fin m)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    0≤hardGaussianPairThirdBoundaryDensity s u b e f a c k := by
  unfold hardGaussianPairThirdBoundaryDensity
  exact mul_nonneg (mul_nonneg (gaussianPDFReal_nonneg _ _ _) (gaussianPDFReal_nonneg _ _ _))
    (gaussianFiniteThresholdFirst_nonneg_of_slack _ _ _ hreg k)

theorem hardGaussianPairThirdBoundaryDensity_zero_of_zero_residual {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (e f : Vector r) (a c : ℝ) (k : Fin m) (hks : k∈s)
    (hk : hardPairResidualNormal e f (u k)=0)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardGaussianPairThirdBoundaryDensity s u b e f a c k=0 := by
  have hs : hardPairResidualLevels u b e f a c k≠0 :=
    (hreg k hks).1.resolve_left (not_not.mpr hk)
  unfold hardGaussianPairThirdBoundaryDensity
  rw [gaussianFiniteThresholdFirst_zero_of_slack _ _ _ k hks hk hs,mul_zero]

/-- Restoring the exact third residual scale identifies the pair Green
boundary coefficient with one actual codimension-three Gaussian mass.
All remaining hard inequalities stay non-strict and retained. -/
theorem hardGaussianPairThirdBoundaryDensity_scale_eq_mass {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (a c : ℝ) (k : Fin m) (hks : k∈s) (hk : hardPairResidualNormal e f (u k)≠0)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardPairThirdScale u e f k*hardGaussianPairThirdBoundaryDensity s u b e f a c k=
      gaussianFrameHardMass (s.erase k) u b
        (nativeTripleFrame e f (hardPairThirdDirection u e f k))
        (nativeTripleLevels a c (hardPairResidualLevels u b e f a c k/hardPairThirdScale u e f k)) := by
  let v := hardPairResidualNormals u e f
  let d := hardPairResidualLevels u b e f a c
  let σ := hardPairThirdScale u e f k
  let h := hardPairThirdDirection u e f k
  let t := d k/σ
  have hσ : 0<σ := hardPairThirdScale_pos u e f k hk
  have hn : vectorNormSq (v k)=σ^2 := (Real.sq_sqrt (vectorNormSq_nonneg _)).symm
  have hh := hardPairThirdDirection_geometry u e f he hf hef k hk
  have hprob : gaussianThresholdSectionProbability (s.erase k) v d h t=
      (standardGaussian (n+1)).real {g | WithLp.equiv 2 (Vector (n+1))
        (gaussianFrameSectionPoint (nativeTripleFrame e f h) (nativeTripleLevels a c t)
          ((WithLp.equiv 2 (Vector (n+1))).symm g))∈gaussianFiniteThresholdEvent (s.erase k) u b} := by
    rw [gaussianThresholdSectionProbability_eq_section]
    congr 1
    ext g
    simp only [mem_setOf_eq]
    rw [gaussianFrameSectionPoint_native_triple e f h hef hh.2.1 hh.2.2]
    exact (gaussianPairSectionPoint_mem_event_iff (s.erase k) u b e f a c
      (gaussianSectionPoint h t g) hef).symm
  have hfirst := gaussianFiniteThresholdFirst_eq_section_of_slack s v d k hks hσ hn (hreg k hks).2
  change gaussianFiniteThresholdFirst s v d k=(gaussianPDFReal 0 1 t/σ)*
    gaussianThresholdSectionProbability (s.erase k) v d h t at hfirst
  change σ*((gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c)*gaussianFiniteThresholdFirst s v d k)=_
  rw [hfirst,hprob]
  unfold gaussianFrameHardMass
  simp only [nativeTripleLevels,Fin.prod_univ_three,Matrix.cons_val_zero,Matrix.cons_val_one,
    Matrix.cons_val_two,Matrix.head_cons,Matrix.tail_cons]
  change σ*((gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c)*((gaussianPDFReal 0 1 t/σ)*_))=
    (gaussianPDFReal 0 1 a*gaussianPDFReal 0 1 c*gaussianPDFReal 0 1 t)*_
  field_simp [hσ.ne']
  dsimp only [h,t,d,σ]
  ring

/-- The signed shifted-level coefficient in pair Green is the actual
normal distance times the shared triple mass. -/
theorem hardGaussianPairThirdBoundaryDensity_weight_eq_mass {m n : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector (n+1)) (b : Vector m)
    (e f : Vector (n+1)) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (a c : ℝ) (k : Fin m) (hks : k∈s) (hk : hardPairResidualNormal e f (u k)≠0)
    (hreg : LocalFiniteThresholdRegularity s (hardPairResidualNormals u e f)
      (hardPairResidualLevels u b e f a c)) :
    hardPairResidualLevels u b e f a c k*hardGaussianPairThirdBoundaryDensity s u b e f a c k=
      (hardPairResidualLevels u b e f a c k/hardPairThirdScale u e f k)*
        gaussianFrameHardMass (s.erase k) u b
          (nativeTripleFrame e f (hardPairThirdDirection u e f k))
          (nativeTripleLevels a c (hardPairResidualLevels u b e f a c k/hardPairThirdScale u e f k)) := by
  have hσ := hardPairThirdScale_pos u e f k hk
  rw [← hardGaussianPairThirdBoundaryDensity_scale_eq_mass s u b e f he hf hef a c k hks hk hreg]
  field_simp
  ring

/-- The constructed third direction has positive own-normal pairing,
fixing the actual orientation of its conormal. -/
theorem hardPairThirdDirection_own_pairing {m r : ℕ} (u : Fin m → Vector r)
    (e f : Vector r) (he : vectorNormSq e=1) (hf : vectorNormSq f=1) (hef : faceDot e f=0)
    (k : Fin m) (hk : hardPairResidualNormal e f (u k)≠0) :
    faceDot (u k) (hardPairThirdDirection u e f k)=hardPairThirdScale u e f k := by
  let σ := hardPairThirdScale u e f k
  let h := hardPairThirdDirection u e f k
  have hσ : 0<σ := hardPairThirdScale_pos u e f k hk
  have hg := hardPairThirdDirection_geometry u e f he hf hef k hk
  have hself : faceDot h h=1 := by simpa only [faceDot,vectorNormSq,pow_two] using hg.1
  have heh : faceDot e h=0 := hg.2.1
  have hfh : faceDot f h=0 := hg.2.2
  have hw : hardPairResidualNormal e f (u k)=σ • h := by
    change hardPairResidualNormal e f (u k)=σ • (σ⁻¹ • hardPairResidualNormal e f (u k))
    rw [smul_smul,mul_inv_cancel₀ hσ.ne',one_smul]
  have hd : faceDot (hardPairResidualNormal e f (u k)) h=faceDot (u k) h := by
    simp only [hardPairResidualNormal,gaussianNormalProjection,threshold_faceDot_sub_left,
      threshold_faceDot_smul_left,heh,hfh,mul_zero,sub_zero]
  rw [hw,threshold_faceDot_smul_left,hself,mul_one] at hd
  exact hd.symm

/-- Three incident orthonormal descriptions with the same actual normal
space and normal point share one actual codimension-three hard mass. -/
theorem gaussianFrameHardMass_three_incident_choices {m r : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin r)) (a : Fin 3 → Fin 3 → ℝ)
    (hv : ∀ i, Orthonormal ℝ (v i))
    (hspan : ∀ i, Submodule.span ℝ (Set.range (v i))=Submodule.span ℝ (Set.range (v 0)))
    (hz : ∀ i, (∑ j, a i j • v i j)=∑ j, a 0 j • v 0 j) :
    ∀ i, gaussianFrameHardMass s u b (v i) (a i)=gaussianFrameHardMass s u b (v 0) (a 0) := by
  intro i
  exact gaussianFrameHardMass_frame_independent s u b (v i) (v 0) (hv i) (hv 0)
    (a i) (a 0) (hspan i) (hz i)

/-- Common actual supporting levels determine the same affine normal
point inside the original normal span. This discharges equal-`Z` rather
than asking for it as an input to the shared-mass theorem. -/
theorem gaussianFrameHardMass_eq_of_spanning_levels {m r q p : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v w : Fin q → EuclideanSpace ℝ (Fin r)) (hv : Orthonormal ℝ v) (hw : Orthonormal ℝ w)
    (a c : Fin q → ℝ) (N : Fin p → EuclideanSpace ℝ (Fin r))
    (hspanv : Submodule.span ℝ (Set.range v)=Submodule.span ℝ (Set.range N))
    (hspanw : Submodule.span ℝ (Set.range w)=Submodule.span ℝ (Set.range N))
    (hlevels : ∀ i, ⟪N i,∑ j, a j • v j⟫_ℝ=⟪N i,∑ j, c j • w j⟫_ℝ) :
    gaussianFrameHardMass s u b v a=gaussianFrameHardMass s u b w c := by
  have hzv : (∑ j, a j • v j)∈Submodule.span ℝ (Set.range N) := by
    rw [← hspanv]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  have hzw : (∑ j, c j • w j)∈Submodule.span ℝ (Set.range N) := by
    rw [← hspanw]
    apply Submodule.sum_mem
    intro j _
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j,rfl⟩)
  have hz := normalPoint_eq_of_spanning_levels N _ _ hzv hzw hlevels
  exact gaussianFrameHardMass_frame_independent s u b v w hv hw a c
    (hspanv.trans hspanw.symm) hz

theorem gaussianFrameHardMass_three_choices_of_supporting_levels {m r p : ℕ}
    (s : Finset (Fin m)) (u : Fin m → Vector r) (b : Vector m)
    (v : Fin 3 → Fin 3 → EuclideanSpace ℝ (Fin r)) (a : Fin 3 → Fin 3 → ℝ)
    (N : Fin p → EuclideanSpace ℝ (Fin r)) (B : Fin p → ℝ)
    (hv : ∀ i, Orthonormal ℝ (v i))
    (hspan : ∀ i, Submodule.span ℝ (Set.range (v i))=Submodule.span ℝ (Set.range N))
    (hlevels : ∀ i k, ⟪N k,∑ j, a i j • v i j⟫_ℝ=B k) :
    ∀ i, gaussianFrameHardMass s u b (v i) (a i)=gaussianFrameHardMass s u b (v 0) (a 0) := by
  intro i
  exact gaussianFrameHardMass_eq_of_spanning_levels s u b (v i) (v 0) (hv i) (hv 0)
    (a i) (a 0) N (hspan i) (hspan 0) (fun k => (hlevels i k).trans (hlevels 0 k).symm)

end
end RectangleCLTArxivV1
