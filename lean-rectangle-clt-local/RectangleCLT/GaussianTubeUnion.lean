import RectangleCLT.GaussianTubeEvents
import RectangleCLT.BoundedConcentrationShift
import RectangleCLT.WeightedConditioning
import RectangleCLT.GaussianEnvelope
import RectangleCLT.GaussianLocalDeterminants

/-! Common-space disjointness and boundary localization of the actual
augmented Gaussian tube images. Distinct complete active sets are summed
through one union event, without a factor depending on the number of faces. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT.GaussianTube

noncomputable section

private theorem face_injective {p q : ℕ} (S : CompatibleFaceTuple p q) :
    Function.Injective S.face := by
  intro i j hij
  exact S.coordinate_injective (congrArg Prod.fst hij)

/-- The tube's actual normal Gram matrix is the compatible signed
principal covariance matrix. -/
theorem normalMatrix_gram {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) :
    (normalMatrix S A).transpose * normalMatrix S A = S.gram (A * A.transpose) := by
  ext i j
  exact signedRowNormal_gram A (S.face i) (S.face j)

/-- Active tube invertibility follows from a genuine sparse covariance lower
bound, independently of whether the full Gaussian covariance is invertible. -/
theorem normalMatrix_gram_det_isUnit {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) {a : ℝ}
    (hlocal : LocalCovarianceLower (A * A.transpose) q a) (ha : 0 < a) :
    IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det := by
  have hsym : ∀ i j, (A * A.transpose) i j = (A * A.transpose) j i := by
    intro i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
  rw [normalMatrix_gram]
  exact isUnit_iff_ne_zero.mpr (ne_of_gt (S.gram_det_pos hlocal ha hsym))

/-- The random rectangle's offsets in the Gaussian factor's coordinates. -/
def commonOffsets {p : ℕ} (s : FaceSmoother p) (r : Vector p)
    (e : ℝ × (Face p → ℝ)) (f : Face p) : ℝ :=
  s.offsets f + s.bandwidth * Real.log (e.2 f / e.1) - FaceSmoother.normalDot f r

private theorem signed_normal_eq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (z : Vector p) :
    faceDot (signedRowNormal A f) z = FaceSmoother.normalDot f (A.mulVec z) := by
  simp only [faceDot, signedRowNormal, normalDot_eq_faceSign_mul,
    Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

private theorem normalDot_add {p : ℕ} (f : Face p) (z r : Vector p) :
    FaceSmoother.normalDot f (z + r) =
      FaceSmoother.normalDot f z + FaceSmoother.normalDot f r := by
  rw [normalDot_eq_faceSign_mul, normalDot_eq_faceSign_mul, normalDot_eq_faceSign_mul]
  exact mul_add _ _ _

private theorem exponential_lt_iff {p : ℕ} (s : FaceSmoother p)
    (f : Face p) (hf : f ∈ s.faces) (z : Vector p) (E₀ e : ℝ)
    (h0 : 0 < E₀) (he : 0 < e) :
    E₀ * (s.weights z).weight f < e ↔
      FaceSmoother.normalDot f z < s.offsets f + s.bandwidth * Real.log (e / E₀) := by
  simp only [FaceSmoother.weights, hf, ↓reduceIte]
  rw [← lt_div_iff₀' h0, ← Real.lt_log_iff_exp_lt (div_pos he h0),
    div_lt_iff₀ s.bandwidth_pos]
  unfold FaceSmoother.faceScore
  constructor <;> intro h <;> linarith

private theorem exponential_eq_iff {p : ℕ} (s : FaceSmoother p)
    (f : Face p) (hf : f ∈ s.faces) (z : Vector p) (E₀ e : ℝ)
    (h0 : 0 < E₀) (he : 0 < e) :
    E₀ * (s.weights z).weight f = e ↔
      FaceSmoother.normalDot f z = s.offsets f + s.bandwidth * Real.log (e / E₀) := by
  simp only [FaceSmoother.weights, hf, ↓reduceIte]
  constructor
  · intro h
    have hh : Real.exp (s.faceScore f z / s.bandwidth) = e / E₀ := by
      apply (eq_div_iff (ne_of_gt h0)).mpr
      simpa only [mul_comm] using h
    have hl := congrArg Real.log hh
    rw [Real.log_exp] at hl
    unfold FaceSmoother.faceScore at hl
    have hc := (div_eq_iff (ne_of_gt s.bandwidth_pos)).mp hl
    linarith
  · intro h
    have hh : s.faceScore f z / s.bandwidth = Real.log (e / E₀) := by
      apply (div_eq_iff (ne_of_gt s.bandwidth_pos)).mpr
      unfold FaceSmoother.faceScore
      linarith
    rw [hh, Real.exp_log (div_pos he h0)]
    field_simp

private theorem normal_add_shift {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Face p) (z r : Vector p) :
    FaceSmoother.normalDot f (A.mulVec z + r) =
      faceDot (signedRowNormal A f) z + FaceSmoother.normalDot f r := by
  rw [normalDot_add, signed_normal_eq]

/-- Every source witness belongs to the complete active face of the common
random rectangle. Strict inactive inequalities remove all overlap boundaries. -/
theorem source_base_exactActiveFace {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) (e : ℝ × (Face p → ℝ))
    (h0 : 0 < e.1) (he : ∀ f, 0 < e.2 f) (width : ℝ) (w : Coordinates p q)
    (hw : w ∈ sourceDomain S s A r e.1 e.2 width)
    (heq : ∀ i, tube (map (normalMatrix S A) s.bandwidth e.1 (activeOffsets S s r) w) i =
      e.2 (S.face i)) :
    base w ∈ exactActiveFace s.faces (activeFaces S) (signedRowNormal A) (commonOffsets s r e) := by
  classical
  have hact (f : Face p) (hf : f ∈ activeFaces S) :
      faceDot (signedRowNormal A f) (base w) = commonOffsets s r e f := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    have hh := heq i
    rw [activeExponential_eq S s A r hactive] at hh
    have hx := (exponential_eq_iff s (S.face i) (hactive i) _ e.1 _ h0 (he _)).mp hh
    rw [normal_add_shift] at hx
    dsimp [commonOffsets]
    linarith
  have hstrict (f : Face p) (hf : f ∈ s.faces) (hna : f ∉ activeFaces S) :
      faceDot (signedRowNormal A f) (base w) < commonOffsets s r e f := by
    have hx := (exponential_lt_iff s f hf _ e.1 _ h0 (he f)).mp (hw.2 f hf hna)
    rw [normal_add_shift] at hx
    dsimp [commonOffsets]
    linarith
  constructor
  · intro f hf
    by_cases hfa : f ∈ activeFaces S
    · exact (hact f hfa).le
    · exact (hstrict f hf hfa).le
  · intro f hf
    by_cases hfa : f ∈ activeFaces S
    · exact ⟨fun _ => hfa, fun _ => hact f hfa⟩
    · exact ⟨fun hh => False.elim ((ne_of_lt (hstrict f hf hfa)) hh), fun hh => False.elim (hfa hh)⟩

/-- Extend the active tuple's coefficients by zero to the full face family. -/
def fullCoefficients {p q : ℕ} (S : CompatibleFaceTuple p q) (u : Fin q → ℝ)
    (f : Face p) : ℝ := ∑ i, if S.face i = f then u i else 0

private theorem fullCoefficients_at {p q : ℕ} (S : CompatibleFaceTuple p q)
    (u : Fin q → ℝ) (i : Fin q) : fullCoefficients S u (S.face i) = u i := by
  classical
  unfold fullCoefficients
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hji
    exact if_neg (fun hh => hji (face_injective S hh))
  · simp

private theorem displacement_fullCoefficients {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (u : Fin q → ℝ) :
    outwardDisplacement (activeFaces S) (signedRowNormal A) (fullCoefficients S u) =
      (normalMatrix S A).mulVec u := by
  classical
  funext j
  unfold outwardDisplacement activeFaces
  rw [Finset.sum_image (fun i _ k _ hik => face_injective S hik)]
  simp_rw [fullCoefficients_at]
  simp only [normalMatrix, Matrix.mulVec, dotProduct, signedRowNormal]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Each augmented image event is an actual positive outward tube of the
same common random rectangle, in Gaussian-factor coordinates. -/
theorem imageEvent_mem_outwardTube {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces) (width : ℝ)
    {ze : Vector p × (ℝ × (Face p → ℝ))}
    (hz : ze ∈ imageEvent S s A r width) :
    ze.1 ∈ outwardTube s.faces (activeFaces S) (signedRowNormal A)
      (commonOffsets s r ze.2) width := by
  classical
  obtain ⟨h0, he, w, hw, heq⟩ := hz
  have het (i : Fin q) := congrArg (fun v : Coordinates p q => tube v i) heq
  have hbase := source_base_exactActiveFace S s A r hactive ze.2 h0 he width w hw het
  refine ⟨base w, hbase, fullCoefficients S (tube w), ?_, ?_⟩
  · intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    simpa only [fullCoefficients_at] using hw.1 i
  · have hy := congrArg (base : Coordinates p q → Vector p) heq
    rw [base_map] at hy
    simpa only [displacement_fullCoefficients] using hy.symm

/-- Distinct complete active sets have disjoint images in the common
Gaussian/exponential probability space. -/
theorem imageEvent_disjoint {p q k : ℕ}
    (S : CompatibleFaceTuple p q) (T : CompatibleFaceTuple p k)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hS : ∀ i, S.face i ∈ s.faces) (hT : ∀ i, T.face i ∈ s.faces)
    (width : ℝ) (hne : activeFaces S ≠ activeFaces T) :
    Disjoint (imageEvent S s A r width) (imageEvent T s A r width) := by
  classical
  have hsubS : activeFaces S ⊆ s.faces := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact hS i
  have hsubT : activeFaces T ⊆ s.faces := by
    intro f hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact hT i
  rw [Set.disjoint_left]
  intro ze hzS hzT
  have hd := outwardTube_disjoint (normal := signedRowNormal A)
    (offset := commonOffsets s r ze.2) (width := width) hsubS hsubT hne
  exact Set.disjoint_left.mp hd
    (imageEvent_mem_outwardTube S s A r hS width hzS)
    (imageEvent_mem_outwardTube T s A r hT width hzT)

private theorem abs_faceDot_le_one {p : ℕ} (x y : Vector p)
    (hx : vectorNormSq x = 1) (hy : vectorNormSq y = 1) : |faceDot x y| ≤ 1 := by
  have hp : 0 ≤ vectorNormSq x + vectorNormSq y + 2 * faceDot x y := by
    calc
      0 ≤ ∑ j, (x j + y j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      _ = _ := by
        simp only [add_sq, vectorNormSq, faceDot, Finset.sum_add_distrib,
          ← Finset.mul_sum, mul_assoc]
        ring
  have hm : 0 ≤ vectorNormSq x + vectorNormSq y - 2 * faceDot x y := by
    calc
      0 ≤ ∑ j, (x j - y j) ^ 2 := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
      _ = _ := by
        simp only [sub_sq, vectorNormSq, faceDot, Finset.sum_add_distrib,
          Finset.sum_sub_distrib, ← Finset.mul_sum, mul_assoc]
        ring
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem signedRowNormal_normSq {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (hdiag : ∀ j, (A * A.transpose) j j = 1) (f : Face p) :
    vectorNormSq (signedRowNormal A f) = 1 := by
  have hh := hdiag f.1
  simp only [vectorNormSq, signedRowNormal, mul_pow, faceSign_sq, one_mul]
  simpa only [Matrix.mul_apply, Matrix.transpose_apply, pow_two] using hh

private theorem outward_mem_annulus_corr {p q : ℕ}
    (faces : Finset (Face p)) (normal : Face p → Vector p) (offset : Face p → ℝ)
    (active : Fin q → Face p) (N : Matrix (Fin p) (Fin q) ℝ)
    (hN : ∀ i j, N j i = normal (active i) j)
    (ha : ∀ i, active i ∈ faces) (hd : IsUnit (N.transpose * N).det)
    (hq : 0 < q) (z : Vector p) (u : Fin q → ℝ) (width ρ : ℝ) (hρ : 0 ≤ ρ)
    (hzmem : z ∈ facePolyhedron faces normal offset)
    (hz : ∀ i, faceDot (normal (active i)) z = offset (active i))
    (hu : ∀ i, 0 < u i ∧ u i ≤ width)
    (hcorr : ∀ f ∈ faces, ∀ i, |faceDot (normal f) (fun j => N j i)| ≤ ρ) :
    z + N.mulVec u ∈
      facePolyhedron faces normal (fun f => offset f + (q : ℝ) * ρ * width) \
        facePolyhedron faces normal offset := by
  refine ⟨?_, outward_not_mem_polyhedron faces normal offset active N hN ha hd hq z u hz
    (fun i => (hu i).1)⟩
  intro f hf
  have hdot : faceDot (normal f) (N.mulVec u) ≤ (q : ℝ) * ρ * width := by
    rw [faceDot_comm, faceDot_mulVec]
    calc
      _ ≤ ∑ i, u i * ρ := by
        apply Finset.sum_le_sum
        intro i _
        apply mul_le_mul_of_nonneg_left _ (hu i).1.le
        apply (le_abs_self _).trans
        simpa only [faceDot, Matrix.mulVec, dotProduct, Matrix.transpose_apply, mul_comm]
          using hcorr f hf i
      _ ≤ ∑ _i : Fin q, width * ρ := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hu i).2 hρ)
      _ = _ := by simp; ring
  have hsum : faceDot (normal f) (z + N.mulVec u) =
      faceDot (normal f) z + faceDot (normal f) (N.mulVec u) := by
    simp only [faceDot, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  rw [hsum]
  exact add_le_add (hzmem f hf) hdot

/-- The common Gaussian image lies in the actual random rectangle boundary
layer of width `q*width`. This is the geometric localization used before
conditioning on the independent bounded base. -/
theorem imageEvent_mem_boundaryLayer {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq : 0 < q) (width : ℝ) {ze : Vector p × (ℝ × (Face p → ℝ))}
    (hz : ze ∈ imageEvent S s A r width) :
    A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).boundaryLayer ((q : ℝ) * width) := by
  classical
  obtain ⟨h0, he, w, hw, heq⟩ := hz
  have het (i : Fin q) := congrArg (fun v : Coordinates p q => tube v i) heq
  have hbase := source_base_exactActiveFace S s A r hactive ze.2 h0 he width w hw het
  have hface (i : Fin q) :
      faceDot (signedRowNormal A (S.face i)) (base w) = commonOffsets s r ze.2 (S.face i) :=
    (hbase.2 (S.face i) (hactive i)).mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hcorr : ∀ f ∈ s.faces, ∀ i, |faceDot (signedRowNormal A f)
      (fun j => normalMatrix S A j i)| ≤ 1 := by
    intro f _ i
    exact abs_faceDot_le_one _ _ (signedRowNormal_normSq A hdiag f)
      (signedRowNormal_normSq A hdiag (S.face i))
  have ht := outward_mem_annulus s.faces (signedRowNormal A) (commonOffsets s r ze.2)
    S.face (normalMatrix S A) (fun _ _ => rfl) hactive hd hq (base w) (tube w) width
    hbase.1 hface (fun i => ⟨(hw.1 i).1, (hw.1 i).2.le⟩) hcorr
  have hy := congrArg (base : Coordinates p q → Vector p) heq
  rw [base_map] at hy
  change base w + (normalMatrix S A).mulVec (tube w) = ze.1 at hy
  rw [hy] at ht
  have hpoly (d : ℝ) :
      ze.1 ∈ facePolyhedron s.faces (signedRowNormal A)
        (fun f => commonOffsets s r ze.2 f + d) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet d := by
    simp only [facePolyhedron, Set.mem_setOf_eq, FaceSmoother.outerSet,
      FaceSmoother.randomRectangle, commonOffsets]
    constructor <;> intro h f hf <;> have hh := h f hf <;>
      rw [normal_add_shift] at * <;> linarith
  have hpoly0 : ze.1 ∈ facePolyhedron s.faces (signedRowNormal A) (commonOffsets s r ze.2) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet 0 := by
    simpa only [add_zero] using hpoly 0
  have hwidth : 0 < width := ((hw.1 ⟨0, hq⟩).1).trans ((hw.1 ⟨0, hq⟩).2)
  have hqw : 0 ≤ (q : ℝ) * width := mul_nonneg (Nat.cast_nonneg _) hwidth.le
  refine ⟨(hpoly _).mp ht.1, ?_⟩
  intro hinner
  apply ht.2
  apply hpoly0.mpr
  intro f hf
  have hh := hinner f hf
  linarith

/-- General-variance form of common-space localization, preserving the
factor `ρ` in the observed displacement width. -/
theorem imageEvent_mem_boundaryLayer_of_variance {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p)
    (hactive : ∀ i, S.face i ∈ s.faces)
    {ρ : ℝ} (hρ : 0 < ρ) (hdiag : ∀ j, (A * A.transpose) j j = ρ)
    (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det)
    (hq : 0 < q) (width : ℝ) {ze : Vector p × (ℝ × (Face p → ℝ))}
    (hz : ze ∈ imageEvent S s A r width) :
    A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).boundaryLayer ((q : ℝ) * ρ * width) := by
  classical
  obtain ⟨h0, he, w, hw, heq⟩ := hz
  have het (i : Fin q) := congrArg (fun v : Coordinates p q => tube v i) heq
  have hbase := source_base_exactActiveFace S s A r hactive ze.2 h0 he width w hw het
  have hface (i : Fin q) :
      faceDot (signedRowNormal A (S.face i)) (base w) = commonOffsets s r ze.2 (S.face i) :=
    (hbase.2 (S.face i) (hactive i)).mpr (Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩)
  have hcorr : ∀ f ∈ s.faces, ∀ i, |faceDot (signedRowNormal A f)
      (fun j => normalMatrix S A j i)| ≤ ρ := by
    intro f _ i
    change |faceDot (signedRowNormal A f) (signedRowNormal A ((S.face i)))| ≤ ρ
    rw [signedRowNormal_gram, abs_mul, abs_mul, abs_faceSign, abs_faceSign, one_mul, one_mul]
    exact rowGram_abs_le_variance A hρ hdiag _ _
  have ht := outward_mem_annulus_corr s.faces (signedRowNormal A) (commonOffsets s r ze.2)
    S.face (normalMatrix S A) (fun _ _ => rfl) hactive hd hq (base w) (tube w) width ρ hρ.le
    hbase.1 hface (fun i => ⟨(hw.1 i).1, (hw.1 i).2.le⟩) hcorr
  have hy := congrArg (base : Coordinates p q → Vector p) heq
  rw [base_map] at hy
  change base w + (normalMatrix S A).mulVec (tube w) = ze.1 at hy
  rw [hy] at ht
  have hpoly (d : ℝ) :
      ze.1 ∈ facePolyhedron s.faces (signedRowNormal A)
        (fun f => commonOffsets s r ze.2 f + d) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet d := by
    simp only [facePolyhedron, Set.mem_setOf_eq, FaceSmoother.outerSet,
      FaceSmoother.randomRectangle, commonOffsets]
    constructor <;> intro h f hf <;> have hh := h f hf <;>
      rw [normal_add_shift] at * <;> linarith
  have hpoly0 : ze.1 ∈ facePolyhedron s.faces (signedRowNormal A) (commonOffsets s r ze.2) ↔
      A.mulVec ze.1 + r ∈ (s.randomRectangle ze.2).outerSet 0 := by
    simpa only [add_zero] using hpoly 0
  have hwidth : 0 < width := ((hw.1 ⟨0, hq⟩).1).trans ((hw.1 ⟨0, hq⟩).2)
  have hqw : 0 ≤ (q : ℝ) * ρ * width :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hρ.le) hwidth.le
  refine ⟨(hpoly _).mp ht.1, ?_⟩
  intro hinner
  apply ht.2
  apply hpoly0.mpr
  intro f hf
  have hh := hinner f hf
  linarith

/-- One common experiment, including the independent bounded base. -/
abbrev CommonSamples (p : ℕ) := Vector p × (ℝ × (Face p → ℝ))

def liftedImageEvent {Ω : Type*} {p q : ℕ} (S : CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (width : ℝ) : Set (CommonSamples p × Ω) :=
  {z | z.1 ∈ imageEvent S s A (V z.2) width}

/-- The measured common boundary event containing the whole tube family. -/
def annulusEvent {Ω : Type*} {p : ℕ} (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (d : ℝ) :
    Set (CommonSamples p × Ω) :=
  {z | A.mulVec z.1.1 + V z.2 ∈ (s.randomRectangle z.1.2).boundaryLayer d}

theorem measurableSet_liftedImageEvent {Ω : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (S : CompatibleFaceTuple p q) (s : FaceSmoother p)
    (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (width : ℝ) (hd : IsUnit ((normalMatrix S A).transpose * normalMatrix S A).det) :
    MeasurableSet (liftedImageEvent S s A V width) :=
  (measurableSet_imageEvent_joint S s A width hd).preimage
    ((hV.comp measurable_snd).prodMk measurable_fst)

theorem measurableSet_annulusEvent {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    (V : Ω → Vector p) (hV : Measurable V) (d : ℝ) :
    MeasurableSet (annulusEvent s A V d) := by
  have hX : Measurable (fun z : CommonSamples p × Ω => A.mulVec z.1.1 + V z.2) :=
    ((measurable_mulVec A).comp (measurable_fst.comp measurable_fst)).add
      (hV.comp measurable_snd)
  have hnormal (f : Face p) : Measurable
      (fun z : CommonSamples p × Ω => FaceSmoother.normalDot f (A.mulVec z.1.1 + V z.2)) := by
    simp only [normalDot_eq_faceSign_mul]
    exact ((measurable_pi_apply f.1).comp hX).const_mul _
  have hoff (f : Face p) : Measurable
      (fun z : CommonSamples p × Ω => s.offsets f + s.bandwidth * Real.log (z.1.2.2 f / z.1.2.1)) := by
    have hEf : Measurable (fun z : CommonSamples p × Ω => z.1.2.2 f) :=
      (measurable_pi_apply f).comp ((measurable_snd.comp measurable_snd).comp measurable_fst)
    have hE0 : Measurable (fun z : CommonSamples p × Ω => z.1.2.1) :=
      (measurable_fst.comp measurable_snd).comp measurable_fst
    exact ((hEf.div hE0).log.const_mul _).const_add _
  have houter (a : ℝ) : MeasurableSet
      {z : CommonSamples p × Ω | A.mulVec z.1.1 + V z.2 ∈ (s.randomRectangle z.1.2).outerSet a} := by
    change MeasurableSet {z : CommonSamples p × Ω | ∀ f ∈ s.faces,
      FaceSmoother.normalDot f (A.mulVec z.1.1 + V z.2) ≤
        s.offsets f + s.bandwidth * Real.log (z.1.2.2 f / z.1.2.1) + a}
    simp only [Set.setOf_forall]
    apply MeasurableSet.iInter
    intro f
    apply MeasurableSet.iInter
    intro _
    exact measurableSet_le (hnormal f) ((hoff f).add_const a)
  exact (houter d).diff (houter (-d))

/-- One point belongs to at most one image indexed by a distinct complete
active set; hence the weighted family fits inside one annulus indicator. -/
theorem sum_weighted_image_indicators_le
    {Ω ι : Type*} {p q : ℕ} (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hdiag : ∀ j, (A * A.transpose) j j = 1)
    (hd : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hq : 0 < q) (width : ℝ)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (w : CommonSamples p → ℝ) (hw0 : ∀ e, 0 ≤ w e) (z : CommonSamples p × Ω) :
    (∑ i ∈ I, w z.1 * (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) ≤
      w z.1 * (annulusEvent s A V ((q : ℝ) * width)).indicator (fun _ => (1 : ℝ)) z := by
  classical
  by_cases hex : ∃ i ∈ I, z ∈ liftedImageEvent (S i) s A V width
  · obtain ⟨i, hi, hzi⟩ := hex
    have hza : z ∈ annulusEvent s A V ((q : ℝ) * width) :=
      imageEvent_mem_boundaryLayer (S i) s A (V z.2) (hactive i hi) hdiag (hd i hi) hq width hzi
    rw [Set.indicator_of_mem hza, Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hzi]
    · intro j hj hji
      have hne : activeFaces (S j) ≠ activeFaces (S i) := fun hh => hji (hinj j hj i hi hh)
      have hdis := imageEvent_disjoint (S j) (S i) s A (V z.2)
        (hactive j hj) (hactive i hi) width hne
      have hzj : z ∉ liftedImageEvent (S j) s A V width :=
        fun hh => Set.disjoint_left.mp hdis hh hzi
      rw [Set.indicator_of_not_mem hzj, mul_zero]
    · exact fun hn => False.elim (hn hi)
  · have hsum : (∑ i ∈ I, w z.1 *
        (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_not_mem (fun hz => hex ⟨i, hi, hz⟩), mul_zero]
    rw [hsum]
    apply mul_nonneg (hw0 _)
    by_cases hz : z ∈ annulusEvent s A V ((q : ℝ) * width) <;> simp [hz]

/-- The same disjoint-family estimate with the actual Gaussian coordinate
variance in the localization width. -/
theorem sum_weighted_image_indicators_le_of_variance
    {Ω ι : Type*} {p q : ℕ} (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    {ρ : ℝ} (hρ : 0 < ρ) (hdiag : ∀ j, (A * A.transpose) j j = ρ)
    (hd : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hq : 0 < q) (width : ℝ)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (w : CommonSamples p → ℝ) (hw0 : ∀ e, 0 ≤ w e) (z : CommonSamples p × Ω) :
    (∑ i ∈ I, w z.1 * (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) ≤
      w z.1 * (annulusEvent s A V ((q : ℝ) * ρ * width)).indicator (fun _ => (1 : ℝ)) z := by
  classical
  by_cases hex : ∃ i ∈ I, z ∈ liftedImageEvent (S i) s A V width
  · obtain ⟨i, hi, hzi⟩ := hex
    have hza : z ∈ annulusEvent s A V ((q : ℝ) * ρ * width) :=
      imageEvent_mem_boundaryLayer_of_variance (S i) s A (V z.2) (hactive i hi) hρ hdiag (hd i hi) hq width hzi
    rw [Set.indicator_of_mem hza, Finset.sum_eq_single i]
    · rw [Set.indicator_of_mem hzi]
    · intro j hj hji
      have hne : activeFaces (S j) ≠ activeFaces (S i) := fun hh => hji (hinj j hj i hi hh)
      have hdis := imageEvent_disjoint (S j) (S i) s A (V z.2)
        (hactive j hj) (hactive i hi) width hne
      have hzj : z ∉ liftedImageEvent (S j) s A V width :=
        fun hh => Set.disjoint_left.mp hdis hh hzi
      rw [Set.indicator_of_not_mem hzj, mul_zero]
    · exact fun hn => False.elim (hn hi)
  · have hsum : (∑ i ∈ I, w z.1 *
        (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) = 0 := by
      apply Finset.sum_eq_zero
      intro i hi
      rw [Set.indicator_of_not_mem (fun hz => hex ⟨i, hi, hz⟩), mul_zero]
    rw [hsum]
    apply mul_nonneg (hw0 _)
    by_cases hz : z ∈ annulusEvent s A V ((q : ℝ) * ρ * width) <;> simp [hz]

/-- Summing all distinct compatible active-face images and conditioning on
the actual bounded independent base gives one concentration factor. The
weight may depend arbitrarily on the Gaussian image and exponential samples;
there is no factor depending on the number of active-face choices. -/
theorem integral_sum_weighted_image_indicators_le
    {Ω ι : Type*} [MeasurableSpace Ω] {p n q : ℕ}
    (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ j, (A * A.transpose) j j = ρ)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hd : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (hq : 0 < q) {width : ℝ} (hwidth : 0 < width)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ i ∈ I, ∫ z, w z.1 *
      (liftedImageEvent (S i) s A (sumVector ξ) width).indicator (fun _ => (1 : ℝ)) z
        ∂γ.prod μ) ≤
      (1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v)) *
        (∫ e, w e ∂γ) := by
  classical
  have hwp : Integrable (fun z : CommonSamples p × Ω => w z.1) (γ.prod μ) := by
    simpa only [mul_one] using hw.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hwi (i : ι) (hi : i ∈ I) : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (liftedImageEvent (S i) s A (sumVector ξ) width).indicator (fun _ => (1 : ℝ)) z)
        (γ.prod μ) := by
    have heq : (fun z : CommonSamples p × Ω => w z.1 *
        (liftedImageEvent (S i) s A (sumVector ξ) width).indicator (fun _ => (1 : ℝ)) z) =
        (liftedImageEvent (S i) s A (sumVector ξ) width).indicator (fun z => w z.1) := by
      funext z
      by_cases hz : z ∈ liftedImageEvent (S i) s A (sumVector ξ) width <;> simp [hz]
    rw [heq]
    exact hwp.indicator (measurableSet_liftedImageEvent (S i) s A _ h.measurable_sum width (hd i hi))
  have hAnn := measurableSet_annulusEvent s A (sumVector ξ) h.measurable_sum ((q : ℝ) * ρ * width)
  have hwa : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width)).indicator (fun _ => (1 : ℝ)) z)
        (γ.prod μ) := by
    have heq : (fun z : CommonSamples p × Ω => w z.1 *
        (annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width)).indicator (fun _ => (1 : ℝ)) z) =
        (annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width)).indicator (fun z => w z.1) := by
      funext z
      by_cases hz : z ∈ annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width) <;> simp [hz]
    rw [heq]
    exact hwp.indicator hAnn
  have hsections (e : CommonSamples p) :
      μ.real {ω | (e, ω) ∈ annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width)} ≤
        1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v) := by
    have hdpos : 0 < (q : ℝ) * ρ * width :=
      mul_pos (mul_pos (by exact_mod_cast hq) hρ) hwidth
    simpa only [annulusEvent, Set.mem_setOf_eq, add_comm] using
      h.boundary_probability_le hp hv hdiag (s.randomRectangle e.2) (A.mulVec e.1) hdpos
  rw [← integral_finset_sum I (fun i hi => hwi i hi)]
  calc
    _ ≤ ∫ z, w z.1 *
        (annulusEvent s A (sumVector ξ) ((q : ℝ) * ρ * width)).indicator (fun _ => (1 : ℝ)) z
          ∂γ.prod μ :=
      integral_mono (integrable_finset_sum I (fun i hi => hwi i hi)) hwa
        (sum_weighted_image_indicators_le_of_variance I S s A (sumVector ξ)
          hactive hρ hA hd hq width hinj w hw0)
    _ ≤ _ := integral_weighted_indicator_le hAnn hw hw0 hsections

/-- The unlocalized common-space estimate: all distinct active-face tube
images together use at most the total weighted mass of the experiment. -/
theorem integral_sum_weighted_image_indicators_le_total
    {Ω ι : Type*} [MeasurableSpace Ω] {p q : ℕ}
    (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (V : Ω → Vector p)
    (hV : Measurable V) (width : ℝ)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hd : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ i ∈ I, ∫ z, w z.1 *
      (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z ∂γ.prod μ) ≤
      ∫ e, w e ∂γ := by
  classical
  have hwp : Integrable (fun z : CommonSamples p × Ω => w z.1) (γ.prod μ) := by
    simpa only [mul_one] using hw.mul_prod (integrable_const (1 : ℝ) (μ := μ))
  have hwi (i : ι) (hi : i ∈ I) : Integrable (fun z : CommonSamples p × Ω => w z.1 *
      (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) (γ.prod μ) := by
    have heq : (fun z : CommonSamples p × Ω => w z.1 *
        (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) =
        (liftedImageEvent (S i) s A V width).indicator (fun z => w z.1) := by
      funext z
      by_cases hz : z ∈ liftedImageEvent (S i) s A V width <;> simp [hz]
    rw [heq]
    exact hwp.indicator (measurableSet_liftedImageEvent (S i) s A V hV width (hd i hi))
  have hpoint (z : CommonSamples p × Ω) :
      (∑ i ∈ I, w z.1 * (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) ≤
        w z.1 := by
    by_cases hex : ∃ i ∈ I, z ∈ liftedImageEvent (S i) s A V width
    · obtain ⟨i, hi, hzi⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hzi]
      · intro j hj hji
        have hne : activeFaces (S j) ≠ activeFaces (S i) := fun hh => hji (hinj j hj i hi hh)
        have hdis := imageEvent_disjoint (S j) (S i) s A (V z.2)
          (hactive j hj) (hactive i hi) width hne
        have hzj : z ∉ liftedImageEvent (S j) s A V width :=
          fun hh => Set.disjoint_left.mp hdis hh hzi
        rw [Set.indicator_of_not_mem hzj, mul_zero]
      · exact fun hn => False.elim (hn hi)
    · have hz : ∀ i ∈ I, z ∉ liftedImageEvent (S i) s A V width :=
        fun i hi hzi => hex ⟨i, hi, hzi⟩
      have hzero : (∑ i ∈ I, w z.1 *
          (liftedImageEvent (S i) s A V width).indicator (fun _ => (1 : ℝ)) z) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Set.indicator_of_not_mem (hz i hi), mul_zero]
      rw [hzero]
      exact hw0 _
  rw [← integral_finset_sum I (fun i hi => hwi i hi)]
  have hh := integral_mono (integrable_finset_sum I (fun i hi => hwi i hi)) hwp hpoint
  have heq : (∫ z : CommonSamples p × Ω, w z.1 ∂γ.prod μ) = ∫ e, w e ∂γ := by
    rw [integral_prod _ hwp]
    simp
  exact hh.trans_eq heq

/-- A compatible active face set has a canonical ordered representative;
its choice of ordering has no effect on the common-space union argument. -/
def tupleOfFaceSet {p q : ℕ} (T : Finset (Face p)) (hcard : T.card = q)
    (hcoord : ∀ f ∈ T, ∀ g ∈ T, f.1 = g.1 → f = g) : CompatibleFaceTuple p q := by
  classical
  let e : T ≃ Fin q := T.equivFin.trans (finCongr hcard)
  exact
    { face := fun i => (e.symm i).val
      coordinate_injective := fun i j hij => e.symm.injective (Subtype.ext
        (hcoord _ (e.symm i).property _ (e.symm j).property hij)) }

theorem activeFaces_tupleOfFaceSet {p q : ℕ} (T : Finset (Face p)) (hcard : T.card = q)
    (hcoord : ∀ f ∈ T, ∀ g ∈ T, f.1 = g.1 → f = g) :
    activeFaces (tupleOfFaceSet T hcard hcoord) = T := by
  classical
  let e : T ≃ Fin q := T.equivFin.trans (finCongr hcard)
  change Finset.univ.image (fun i => (e.symm i).val) = T
  ext f
  constructor
  · intro hf
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hf
    exact (e.symm i).property
  · intro hf
    exact Finset.mem_image.mpr ⟨e ⟨f, hf⟩, Finset.mem_univ _, by simp⟩

/-- All compatible subsets of the specified face family, counted once each. -/
def CompatibleFaceSets {p : ℕ} (faces : Finset (Face p)) (q : ℕ) :=
  {T : Finset (Face p) // T ⊆ faces ∧ T.card = q ∧
    ∀ f ∈ T, ∀ g ∈ T, f.1 = g.1 → f = g}

noncomputable instance {p q : ℕ} {faces : Finset (Face p)} :
    Fintype (CompatibleFaceSets faces q) := by
  classical
  unfold CompatibleFaceSets
  exact Fintype.ofFinite _

def compatibleSetTuple {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) : CompatibleFaceTuple p q :=
  tupleOfFaceSet T.val T.property.2.1 T.property.2.2

@[simp] theorem activeFaces_compatibleSetTuple {p q : ℕ} {faces : Finset (Face p)}
    (T : CompatibleFaceSets faces q) : activeFaces (compatibleSetTuple T) = T.val :=
  activeFaces_tupleOfFaceSet _ _ _

/-- The weighted localization estimate summed over every compatible face set.
The canonical enumeration discharges the distinct-active-set condition, so
there is no counting premise and no factor involving the number of faces. -/
theorem integral_sum_all_compatible_images_le
    {Ω : Type*} [MeasurableSpace Ω] {p n q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ)
    {ρ : ℝ} (hρ : 0 < ρ) (hA : ∀ j, (A * A.transpose) j j = ρ)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det)
    (hq : 0 < q) {width : ℝ} (hwidth : 0 < width)
    {μ : Measure Ω} [IsProbabilityMeasure μ] {ξ : Fin n → Ω → Vector p} {η v : ℝ}
    (h : BoundedIndependentHypotheses μ ξ η) (hp : 1 ≤ p) (hv : 0 < v)
    (hdiag : ∀ j, covariance μ (sumVector ξ) j j = v)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ T : CompatibleFaceSets s.faces q, ∫ z, w z.1 *
      (liftedImageEvent (compatibleSetTuple T) s A (sumVector ξ) width).indicator
        (fun _ => (1 : ℝ)) z ∂γ.prod μ) ≤
      (1073741824 * ((q : ℝ) * ρ * width + η) * Real.sqrt (dimensionLog p / v)) *
        (∫ e, w e ∂γ) := by
  classical
  apply integral_sum_weighted_image_indicators_le Finset.univ compatibleSetTuple s A hρ hA
    _ (fun T _ => hd T) _ hq hwidth h hp hv hdiag γ w hw hw0
  · intro T _ i
    apply T.property.1
    rw [← activeFaces_compatibleSetTuple T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro T _ U _ heq
    apply Subtype.ext
    simpa only [activeFaces_compatibleSetTuple] using heq

/-- Direct fixed-shift form of the unlocalized common-space union estimate. -/
theorem integral_sum_fixed_image_indicators_le_total
    {ι : Type*} {p q : ℕ} (I : Finset ι) (S : ι → CompatibleFaceTuple p q)
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (hactive : ∀ i ∈ I, ∀ j, (S i).face j ∈ s.faces)
    (hd : ∀ i ∈ I, IsUnit ((normalMatrix (S i) A).transpose * normalMatrix (S i) A).det)
    (hinj : ∀ i ∈ I, ∀ j ∈ I, activeFaces (S i) = activeFaces (S j) → i = j)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ i ∈ I, ∫ e, w e * (imageEvent (S i) s A r width).indicator (fun _ => (1 : ℝ)) e ∂γ) ≤
      ∫ e, w e ∂γ := by
  classical
  have hmeas (i : ι) (hi : i ∈ I) : MeasurableSet (imageEvent (S i) s A r width) :=
    (measurableSet_imageEvent_joint (S i) s A width (hd i hi)).preimage
      (measurable_const.prodMk measurable_id)
  have hwi (i : ι) (hi : i ∈ I) : Integrable
      (fun e => w e * (imageEvent (S i) s A r width).indicator (fun _ => (1 : ℝ)) e) γ := by
    have heq : (fun e => w e * (imageEvent (S i) s A r width).indicator (fun _ => (1 : ℝ)) e) =
        (imageEvent (S i) s A r width).indicator w := by
      funext e
      by_cases he : e ∈ imageEvent (S i) s A r width <;> simp [he]
    rw [heq]
    exact hw.indicator (hmeas i hi)
  have hpoint (e : CommonSamples p) :
      (∑ i ∈ I, w e * (imageEvent (S i) s A r width).indicator (fun _ => (1 : ℝ)) e) ≤ w e := by
    by_cases hex : ∃ i ∈ I, e ∈ imageEvent (S i) s A r width
    · obtain ⟨i, hi, hei⟩ := hex
      rw [Finset.sum_eq_single i]
      · simp [Set.indicator_of_mem hei]
      · intro j hj hji
        have hne : activeFaces (S j) ≠ activeFaces (S i) := fun hh => hji (hinj j hj i hi hh)
        have hdis := imageEvent_disjoint (S j) (S i) s A r (hactive j hj) (hactive i hi) width hne
        rw [Set.indicator_of_not_mem (fun hej => Set.disjoint_left.mp hdis hej hei), mul_zero]
      · exact fun hn => False.elim (hn hi)
    · have hzero : (∑ i ∈ I, w e *
          (imageEvent (S i) s A r width).indicator (fun _ => (1 : ℝ)) e) = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        rw [Set.indicator_of_not_mem (fun hei => hex ⟨i, hi, hei⟩), mul_zero]
      rw [hzero]
      exact hw0 e
  rw [← integral_finset_sum I (fun i hi => hwi i hi)]
  exact integral_mono (integrable_finset_sum I (fun i hi => hwi i hi)) hw hpoint

/-- Sum every compatible face set's fixed-shift image once, against one
common Gaussian/exponential law and one nonnegative integrable weight. -/
theorem integral_sum_all_fixed_compatible_images_le_total {p q : ℕ}
    (s : FaceSmoother p) (A : Matrix (Fin p) (Fin p) ℝ) (r : Vector p) (width : ℝ)
    (hd : ∀ T : CompatibleFaceSets s.faces q,
      IsUnit ((normalMatrix (compatibleSetTuple T) A).transpose *
        normalMatrix (compatibleSetTuple T) A).det)
    (γ : Measure (CommonSamples p)) [IsProbabilityMeasure γ]
    (w : CommonSamples p → ℝ) (hw : Integrable w γ) (hw0 : ∀ e, 0 ≤ w e) :
    (∑ T : CompatibleFaceSets s.faces q, ∫ e, w e *
      (imageEvent (compatibleSetTuple T) s A r width).indicator (fun _ => (1 : ℝ)) e ∂γ) ≤
      ∫ e, w e ∂γ := by
  classical
  apply integral_sum_fixed_image_indicators_le_total Finset.univ compatibleSetTuple s A r width
    _ (fun T _ => hd T) _ γ w hw hw0
  · intro T _ i
    apply T.property.1
    rw [← activeFaces_compatibleSetTuple T]
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
  · intro T _ U _ heq
    apply Subtype.ext
    simpa only [activeFaces_compatibleSetTuple] using heq

end

end RectangleCLT.GaussianTube
