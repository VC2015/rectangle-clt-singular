import RectangleCLT.GaussianNormalMap
import Mathlib.Analysis.InnerProductSpace.Projection
import Mathlib.Analysis.InnerProductSpace.PiL2

/-! Weighted exponential moments of maxima of concrete Gaussian projections.
The finite family may have polynomially many members; no independence of its
members is required. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators Topology NNReal InnerProductSpace

namespace RectangleCLT

noncomputable section

def linearProjectionFamily {ι : Type*} {p : ℕ} (A : ι → Fin p → ℝ)
    (z : Vector p) : ι → ℝ := fun i => ∑ j, A i j * z j

theorem measurable_linearProjectionFamily {ι : Type*} [Fintype ι] {p : ℕ}
    (A : ι → Fin p → ℝ) : Measurable (linearProjectionFamily A) := by
  apply measurable_pi_lambda
  intro i
  exact Finset.measurable_sum _ (fun j _ => measurable_const.mul (measurable_pi_apply j))

theorem standardGaussian_mgf_linearProjection {p : ℕ} (a : Fin p → ℝ) (t : ℝ) :
    mgf (fun z : Vector p => ∑ j, a j * z j) (standardGaussian p) t =
      Real.exp (t ^ 2 * (∑ j, a j ^ 2) / 2) := by
  classical
  have hind : iIndepFun (fun i (z : Vector p) => a i * z i) (standardGaussian p) :=
    (standardGaussian_iIndepFun p).comp (fun i u => a i * u)
      (fun i => measurable_const.mul measurable_id)
  have hmeas (i : Fin p) : Measurable (fun z : Vector p => a i * z i) :=
    measurable_const.mul (measurable_pi_apply i)
  have hfun : (fun z : Vector p => ∑ j, a j * z j) =
      ∑ i ∈ Finset.univ, fun z : Vector p => a i * z i := by funext z; simp
  rw [hfun, hind.mgf_sum hmeas]
  have hscalar (i : Fin p) :
      mgf (fun z : Vector p => a i * z i) (standardGaussian p) t =
        Real.exp ((a i * t) ^ 2 / 2) := by
    change mgf ((a i) • (fun z : Vector p => z i)) (standardGaussian p) t = _
    rw [mgf_smul_left, standardGaussian_mgf_coordinate]
  simp_rw [hscalar]
  rw [← Real.exp_sum]
  congr 1
  rw [Finset.mul_sum, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem integrable_exp_linearProjection {p : ℕ} (a : Fin p → ℝ) (t : ℝ) :
    Integrable (fun z : Vector p => Real.exp (t * ∑ j, a j * z j))
      (standardGaussian p) :=
  mgf_pos_iff.mp (by rw [standardGaussian_mgf_linearProjection]; positivity)

private theorem exp_norm_family_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (x : ι → ℝ) (t : ℝ) :
    Real.exp (t * ‖x‖) ≤ ∑ i, (Real.exp (t * x i) + Real.exp (-t * x i)) := by
  classical
  obtain ⟨i, hi, hmax⟩ := Finset.exists_max_image Finset.univ (fun i => |x i|)
    (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)
  have hnorm : ‖x‖ = |x i| := by
    apply le_antisymm
    · exact (pi_norm_le_iff_of_nonneg (abs_nonneg _)).mpr fun j =>
        by simpa only [Real.norm_eq_abs] using hmax j (Finset.mem_univ j)
    · simpa only [Real.norm_eq_abs] using norm_le_pi_norm x i
  rw [hnorm]
  have hcoord : Real.exp (t * |x i|) ≤
      Real.exp (t * x i) + Real.exp (-t * x i) := by
    by_cases hx : 0 ≤ x i
    · rw [abs_of_nonneg hx]
      exact le_add_of_nonneg_right (Real.exp_nonneg _)
    · rw [abs_of_neg (lt_of_not_ge hx), mul_neg, ← neg_mul]
      exact le_add_of_nonneg_left (Real.exp_nonneg _)
  exact hcoord.trans (Finset.single_le_sum
    (fun j _ => add_nonneg (Real.exp_nonneg (t * x j))
      (Real.exp_nonneg (-t * x j))) hi)

theorem integrable_exp_projectionMaximum {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (A : ι → Fin p → ℝ) (t : ℝ) :
    Integrable (fun z : Vector p => Real.exp (t * ‖linearProjectionFamily A z‖))
      (standardGaussian p) := by
  have hi := integrable_finset_sum Finset.univ (fun i _ =>
    (integrable_exp_linearProjection (A i) t).add
      (integrable_exp_linearProjection (A i) (-t)))
  apply hi.mono'
    (((measurable_linearProjectionFamily A).norm).const_mul t).exp.aestronglyMeasurable
  exact ae_of_all _ fun z => by
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    exact exp_norm_family_le (linearProjectionFamily A z) t

theorem integral_exp_projectionMaximum_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (A : ι → Fin p → ℝ) (hA : ∀ i, (∑ j, A i j ^ 2) ≤ 1) (t : ℝ) :
    (∫ z : Vector p, Real.exp (t * ‖linearProjectionFamily A z‖)
      ∂standardGaussian p) ≤
      (2 * (Fintype.card ι : ℝ)) * Real.exp (t ^ 2 / 2) := by
  have hi (i : ι) : Integrable (fun z : Vector p =>
      Real.exp (t * linearProjectionFamily A z i) +
        Real.exp (-t * linearProjectionFamily A z i)) (standardGaussian p) :=
    (integrable_exp_linearProjection (A i) t).add
      (integrable_exp_linearProjection (A i) (-t))
  calc
    _ ≤ ∫ z : Vector p, ∑ i, (Real.exp (t * linearProjectionFamily A z i) +
        Real.exp (-t * linearProjectionFamily A z i)) ∂standardGaussian p :=
      integral_mono (integrable_exp_projectionMaximum A t)
        (integrable_finset_sum Finset.univ (fun i _ => hi i))
        (fun z => exp_norm_family_le (linearProjectionFamily A z) t)
    _ = ∑ i, (Real.exp (t ^ 2 * (∑ j, A i j ^ 2) / 2) +
        Real.exp (t ^ 2 * (∑ j, A i j ^ 2) / 2)) := by
      rw [integral_finset_sum Finset.univ (fun i _ => hi i)]
      apply Finset.sum_congr rfl
      intro i _
      simp only [linearProjectionFamily]
      rw [integral_add (integrable_exp_linearProjection (A i) t)
        (integrable_exp_linearProjection (A i) (-t))]
      change mgf (fun z : Vector p => ∑ j, A i j * z j) (standardGaussian p) t +
        mgf (fun z : Vector p => ∑ j, A i j * z j) (standardGaussian p) (-t) = _
      rw [standardGaussian_mgf_linearProjection, standardGaussian_mgf_linearProjection]
      simp only [neg_sq]
    _ ≤ ∑ _i : ι, (Real.exp (t ^ 2 / 2) + Real.exp (t ^ 2 / 2)) := by
      apply Finset.sum_le_sum
      intro i _
      have h := Real.exp_le_exp.mpr (by nlinarith [sq_nonneg t, hA i] :
        t ^ 2 * (∑ j, A i j ^ 2) / 2 ≤ t ^ 2 / 2)
      exact add_le_add h h
    _ = _ := by simp; ring

/-- A polynomial-size Gaussian projection family has a dimension-free
exponential moment after normalization by `sqrt L`. -/
theorem integral_exp_projectionMaximum_scaled_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (A : ι → Fin p → ℝ) (hA : ∀ i, (∑ j, A i j ^ 2) ≤ 1)
    {L C : ℝ} (hL : 1 ≤ L)
    (hcard : 2 * (Fintype.card ι : ℝ) ≤ Real.exp (C * L)) (b : ℝ) :
    (∫ z : Vector p, Real.exp ((b / Real.sqrt L) * ‖linearProjectionFamily A z‖)
      ∂standardGaussian p) ≤ Real.exp (C + b ^ 2 / 2) := by
  let s := Real.sqrt L
  have hLpos : 0 < L := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs2 : s ^ 2 = L := Real.sq_sqrt hLpos.le
  have hhigh : (∫ z : Vector p, Real.exp ((b * s) * ‖linearProjectionFamily A z‖)
      ∂standardGaussian p) ≤ Real.exp ((C + b ^ 2 / 2) * L) := by
    calc
      _ ≤ (2 * (Fintype.card ι : ℝ)) * Real.exp ((b * s) ^ 2 / 2) :=
        integral_exp_projectionMaximum_le A hA (b * s)
      _ ≤ Real.exp (C * L) * Real.exp ((b * s) ^ 2 / 2) :=
        mul_le_mul_of_nonneg_right hcard (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; nlinarith [hs2]
  have hh := (integral_exp_scale_le
    (((measurable_linearProjectionFamily A).norm).const_mul (b * s))
    (integrable_exp_projectionMaximum A (b * s)) (inv_nonneg.mpr hLpos.le)
    ((inv_le_one₀ hLpos).mpr hL) hhigh).2
  have hcoeff : L⁻¹ * (b * s) = b / s := by
    field_simp [ne_of_gt hLpos, ne_of_gt hs]
    nlinarith only [congrArg (fun u : ℝ => b * u) hs2]
  have hexponent : L⁻¹ * ((C + b ^ 2 / 2) * L) = C + b ^ 2 / 2 := by field_simp
  simpa only [← mul_assoc, hcoeff, hexponent] using hh

/-- A concrete nonnegative radius dominated by a finite Gaussian projection
maximum has all the exponential-polynomial moments needed by the face tubes.
The explicit constant depends on `k` and the family-size exponent only. -/
theorem projectionMaximum_weighted_moment_le {ι : Type*} [Fintype ι] [Nonempty ι]
    {p : ℕ} (A : ι → Fin p → ℝ) (hA : ∀ i, (∑ j, A i j ^ 2) ≤ 1)
    (R : Vector p → ℝ) (hRm : Measurable R) (hR0 : ∀ z, 0 ≤ R z)
    {d L C M : ℝ} (hL : 1 ≤ L)
    (hcard : 2 * (Fintype.card ι : ℝ) ≤ Real.exp (C * L))
    (hdom : ∀ z, R z ≤ d * ‖linearProjectionFamily A z‖)
    (hM : Real.sqrt L ≤ M) (k : ℕ) :
    Integrable (fun z => Real.exp (R z / M) * (1 + R z) ^ k) (standardGaussian p) ∧
      (∫ z, Real.exp (R z / M) * (1 + R z) ^ k ∂standardGaussian p) ≤
        (Real.sqrt L) ^ k * Real.exp (C + (d * (k + 1 : ℝ)) ^ 2 / 2) := by
  let s := Real.sqrt L
  let b := d * (k + 1 : ℝ)
  have hLpos : 0 < L := by linarith
  have hs : 0 < s := Real.sqrt_pos.mpr hLpos
  have hs1 : 1 ≤ s := Real.one_le_sqrt.mpr hL
  have hbound (z : Vector p) : Real.exp (R z / M) * (1 + R z) ^ k ≤
      s ^ k * Real.exp ((b / s) * ‖linearProjectionFamily A z‖) := by
    have hx : 0 ≤ R z / s := div_nonneg (hR0 z) hs.le
    have hp : (1 + R z) ^ k ≤ s ^ k * Real.exp ((k : ℝ) * (R z / s)) := by
      calc
        _ ≤ (s * (1 + R z / s)) ^ k := by
          apply pow_le_pow_left₀ (by linarith [hR0 z])
          rw [mul_add, mul_one, mul_div_cancel₀ _ hs.ne']
          linarith
        _ = s ^ k * (1 + R z / s) ^ k := mul_pow _ _ _
        _ ≤ s ^ k * (Real.exp (R z / s)) ^ k := by
          apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le k)
          exact pow_le_pow_left₀ (by linarith : 0 ≤ 1 + R z / s)
            (by linarith [Real.add_one_le_exp (R z / s)] : 1 + R z / s ≤ Real.exp (R z / s)) k
        _ = _ := by rw [← Real.exp_nat_mul]
    have he : Real.exp (R z / M) ≤ Real.exp (R z / s) :=
      Real.exp_le_exp.mpr (div_le_div_of_nonneg_left (hR0 z) hs hM)
    calc
      _ ≤ Real.exp (R z / s) * (s ^ k * Real.exp ((k : ℝ) * (R z / s))) :=
        mul_le_mul he hp (pow_nonneg (by linarith [hR0 z]) k) (Real.exp_nonneg _)
      _ = s ^ k * Real.exp (((k : ℝ) + 1) * R z / s) := by
        rw [mul_left_comm, ← Real.exp_add]
        congr 2
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (pow_nonneg hs.le k)
        apply Real.exp_le_exp.mpr
        have hh := mul_le_mul_of_nonneg_left (hdom z) (by positivity : 0 ≤ (k : ℝ) + 1)
        exact (div_le_div_of_nonneg_right hh hs.le).trans_eq (by dsimp [b]; ring)
  have hI := (integrable_exp_projectionMaximum A (b / s)).const_mul (s ^ k)
  have hi : Integrable (fun z => Real.exp (R z / M) * (1 + R z) ^ k)
      (standardGaussian p) := by
    apply hI.mono' (((hRm.div_const M).exp).mul ((measurable_const.add hRm).pow_const k)).aestronglyMeasurable
    exact ae_of_all _ fun z => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_nonneg _)
        (pow_nonneg (by linarith [hR0 z]) k))]
      exact hbound z
  refine ⟨hi, ?_⟩
  calc
    _ ≤ ∫ z : Vector p, s ^ k *
        Real.exp ((b / s) * ‖linearProjectionFamily A z‖) ∂standardGaussian p :=
      integral_mono hi hI hbound
    _ = s ^ k * (∫ z : Vector p, Real.exp ((b / s) * ‖linearProjectionFamily A z‖)
        ∂standardGaussian p) := integral_const_mul _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (integral_exp_projectionMaximum_scaled_le A hA hL hcard b) (pow_nonneg hs.le k)

/-- Reinterpret native coordinate vectors in their Euclidean norm. -/
def projectionEuclideanVector {p : ℕ} (z : Vector p) : EuclideanSpace ℝ (Fin p) :=
  (WithLp.equiv 2 (Vector p)).symm z

def projectionBasisRows {ι : Type*} {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) :
    Option (Σ i, Fin (Module.finrank ℝ (V i))) → Fin p → ℝ :=
  fun i j => match i with
    | none => 0
    | some a => ((stdOrthonormalBasis ℝ (V a.1) a.2 : V a.1) :
        EuclideanSpace ℝ (Fin p)) j

/-- The true maximum norm of orthogonal projections onto the given family of
subspaces. In particular it is independent of all face thresholds. -/
def subspaceProjectionRadius {ι : Type*} [Fintype ι] {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) (z : Vector p) : ℝ :=
  ‖fun i => ‖(V i).orthogonalProjection (projectionEuclideanVector z)‖‖

theorem measurable_subspaceProjectionRadius {ι : Type*} [Fintype ι] {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) :
    Measurable (subspaceProjectionRadius V) := by
  apply Continuous.measurable
  apply Continuous.norm
  apply continuous_pi
  intro i
  exact ((V i).orthogonalProjection.continuous.comp (PiLp.continuous_equiv_symm 2 _)).norm

theorem projectionBasisRows_variance_le {ι : Type*} {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p)))
    (i : Option (Σ i, Fin (Module.finrank ℝ (V i)))) :
    (∑ j, projectionBasisRows V i j ^ 2) ≤ 1 := by
  classical
  cases i with
  | none => simp [projectionBasisRows]
  | some i =>
    have hn : ‖((stdOrthonormalBasis ℝ (V i.1) i.2 : V i.1) :
        EuclideanSpace ℝ (Fin p))‖ = 1 :=
      (stdOrthonormalBasis ℝ (V i.1)).orthonormal.norm_eq_one i.2
    have hsq := PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ)
      (((stdOrthonormalBasis ℝ (V i.1) i.2 : V i.1) : EuclideanSpace ℝ (Fin p)))
    rw [hn] at hsq
    simp only [projectionBasisRows, Real.norm_eq_abs, sq_abs, one_pow] at hsq ⊢
    exact hsq.symm.le

theorem subspaceProjectionRadius_le_projectionMaximum {ι : Type*} [Fintype ι] {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) (q : ℕ)
    (hV : ∀ i, Module.finrank ℝ (V i) ≤ q) (z : Vector p) :
    subspaceProjectionRadius V z ≤
      (q : ℝ) * ‖linearProjectionFamily (projectionBasisRows V) z‖ := by
  classical
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (Nat.cast_nonneg q) (norm_nonneg _))).mpr
  intro i
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  let b := stdOrthonormalBasis ℝ (V i)
  calc
    _ = ‖∑ j, ⟪(b j : EuclideanSpace ℝ (Fin p)), projectionEuclideanVector z⟫_ℝ • b j‖ := by
      rw [← b.orthogonalProjection_eq_sum]
    _ ≤ ∑ j, ‖⟪(b j : EuclideanSpace ℝ (Fin p)), projectionEuclideanVector z⟫_ℝ • b j‖ :=
      norm_sum_le _ _
    _ = ∑ j : Fin (Module.finrank ℝ (V i)),
        |linearProjectionFamily (projectionBasisRows V) z (some ⟨i, j⟩)| := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_smul, b.orthonormal.norm_eq_one, mul_one, Real.norm_eq_abs]
      congr 1
      simp [linearProjectionFamily, projectionBasisRows, projectionEuclideanVector,
        PiLp.inner_apply, b, real_inner_comm, mul_comm]
    _ ≤ ∑ _j : Fin (Module.finrank ℝ (V i)),
        ‖linearProjectionFamily (projectionBasisRows V) z‖ := by
      apply Finset.sum_le_sum
      intro j _
      exact (Real.norm_eq_abs _).symm.le.trans
        (norm_le_pi_norm (linearProjectionFamily (projectionBasisRows V) z) (some ⟨i, j⟩))
    _ = (Module.finrank ℝ (V i) : ℝ) *
        ‖linearProjectionFamily (projectionBasisRows V) z‖ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hV i) (norm_nonneg _)

theorem projectionBasisRows_card_le {ι : Type*} [Fintype ι] {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) (q : ℕ)
    (hV : ∀ i, Module.finrank ℝ (V i) ≤ q) :
    Fintype.card (Option (Σ i, Fin (Module.finrank ℝ (V i)))) ≤
      1 + q * Fintype.card ι := by
  classical
  simp only [Fintype.card_option, Fintype.card_sigma, Fintype.card_fin]
  have h := Finset.sum_le_sum (fun i (_ : i ∈ (Finset.univ : Finset ι)) => hV i)
  simpa [Nat.add_comm, Nat.mul_comm] using Nat.add_le_add_right h 1

theorem subspaceProjectionRadius_weighted_moment_le {ι : Type*} [Fintype ι] {p : ℕ}
    (V : ι → Submodule ℝ (EuclideanSpace ℝ (Fin p))) (q : ℕ)
    (hV : ∀ i, Module.finrank ℝ (V i) ≤ q) {L C M : ℝ} (hL : 1 ≤ L)
    (hcard : 2 * (1 + (q : ℝ) * (Fintype.card ι : ℝ)) ≤ Real.exp (C * L))
    (hM : Real.sqrt L ≤ M) (k : ℕ) :
    Integrable (fun z => Real.exp (subspaceProjectionRadius V z / M) *
      (1 + subspaceProjectionRadius V z) ^ k) (standardGaussian p) ∧
      (∫ z, Real.exp (subspaceProjectionRadius V z / M) *
        (1 + subspaceProjectionRadius V z) ^ k ∂standardGaussian p) ≤
        (Real.sqrt L) ^ k * Real.exp (C + ((q : ℝ) * (k + 1 : ℝ)) ^ 2 / 2) := by
  have hc : 2 * (Fintype.card (Option (Σ i, Fin (Module.finrank ℝ (V i)))) : ℝ) ≤
      Real.exp (C * L) := by
    have hh : (Fintype.card (Option (Σ i, Fin (Module.finrank ℝ (V i)))) : ℝ) ≤
        1 + (q : ℝ) * (Fintype.card ι : ℝ) := by
      exact_mod_cast projectionBasisRows_card_le V q hV
    exact (mul_le_mul_of_nonneg_left hh (by norm_num : (0 : ℝ) ≤ 2)).trans hcard
  exact projectionMaximum_weighted_moment_le (projectionBasisRows V)
    (projectionBasisRows_variance_le V) (subspaceProjectionRadius V)
    (measurable_subspaceProjectionRadius V) (fun _ => norm_nonneg _) hL hc
    (subspaceProjectionRadius_le_projectionMaximum V q hV) hM k

/-- Every four-tuple of signed normals, with repetitions allowed. All spans
of at most four normals occur by padding tuples with repeated entries. -/
def fourFaceSubspace {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Fin 4 → Face p) : Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  Submodule.span ℝ (Set.range (fun i => projectionEuclideanVector (signedRowNormal A (f i))))

theorem fourFaceSubspace_finrank_le {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    (f : Fin 4 → Face p) : Module.finrank ℝ (fourFaceSubspace A f) ≤ 4 := by
  simpa [fourFaceSubspace] using
    (finrank_range_le_card
      (fun i : Fin 4 => projectionEuclideanVector (signedRowNormal A (f i))))

def fourFaceProjectionRadius {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ) : Vector p → ℝ :=
  subspaceProjectionRadius (fourFaceSubspace A)

theorem fourFaceProjectionRadius_nonneg {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (z : Vector p) : 0 ≤ fourFaceProjectionRadius A z :=
  norm_nonneg _

theorem measurable_fourFaceProjectionRadius {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) : Measurable (fourFaceProjectionRadius A) :=
  measurable_subspaceProjectionRadius _

theorem fourFaceSubspace_projection_norm_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (f : Fin 4 → Face p) (z : Vector p) :
    ‖(fourFaceSubspace A f).orthogonalProjection (projectionEuclideanVector z)‖ ≤
      fourFaceProjectionRadius A z := by
  have h := norm_le_pi_norm
    (fun f : Fin 4 → Face p =>
      ‖(fourFaceSubspace A f).orthogonalProjection (projectionEuclideanVector z)‖) f
  simpa only [Real.norm_of_nonneg (norm_nonneg _)] using h

theorem fourFaceProjectionRadius_add_le {p : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (z d : Vector p) :
    fourFaceProjectionRadius A (z + d) ≤
      fourFaceProjectionRadius A z + ‖projectionEuclideanVector d‖ := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg (fourFaceProjectionRadius_nonneg A z)
    (norm_nonneg _))).mpr
  intro f
  rw [Real.norm_of_nonneg (norm_nonneg _)]
  have hadd : projectionEuclideanVector (z + d) =
      projectionEuclideanVector z + projectionEuclideanVector d := rfl
  rw [hadd, map_add]
  apply (norm_add_le _ _).trans
  apply add_le_add (fourFaceSubspace_projection_norm_le A f z)
  exact ((fourFaceSubspace A f).orthogonalProjection.le_opNorm _).trans
    ((mul_le_mul_of_nonneg_right (fourFaceSubspace A f).orthogonalProjection_norm_le
      (norm_nonneg _)).trans_eq (one_mul _))

theorem orthogonalProjection_norm_mono {p : ℕ}
    {U V : Submodule ℝ (EuclideanSpace ℝ (Fin p))} (hUV : U ≤ V)
    (z : EuclideanSpace ℝ (Fin p)) : ‖U.orthogonalProjection z‖ ≤ ‖V.orthogonalProjection z‖ := by
  rw [← Submodule.orthogonalProjection_orthogonalProjection_of_le hUV z]
  calc
    _ ≤ ‖U.orthogonalProjection‖ * ‖(V.orthogonalProjection z : EuclideanSpace ℝ (Fin p))‖ :=
      U.orthogonalProjection.le_opNorm _
    _ ≤ _ := by
      simpa using mul_le_mul_of_nonneg_right U.orthogonalProjection_norm_le
        (norm_nonneg (V.orthogonalProjection z))

/-- Every span generated by between one and four signed normals is among the
subspaces controlled by the threshold-independent four-tuple radius. -/
theorem smallFaceSpan_projection_norm_le {p q : ℕ}
    (A : Matrix (Fin p) (Fin p) ℝ) (f : Fin q → Face p)
    (hq0 : 0 < q) (hq : q ≤ 4) (z : Vector p) :
    ‖(Submodule.span ℝ (Set.range (fun i =>
        projectionEuclideanVector (signedRowNormal A (f i))))).orthogonalProjection
      (projectionEuclideanVector z)‖ ≤ fourFaceProjectionRadius A z := by
  classical
  let g : Fin 4 → Face p := fun i =>
    if hi : i.val < q then f ⟨i.val, hi⟩ else f ⟨0, hq0⟩
  have hsub : (Set.range (fun i => projectionEuclideanVector (signedRowNormal A (f i)))) ⊆
      Set.range (fun i => projectionEuclideanVector (signedRowNormal A (g i))) := by
    rintro _ ⟨i, rfl⟩
    refine ⟨⟨i.val, lt_of_lt_of_le i.isLt hq⟩, ?_⟩
    simp [g, i.isLt]
  exact (orthogonalProjection_norm_mono (Submodule.span_mono hsub)
    (projectionEuclideanVector z)).trans (fourFaceSubspace_projection_norm_le A g z)

namespace CompatibleFaceTuple

def normalSpan {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) : Submodule ℝ (EuclideanSpace ℝ (Fin p)) :=
  Submodule.span ℝ (Set.range (fun i =>
    projectionEuclideanVector (signedRowNormal A (S.face i))))

theorem abs_inner_normalSpan_le_projectionRadius {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hq0 : 0 < q) (hq : q ≤ 4) {d : EuclideanSpace ℝ (Fin p)}
    (hd : d ∈ S.normalSpan A) (y : Vector p) :
    |⟪d, projectionEuclideanVector y⟫_ℝ| ≤ ‖d‖ * fourFaceProjectionRadius A y := by
  let u : S.normalSpan A := ⟨d, hd⟩
  have heq : ⟪d, projectionEuclideanVector y⟫_ℝ =
      ⟪u, (S.normalSpan A).orthogonalProjection (projectionEuclideanVector y)⟫_ℝ := by
    rw [Submodule.inner_orthogonalProjection_eq_of_mem_left]
  rw [heq]
  exact (abs_real_inner_le_norm u _).trans (mul_le_mul_of_nonneg_left
    (smallFaceSpan_projection_norm_le A S.face hq0 hq y) (norm_nonneg _))

theorem abs_faceDot_normalSpan_le_projectionRadius {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hq0 : 0 < q) (hq : q ≤ 4) {d : Vector p}
    (hd : projectionEuclideanVector d ∈ S.normalSpan A) (y : Vector p) :
    |faceDot d y| ≤ ‖projectionEuclideanVector d‖ * fourFaceProjectionRadius A y := by
  simpa [faceDot, projectionEuclideanVector, PiLp.inner_apply, mul_comm] using
    S.abs_inner_normalSpan_le_projectionRadius A hq0 hq hd y

theorem regressionMean_mem_normalSpan {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (b : Fin q → ℝ) :
    projectionEuclideanVector (S.regressionMean A b) ∈ S.normalSpan A := by
  have heq : projectionEuclideanVector (S.regressionMean A b) =
      ∑ i, ((S.gram (A * A.transpose))⁻¹.mulVec b) i •
        projectionEuclideanVector (signedRowNormal A (S.face i)) := by
    ext j
    change _ = (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin p => ℝ) j)
      (∑ i, ((S.gram (A * A.transpose))⁻¹.mulVec b) i •
        projectionEuclideanVector (signedRowNormal A (S.face i)))
    rw [map_sum]
    simp [projectionEuclideanVector, regressionMean, normalCombination]
  rw [heq]
  exact Submodule.sum_mem _ (fun i _ => Submodule.smul_mem _ _
    (Submodule.subset_span (Set.mem_range_self i)))

/-- The concrete Gaussian regression mean really is the orthogonal
projection onto the active-normal span. -/
theorem regressionMean_eq_orthogonalProjection {p q : ℕ} (S : CompatibleFaceTuple p q)
    (A : Matrix (Fin p) (Fin p) ℝ) (hd : IsUnit (S.gram (A * A.transpose)).det)
    (z : Vector p) :
    ((S.normalSpan A).orthogonalProjection (projectionEuclideanVector z) :
      EuclideanSpace ℝ (Fin p)) =
      projectionEuclideanVector (S.regressionMean A (S.activeScores A z)) := by
  apply Submodule.eq_orthogonalProjection_of_mem_of_inner_eq_zero
    (S.regressionMean_mem_normalSpan A _)
  intro w hw
  change w ∈ Submodule.span ℝ (Set.range (fun i =>
    projectionEuclideanVector (signedRowNormal A (S.face i)))) at hw
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    have h := congrFun (S.activeScores_regressionResidual A hd z) i
    simpa [activeScores, regressionResidual, faceDot,
      projectionEuclideanVector, PiLp.inner_apply, mul_comm] using h
  | zero => simp
  | add x y _ _ hx hy => simp only [inner_add_right, hx, hy, add_zero]
  | smul a x _ hx => simp only [inner_smul_right, hx, mul_zero]

theorem regressionMean_norm_le_fourFaceProjectionRadius {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (hq0 : 0 < q) (hq : q ≤ 4)
    (z : Vector p) :
    ‖projectionEuclideanVector (S.regressionMean A (S.activeScores A z))‖ ≤
      fourFaceProjectionRadius A z := by
  rw [← S.regressionMean_eq_orthogonalProjection A hd z]
  exact smallFaceSpan_projection_norm_le A S.face hq0 hq z

theorem sqrt_radiusSq_eq_norm_regressionMean {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (b : Fin q → ℝ) :
    Real.sqrt (S.radiusSq A b) = ‖projectionEuclideanVector (S.regressionMean A b)‖ := by
  have hnorm : ‖projectionEuclideanVector (S.regressionMean A b)‖ ^ 2 =
      vectorNormSq (S.regressionMean A b) := by
    simpa [projectionEuclideanVector, vectorNormSq, Real.norm_eq_abs, sq_abs] using
      PiLp.norm_sq_eq_of_L2 (fun _ : Fin p => ℝ)
        (projectionEuclideanVector (S.regressionMean A b))
  rw [← S.regressionMean_normSq A hd, ← hnorm, Real.sqrt_sq (norm_nonneg _)]

theorem sqrt_radiusSq_le_fourFaceProjectionRadius {p q : ℕ}
    (S : CompatibleFaceTuple p q) (A : Matrix (Fin p) (Fin p) ℝ)
    (hd : IsUnit (S.gram (A * A.transpose)).det) (hq0 : 0 < q) (hq : q ≤ 4)
    (z : Vector p) : Real.sqrt (S.radiusSq A (S.activeScores A z)) ≤
      fourFaceProjectionRadius A z := by
  rw [S.sqrt_radiusSq_eq_norm_regressionMean A hd]
  exact S.regressionMean_norm_le_fourFaceProjectionRadius A hd hq0 hq z

end CompatibleFaceTuple

private theorem fourFace_basis_card_exp_le {p : ℕ} (hp : 1 ≤ p) :
    2 * (1 + (4 : ℝ) * (Fintype.card (Fin 4 → Face p) : ℝ)) ≤
      Real.exp (8 * dimensionLog p) := by
  have hp1 : 1 ≤ (p : ℝ) := by exact_mod_cast hp
  have hp0 : 0 < (p : ℝ) := by linarith
  have hcard : (Fintype.card (Fin 4 → Face p) : ℝ) = (2 * (p : ℝ)) ^ 4 := by
    simp [Face, Fintype.card_fun, Fintype.card_prod, mul_comm, Nat.cast_pow]
  have hexp1 : 2 ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hexp8 : (256 : ℝ) ≤ Real.exp 8 := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hexp1 8
    norm_num at hh
    simpa only [← Real.exp_nat_mul, show (8 : ℝ) * 1 = 8 by norm_num] using hh
  have hp48 : (p : ℝ) ^ 4 ≤ (p : ℝ) ^ 8 := pow_le_pow_right₀ hp1 (by decide)
  have hp8 : 1 ≤ (p : ℝ) ^ 8 := one_le_pow₀ hp1
  have heq : Real.exp (8 * dimensionLog p) = Real.exp 8 * (p : ℝ) ^ 8 := by
    rw [dimensionLog, Real.log_mul (Real.exp_ne_zero _) hp0.ne', Real.log_exp]
    rw [mul_add, mul_one, Real.exp_add]
    congr 1
    rw [show (8 : ℝ) * Real.log (p : ℝ) = (8 : ℕ) * Real.log (p : ℝ) by norm_num,
      Real.exp_nat_mul, Real.exp_log hp0]
  rw [hcard, heq]
  calc
    2 * (1 + 4 * (2 * (p : ℝ)) ^ 4) ≤ 256 * (p : ℝ) ^ 8 := by
      nlinarith only [hp48, hp8]
    _ ≤ _ := mul_le_mul_of_nonneg_right hexp8 (pow_nonneg hp0.le 8)

/-- Actual version of the projection-radius moment bound used by all four
Gaussian face tubes. It holds for every matrix, including singular ones,
and for every natural moment order. -/
theorem fourFaceProjectionRadius_weighted_moment_le {p : ℕ} (hp : 1 ≤ p)
    (A : Matrix (Fin p) (Fin p) ℝ) {M : ℝ}
    (hM : Real.sqrt (dimensionLog p) ≤ M) (k : ℕ) :
    Integrable (fun z => Real.exp (fourFaceProjectionRadius A z / M) *
      (1 + fourFaceProjectionRadius A z) ^ k) (standardGaussian p) ∧
      (∫ z, Real.exp (fourFaceProjectionRadius A z / M) *
        (1 + fourFaceProjectionRadius A z) ^ k ∂standardGaussian p) ≤
        (Real.sqrt (dimensionLog p)) ^ k * Real.exp (8 + (4 * (k + 1 : ℝ)) ^ 2 / 2) := by
  exact subspaceProjectionRadius_weighted_moment_le (fourFaceSubspace A) 4
    (fourFaceSubspace_finrank_le A) (log_exp_mul_nat_ge_one hp)
    (fourFace_basis_card_exp_le hp) hM k

end
end RectangleCLT
