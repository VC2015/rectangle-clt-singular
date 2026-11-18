import GenericChaining
import Mathlib.Analysis.Normed.Group.Constructions
import Mathlib.Data.Matrix.Mul

/-!
# The signed-coordinate index of Lemma C.2

The indices retain all coordinate signs and a separate zero base point.
Canonical distance may identify their vector images, while the discrete
metric always uses equality of the original indices.
-/

namespace RectangleCLTArxivV1

open MeasureTheory
open scoped BigOperators NNReal ENNReal

/-- The original zero and signed-coordinate indices; no metric quotient is taken. -/
abbrev SignedIndex (p : ℕ) := Option (Bool × Fin p)

@[simp] theorem signedIndex_card (p : ℕ) : Fintype.card (SignedIndex p) = 2 * p + 1 := by
  simp [SignedIndex, Nat.add_comm]

/-- Zero, a positive coordinate (`true`), or its negative (`false`). -/
def signedCoordinate {p : ℕ} : SignedIndex p → (Fin p → ℝ) → ℝ
  | none, _ => 0
  | some (true, j), x => x j
  | some (false, j), x => -x j

@[simp] theorem signedCoordinate_none {p : ℕ} (x : Fin p → ℝ) :
    signedCoordinate none x = 0 := rfl
@[simp] theorem signedCoordinate_pos {p : ℕ} (j : Fin p) (x : Fin p → ℝ) :
    signedCoordinate (some (true, j)) x = x j := rfl
@[simp] theorem signedCoordinate_neg {p : ℕ} (j : Fin p) (x : Fin p → ℝ) :
    signedCoordinate (some (false, j)) x = -x j := rfl

/-- The signed-coordinate process associated with a vector-valued random variable. -/
def signedProcess {p : ℕ} {Ω : Type*} (W : Ω → Fin p → ℝ) (t : SignedIndex p) (ω : Ω) : ℝ :=
  signedCoordinate t (W ω)

@[simp] theorem signedProcess_none {p : ℕ} {Ω : Type*} (W : Ω → Fin p → ℝ) (ω : Ω) :
    signedProcess W none ω = 0 := rfl

/-- The same zero and sign choices applied to any vector family. -/
def signedVectors {p : ℕ} {E : Type*} [Zero E] [Neg E] (a : Fin p → E) : SignedIndex p → E
  | none => 0
  | some (true, j) => a j
  | some (false, j) => -a j

@[simp] theorem signedVectors_none {p : ℕ} {E : Type*} [Zero E] [Neg E] (a : Fin p → E) :
    signedVectors a none = 0 := rfl
@[simp] theorem signedVectors_pos {p : ℕ} {E : Type*} [Zero E] [Neg E] (a : Fin p → E) (j : Fin p) :
    signedVectors a (some (true, j)) = a j := rfl
@[simp] theorem signedVectors_neg {p : ℕ} {E : Type*} [Zero E] [Neg E] (a : Fin p → E) (j : Fin p) :
    signedVectors a (some (false, j)) = -a j := rfl

/-- The discrete metric distinguishes every original signed index. -/
def signedDiscreteMetric {p : ℕ} (δ : ℝ≥0) (s t : SignedIndex p) : ℝ≥0 :=
  if s = t then 0 else δ

theorem signedDiscreteMetric_coe {p : ℕ} (δ : ℝ≥0) (s t : SignedIndex p) :
    (signedDiscreteMetric δ s t : ℝ≥0∞) = GenericChaining.discreteDist (δ : ℝ≥0∞) s t := by
  simp only [signedDiscreteMetric, GenericChaining.discreteDist]
  split <;> rfl

theorem signedCoordinate_add {p : ℕ} (t : SignedIndex p) (x y : Fin p → ℝ) :
    signedCoordinate t (x + y) = signedCoordinate t x + signedCoordinate t y := by
  cases t with
  | none => simp
  | some v =>
    rcases v with ⟨b, j⟩
    cases b
    · simp only [signedCoordinate, Pi.add_apply]
      ring
    · rfl

theorem signedCoordinate_sub {p : ℕ} (t : SignedIndex p) (x y : Fin p → ℝ) :
    signedCoordinate t (x - y) = signedCoordinate t x - signedCoordinate t y := by
  cases t with
  | none => simp
  | some v =>
    rcases v with ⟨b, j⟩
    cases b
    · simp only [signedCoordinate, Pi.sub_apply]
      ring
    · rfl

theorem signedCoordinate_sum {p : ℕ} {I : Type*} (S : Finset I)
    (x : I → Fin p → ℝ) (t : SignedIndex p) :
    signedCoordinate t (∑ i ∈ S, x i) = ∑ i ∈ S, signedCoordinate t (x i) := by
  cases t with
  | none => simp
  | some v => rcases v with ⟨b, j⟩; cases b <;> simp [signedCoordinate, Finset.sum_apply]

/-- Each selected signed coordinate is bounded by the vector infinity norm. -/
theorem abs_signedCoordinate_le_norm {p : ℕ} (t : SignedIndex p) (x : Fin p → ℝ) :
    |signedCoordinate t x| ≤ ‖x‖ := by
  cases t with
  | none => simpa only [signedCoordinate_none, abs_zero] using norm_nonneg x
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simpa [signedCoordinate] using norm_le_pi_norm x j

/-- A common coordinate envelope also bounds the zero and negative indices. -/
theorem abs_signedCoordinate_le {p : ℕ} (t : SignedIndex p) (x : Fin p → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcoord : ∀ j, |x j| ≤ δ) : |signedCoordinate t x| ≤ δ := by
  cases t with
  | none => simpa using hδ
  | some v => rcases v with ⟨b, j⟩; cases b <;> simpa [signedCoordinate] using hcoord j

/-- A contrast of two signed coordinates has envelope twice the original envelope. -/
theorem abs_signedCoordinate_sub_le {p : ℕ} (s t : SignedIndex p) (x : Fin p → ℝ)
    {δ : ℝ} (hδ : 0 ≤ δ) (hcoord : ∀ j, |x j| ≤ δ) :
    |signedCoordinate t x - signedCoordinate s x| ≤ 2 * δ := by
  apply (abs_sub _ _).trans
  linarith [abs_signedCoordinate_le s x hδ hcoord, abs_signedCoordinate_le t x hδ hcoord]

/-- The one-sided signed maximum is the infinity norm, including the empty
coordinate family because the zero base point remains present. -/
theorem signedMaximum_eq_norm {p : ℕ} (x : Fin p → ℝ) :
    (⨆ t : SignedIndex p, signedCoordinate t x) = ‖x‖ := by
  have hnn : 0 ≤ ⨆ t : SignedIndex p, signedCoordinate t x :=
    le_ciSup (Finite.bddAbove_range (fun t : SignedIndex p => signedCoordinate t x)) none
  apply le_antisymm
  · apply ciSup_le
    intro t
    exact (le_abs_self _).trans (abs_signedCoordinate_le_norm t x)
  · apply (pi_norm_le_iff_of_nonneg hnn).mpr
    intro j
    rw [Real.norm_eq_abs]
    apply abs_le.mpr
    constructor
    · have hh := le_ciSup (Finite.bddAbove_range (fun t : SignedIndex p => signedCoordinate t x))
        (some (false, j))
      change -x j ≤ _ at hh
      linarith
    · exact le_ciSup (Finite.bddAbove_range (fun t : SignedIndex p => signedCoordinate t x)) (some (true, j))

/-- Taking absolute values does not change the signed-coordinate maximum. -/
theorem signedAbsMaximum_eq_norm {p : ℕ} (x : Fin p → ℝ) :
    (⨆ t : SignedIndex p, |signedCoordinate t x|) = ‖x‖ := by
  apply le_antisymm
  · exact ciSup_le fun t => abs_signedCoordinate_le_norm t x
  · rw [← signedMaximum_eq_norm x]
    exact ciSup_le fun t => (le_abs_self _).trans (le_ciSup (Finite.bddAbove_range (fun u : SignedIndex p => |signedCoordinate u x|)) t)

/-- The base-point maximum used by Dirksen is exactly the coordinate infinity norm. -/
theorem signed_incrementMaximum_eq_norm {p : ℕ} {Ω : Type*} (W : Ω → Fin p → ℝ) (ω : Ω) :
    GenericChaining.incrementMaximum (signedProcess W) none ω = ‖W ω‖ := by
  simpa only [GenericChaining.incrementMaximum, signedProcess, signedCoordinate_none, sub_zero] using
    signedAbsMaximum_eq_norm (W ω)

/-- Signed-vector evaluation is the signed Gaussian coordinate process. -/
theorem signedGaussianLinear {p r : ℕ} (a : Fin p → EuclideanSpace ℝ (Fin r))
    (t : SignedIndex p) (g : Fin r → ℝ) :
    GenericChaining.gaussianLinear (signedVectors a t) g =
      signedCoordinate t (fun j => GenericChaining.gaussianLinear (a j) g) := by
  cases t with
  | none => simp
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simp [signedVectors, signedCoordinate, GenericChaining.gaussianLinear]

/-- The coordinate contrast in one observation. -/
def signedContrast {p n : ℕ} {Ω : Type*} (ξ : Fin n → Ω → Fin p → ℝ)
    (s t : SignedIndex p) (i : Fin n) (ω : Ω) : ℝ :=
  signedCoordinate t (ξ i ω) - signedCoordinate s (ξ i ω)

theorem signedContrast_sum {p n : ℕ} {Ω : Type*} (ξ : Fin n → Ω → Fin p → ℝ)
    (s t : SignedIndex p) (ω : Ω) :
    (∑ i, signedContrast ξ s t i ω) =
      signedCoordinate t (∑ i, ξ i ω) - signedCoordinate s (∑ i, ξ i ω) := by
  simp only [signedContrast, signedCoordinate_sum, Finset.sum_sub_distrib]

/-- Signed coordinates are measurable functions of the complete vector. -/
theorem signedCoordinate_measurable {p : ℕ} (t : SignedIndex p) : Measurable (signedCoordinate t) := by
  cases t with
  | none => exact measurable_const
  | some v =>
    rcases v with ⟨b, j⟩
    cases b
    · exact (measurable_pi_apply j).neg
    · exact measurable_pi_apply j

theorem signedContrast_measurable {p : ℕ} (s t : SignedIndex p) :
    Measurable (fun x : Fin p → ℝ => signedCoordinate t x - signedCoordinate s x) :=
  (signedCoordinate_measurable t).sub (signedCoordinate_measurable s)

theorem integrable_signedCoordinate {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {W : Ω → Fin p → ℝ}
    (hW : ∀ j, Integrable (fun ω => W ω j) μ) (t : SignedIndex p) :
    Integrable (fun ω => signedCoordinate t (W ω)) μ := by
  cases t with
  | none => exact integrable_zero _ _ _
  | some v =>
    rcases v with ⟨b, j⟩
    cases b
    · exact (hW j).neg
    · exact hW j

theorem integral_signedCoordinate_zero {p : ℕ} {Ω : Type*} [MeasurableSpace Ω]
    {μ : Measure Ω} {W : Ω → Fin p → ℝ}
    (hW : ∀ j, (∫ ω, W ω j ∂μ) = 0) (t : SignedIndex p) :
    (∫ ω, signedCoordinate t (W ω) ∂μ) = 0 := by
  cases t with
  | none => simp
  | some v => rcases v with ⟨b, j⟩; cases b <;> simp [signedCoordinate, integral_neg, hW]


/-- The coordinate direction associated with a signed index. -/
def signedDirection {p : ℕ} (t : SignedIndex p) : Fin p → ℝ :=
  signedVectors (fun j => Pi.single j 1) t

/-- Signed-coordinate evaluation is a genuine linear projection, so its
contrasts can use the archive's projection covariance identities. -/
theorem signedCoordinate_eq_dotProduct {p : ℕ} (t : SignedIndex p) (x : Fin p → ℝ) :
    signedCoordinate t x = dotProduct (signedDirection t) x := by
  classical
  cases t with
  | none => simp [signedDirection]
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simp [signedCoordinate, signedDirection, signedVectors]

theorem signedContrast_eq_dotProduct {p n : ℕ} {Ω : Type*} (ξ : Fin n → Ω → Fin p → ℝ)
    (s t : SignedIndex p) (i : Fin n) (ω : Ω) :
    signedContrast ξ s t i ω = dotProduct (signedDirection t - signedDirection s) (ξ i ω) := by
  simp only [signedContrast, signedCoordinate_eq_dotProduct, sub_dotProduct]

/-- The transpose of a covariance factor maps a signed coordinate direction
onto the corresponding signed row, without any rank assumption. -/
theorem transpose_mulVec_signedDirection {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (t : SignedIndex p) :
    A.transpose.mulVec (signedDirection t) = signedVectors (fun j => A j) t := by
  classical
  cases t with
  | none => simp [signedDirection]
  | some v =>
    rcases v with ⟨b, j⟩
    cases b <;> simp [signedDirection, signedVectors, Matrix.mulVec_single, Matrix.mulVec_neg]

theorem transpose_mulVec_signedContrast {p r : ℕ} (A : Matrix (Fin p) (Fin r) ℝ)
    (s t : SignedIndex p) :
    A.transpose.mulVec (signedDirection t - signedDirection s) =
      signedVectors (fun j => A j) t - signedVectors (fun j => A j) s := by
  rw [Matrix.mulVec_sub, transpose_mulVec_signedDirection, transpose_mulVec_signedDirection]


/-- Opposite signs remain distinct in the discrete metric even when their
canonical vector images coincide. -/
@[simp] theorem signedDiscreteMetric_opposite {p : ℕ} (δ : ℝ≥0) (j k : Fin p) :
    signedDiscreteMetric δ (some (true, j)) (some (false, k)) = δ := by
  simp [signedDiscreteMetric]

@[simp] theorem signedCanonical_pos_pos {p : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (a : Fin p → E) (j k : Fin p) :
    GenericChaining.canonicalDist (signedVectors a) (some (true, j)) (some (true, k)) =
      ‖a j - a k‖₊ := rfl

@[simp] theorem signedCanonical_pos_neg {p : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (a : Fin p → E) (j k : Fin p) :
    GenericChaining.canonicalDist (signedVectors a) (some (true, j)) (some (false, k)) =
      ‖a j + a k‖₊ := by
  simp [GenericChaining.canonicalDist, signedVectors, sub_neg_eq_add]

@[simp] theorem signedCanonical_none_pos {p : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (a : Fin p → E) (j : Fin p) :
    GenericChaining.canonicalDist (signedVectors a) none (some (true, j)) = ‖a j‖₊ := by
  simp [GenericChaining.canonicalDist, signedVectors]

/-- Exact positive correlation can identify different positive indices in
canonical distance without identifying them in the discrete index type. -/
theorem signedCanonical_zero_of_equal {p : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (a : Fin p → E) {j k : Fin p} (h : a j = a k) :
    GenericChaining.canonicalDist (signedVectors a) (some (true, j)) (some (true, k)) = 0 := by
  simp [h]

/-- Exact negative correlation similarly identifies the positive and negative
images; their discrete distance is still the original envelope. -/
theorem signedCanonical_zero_of_opposite {p : ℕ} {E : Type*} [SeminormedAddCommGroup E]
    (a : Fin p → E) {j k : Fin p} (h : a j = -a k) :
    GenericChaining.canonicalDist (signedVectors a) (some (true, j)) (some (false, k)) = 0 := by
  simp [h]

end RectangleCLTArxivV1
