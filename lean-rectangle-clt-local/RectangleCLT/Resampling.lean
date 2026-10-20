import Kane
import RectangleCLT.Smoother
import RectangleCLT.Optimization
import Mathlib.Data.List.FinRange

/-! The deterministic conditioning step in the resampling argument: choosing
one of two fixed observations at each index turns rectangle membership into an
intersection of affine halfspaces on a Boolean cube. -/

open scoped BigOperators

namespace RectangleCLT

/-- Select the left observation at a true bit and the right observation at a
false bit, then sum the selected observations coordinatewise. -/
def resampledSum {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (x : Kane.Cube n) : Fin p → ℝ :=
  fun j => ∑ i, if x i then left i j else right i j

noncomputable def resamplingCenter {n p : ℕ} (left right : Fin n → (Fin p → ℝ)) (j : Fin p) : ℝ :=
  ∑ i, (left i j + right i j) / 2

noncomputable def resamplingWeight {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (j : Fin p) (i : Fin n) : ℝ := (left i j - right i j) / 2

/-- Each coordinate of the selected sum is an affine Boolean linear form. -/
theorem resampledSum_eq_center_add_score {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) (j : Fin p) :
    resampledSum left right x j = resamplingCenter left right j +
      ∑ i, resamplingWeight left right j i * (if x i then (1 : ℝ) else -1) := by
  unfold resampledSum resamplingCenter resamplingWeight
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  cases hx : x i <;> simp [hx] <;> ring

/-- A closed lower coordinate constraint on the selected sum. -/
noncomputable def resamplingLowerHalfspace {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (j : Fin p) (lo : ℝ) : Kane.Halfspace n where
  weights := resamplingWeight left right j
  threshold := lo - resamplingCenter left right j

/-- A closed upper coordinate constraint on the selected sum. -/
noncomputable def resamplingUpperHalfspace {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (j : Fin p) (hi : ℝ) : Kane.Halfspace n where
  weights i := -resamplingWeight left right j i
  threshold := resamplingCenter left right j - hi

theorem resamplingLowerHalfspace_mem {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) (j : Fin p) (lo : ℝ) :
    (resamplingLowerHalfspace left right j lo).threshold ≤
        (resamplingLowerHalfspace left right j lo).score x ↔
      lo ≤ resampledSum left right x j := by
  have h := resampledSum_eq_center_add_score left right x j
  change lo - resamplingCenter left right j ≤
    (∑ i, resamplingWeight left right j i * (if x i then (1 : ℝ) else -1)) ↔ _
  constructor <;> intro hx <;> linarith

theorem resamplingUpperHalfspace_mem {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) (j : Fin p) (hi : ℝ) :
    (resamplingUpperHalfspace left right j hi).threshold ≤
        (resamplingUpperHalfspace left right j hi).score x ↔
      resampledSum left right x j ≤ hi := by
  have h := resampledSum_eq_center_add_score left right x j
  change resamplingCenter left right j - hi ≤
    (∑ i, -resamplingWeight left right j i * (if x i then (1 : ℝ) else -1)) ↔ _
  simp only [neg_mul, Finset.sum_neg_distrib]
  constructor <;> intro hx <;> linarith

/-- Boolean membership in a closed finite box. Empty or reversed intervals
are allowed, and all boundary points are included. -/
noncomputable def resampledClosedBox {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (lo hi : Fin p → ℝ) (x : Kane.Cube n) : Bool := by
  classical
  exact decide (∀ j, lo j ≤ resampledSum left right x j ∧ resampledSum left right x j ≤ hi j)

/-- The `2p` affine halfspaces representing a resampled closed box. -/
noncomputable def resampledBoxHalfspaces {n p : ℕ} (left right : Fin n → (Fin p → ℝ))
    (lo hi : Fin p → ℝ) : List (Kane.Halfspace n) :=
  ((List.finRange p).map fun j => resamplingLowerHalfspace left right j (lo j)) ++
    ((List.finRange p).map fun j => resamplingUpperHalfspace left right j (hi j))

@[simp] theorem resampledBoxHalfspaces_length {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (lo hi : Fin p → ℝ) :
    (resampledBoxHalfspaces left right lo hi).length = 2 * p := by
  simp [resampledBoxHalfspaces, two_mul]

private theorem intersection_true_iff {n : ℕ} (hs : List (Kane.Halfspace n))
    (x : Kane.Cube n) :
    Kane.intersection hs x = true ↔ ∀ h ∈ hs, h.indicator x = true := by
  induction hs with
  | nil => simp [Kane.intersection]
  | cons h hs ih => simp [Kane.intersection, ih]

/-- Closed-box membership is exactly the intersection of the `2p` halfspaces;
the equivalence includes points on either boundary. -/
theorem resampledBoxHalfspaces_indicator {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (lo hi : Fin p → ℝ) :
    Kane.intersection (resampledBoxHalfspaces left right lo hi) =
      resampledClosedBox left right lo hi := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [intersection_true_iff]
  simp only [resampledClosedBox, decide_eq_true_eq]
  simp only [resampledBoxHalfspaces, List.forall_mem_append,
    List.forall_mem_map, Kane.Halfspace.indicator, decide_eq_true_eq,
    resamplingLowerHalfspace_mem, resamplingUpperHalfspace_mem]
  constructor
  · rintro ⟨hl, hu⟩ j
    exact ⟨hl j (List.mem_finRange j), hu j (List.mem_finRange j)⟩
  · intro h
    exact ⟨fun j _ => (h j).1, fun j _ => (h j).2⟩

/-- The conditioning step of the resampling estimate for a closed box. This is
a deterministic Boolean-noise estimate for fixed pairs of observations. -/
theorem resampledClosedBox_noiseSensitivity_le {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (lo hi : Fin p → ℝ)
    (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    Kane.noiseSensitivity (resampledClosedBox left right lo hi) θ ≤
      4 * Real.sqrt (2 * θ * Real.log ((2 * p : ℕ) + (1 : ℝ))) := by
  rw [← resampledBoxHalfspaces_indicator]
  simpa only [resampledBoxHalfspaces_length] using
    Kane.halfspaces_noiseSensitivity_le (resampledBoxHalfspaces left right lo hi) θ hθ hθone

private theorem resampling_dimensionLog_bound (p : ℕ) (hp : 1 ≤ p) (θ : ℝ)
    (hθ : 0 ≤ θ) :
    4 * Real.sqrt (2 * θ * Real.log ((2 * p : ℕ) + (1 : ℝ))) ≤
      8 * Real.sqrt (θ * Real.log (Real.exp 1 * (p : ℝ))) := by
  have hlog : Real.log ((2 * p : ℕ) + (1 : ℝ)) ≤
      2 * Real.log (Real.exp 1 * (p : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      log_two_mul_nat_add_one_le_two_log_exp_mul hp
  have hinside : 2 * θ * Real.log ((2 * p : ℕ) + (1 : ℝ)) ≤
      4 * (θ * Real.log (Real.exp 1 * (p : ℝ))) := by
    have hh := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * θ)
    nlinarith
  have hfour : Real.sqrt (4 : ℝ) = 2 := by
    have hh := Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)
    norm_num at hh
    exact hh
  calc
    _ ≤ 4 * Real.sqrt (4 * (θ * Real.log (Real.exp 1 * (p : ℝ)))) :=
      mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by norm_num)
    _ = _ := by
      rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 4), hfour]
      ring

/-- The closed-box resampling estimate with the dimension logarithm `log(ep)`
used in the rectangle CLT. -/
theorem resampledClosedBox_noiseSensitivity_le_dimensionLog {n p : ℕ}
    (left right : Fin n → (Fin p → ℝ)) (lo hi : Fin p → ℝ) (hp : 1 ≤ p)
    (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    Kane.noiseSensitivity (resampledClosedBox left right lo hi) θ ≤
      8 * Real.sqrt (θ * Real.log (Real.exp 1 * (p : ℝ))) :=
  (resampledClosedBox_noiseSensitivity_le left right lo hi θ hθ hθone).trans
    (resampling_dimensionLog_bound p hp θ hθ.le)

namespace FaceSmoother

/-- The affine cube halfspace associated with one signed coordinate face. -/
noncomputable def resamplingHalfspace {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (f : Face p) : Kane.Halfspace n :=
  if f.2 then resamplingUpperHalfspace left right f.1 (s.offsets f)
    else resamplingLowerHalfspace left right f.1 (-s.offsets f)

theorem resamplingHalfspace_mem {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) (f : Face p) :
    (s.resamplingHalfspace left right f).threshold ≤
        (s.resamplingHalfspace left right f).score x ↔
      s.faceScore f (resampledSum left right x) ≤ 0 := by
  rcases f with ⟨j, b⟩
  cases b
  · simp only [resamplingHalfspace, Bool.false_eq_true, ↓reduceIte,
      resamplingLowerHalfspace_mem, faceScore, normalDot]
    constructor <;> intro hx <;> linarith
  · simp only [resamplingHalfspace, ↓reduceIte, resamplingUpperHalfspace_mem,
      faceScore, normalDot]
    constructor <;> intro hx <;> linarith

/-- Cube halfspaces for the selected finite collection of faces. -/
noncomputable def resamplingHalfspaces {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) : List (Kane.Halfspace n) :=
  s.faces.toList.map (s.resamplingHalfspace left right)

@[simp] theorem resamplingHalfspaces_length {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) :
    (s.resamplingHalfspaces left right).length = s.faces.card := by
  simp [resamplingHalfspaces]

/-- There are at most two distinct signed coordinate faces per dimension. -/
theorem faces_card_le (s : FaceSmoother p) : s.faces.card ≤ 2 * p := by
  simpa [Face, Nat.mul_comm] using s.faces.card_le_univ

/-- Boolean membership of the selected sum in the closed rectangle described
by a finite face collection. -/
noncomputable def resampledMembership {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) : Bool := by
  classical
  exact decide (s.Inside (resampledSum left right x))

/-- The Boolean membership agrees with the smoother's real-valued rectangle
indicator, so the conditioning bound can be used with its endpoint estimates. -/
@[simp] theorem boolVal_resampledMembership {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (x : Kane.Cube n) :
    Kane.boolVal (s.resampledMembership left right x) =
      s.indicator (resampledSum left right x) := by
  classical
  simp [Kane.boolVal, resampledMembership, indicator]

/-- Exact intersection representation, including missing faces and boundary
points. No independence or moment assumptions are used in this identity. -/
theorem resamplingHalfspaces_indicator {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) :
    Kane.intersection (s.resamplingHalfspaces left right) =
      s.resampledMembership left right := by
  classical
  funext x
  apply Bool.eq_iff_iff.mpr
  rw [intersection_true_iff]
  simp only [resampledMembership, decide_eq_true_eq, resamplingHalfspaces,
    List.forall_mem_map, Finset.mem_toList, Kane.Halfspace.indicator,
    resamplingHalfspace_mem, Inside]

/-- The deterministic resampling bound in terms of the actual number of faces. -/
theorem resampledMembership_noiseSensitivity_le_faces {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    Kane.noiseSensitivity (s.resampledMembership left right) θ ≤
      4 * Real.sqrt (2 * θ * Real.log ((s.faces.card : ℝ) + 1)) := by
  rw [← resamplingHalfspaces_indicator]
  simpa only [resamplingHalfspaces_length] using
    Kane.halfspaces_noiseSensitivity_le (s.resamplingHalfspaces left right) θ hθ hθone

/-- The deterministic resampling bound needed after fixing the two samples:
membership is a function of the selector bits with at most `2p` faces. -/
theorem resampledMembership_noiseSensitivity_le {n p : ℕ} (s : FaceSmoother p)
    (left right : Fin n → (Fin p → ℝ)) (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    Kane.noiseSensitivity (s.resampledMembership left right) θ ≤
      4 * Real.sqrt (2 * θ * Real.log ((2 * p : ℕ) + (1 : ℝ))) := by
  have hcard : (s.faces.card : ℝ) ≤ (2 * p : ℕ) := by exact_mod_cast s.faces_card_le
  have hlog := Real.log_le_log
    (by positivity : (0 : ℝ) < (s.faces.card : ℝ) + 1) (add_le_add_right hcard 1)
  have hinside := mul_le_mul_of_nonneg_left hlog (by positivity : 0 ≤ 2 * θ)
  exact (s.resampledMembership_noiseSensitivity_le_faces left right θ hθ hθone).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hinside) (by norm_num))

/-- The finite-face conditioning estimate with `log(ep)`, ready to combine
with the analytic endpoint bounds for the rectangle smoother. -/
theorem resampledMembership_noiseSensitivity_le_dimensionLog {n p : ℕ}
    (s : FaceSmoother p) (left right : Fin n → (Fin p → ℝ)) (hp : 1 ≤ p)
    (θ : ℝ) (hθ : 0 < θ) (hθone : θ ≤ 1) :
    Kane.noiseSensitivity (s.resampledMembership left right) θ ≤
      8 * Real.sqrt (θ * Real.log (Real.exp 1 * (p : ℝ))) :=
  (s.resampledMembership_noiseSensitivity_le left right θ hθ hθone).trans
    (resampling_dimensionLog_bound p hp θ hθ.le)

end FaceSmoother

end RectangleCLT
