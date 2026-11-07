import RectangleCLTCompanion.LowerProductArray
import RectangleCLTCompanion.SplitV4.PairedNormalization
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Constructions.Pi

/-!
The genuine finite probability model for Lemma F.3.  All signs and masks
are Boolean coordinates under explicit product laws.  The model retains
both activation probabilities, including the unmasked endpoint `pi = 1`.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

structure SymmetricFamilyParameters where
  theta : ℝ
  pi : ℝ
  amplitude : ℝ
  theta_pos : 0 < theta
  theta_le_one : theta ≤ 1
  pi_pos : 0 < pi
  pi_le_one : pi ≤ 1
  amplitude_pos : 0 < amplitude
  variance_lt_half : theta * pi * amplitude ^ 2 < 1 / 2

namespace SymmetricFamilyParameters

def variance (P : SymmetricFamilyParameters) : ℝ := P.theta * P.pi * P.amplitude ^ 2
def scale (P : SymmetricFamilyParameters) : ℝ := Real.sqrt (1 - P.variance)

theorem variance_pos (P : SymmetricFamilyParameters) : 0 < P.variance := by
  unfold variance
  exact mul_pos (mul_pos P.theta_pos P.pi_pos) (sq_pos_of_pos P.amplitude_pos)

theorem scale_pos (P : SymmetricFamilyParameters) : 0 < P.scale := by
  apply Real.sqrt_pos.mpr
  have hv := P.variance_lt_half
  change P.variance < 1 / 2 at hv
  linarith

theorem scale_sq (P : SymmetricFamilyParameters) : P.scale ^ 2 = 1 - P.variance := by
  apply Real.sq_sqrt
  have hv := P.variance_lt_half
  change P.variance < 1 / 2 at hv
  linarith

end SymmetricFamilyParameters

abbrev FamilyProbability := {t : ℝ // 0 ≤ t ∧ t ≤ 1}

def familyBernoulli (t : FamilyProbability) : Measure Bool :=
  ENNReal.ofReal (1 - t.1) • Measure.dirac false + ENNReal.ofReal t.1 • Measure.dirac true

instance familyBernoulli_isProbability (t : FamilyProbability) : IsProbabilityMeasure (familyBernoulli t) where
  measure_univ := by
    simp only [familyBernoulli, Measure.add_apply, Measure.smul_apply,
      Measure.dirac_apply_of_mem (mem_univ _), smul_eq_mul, mul_one]
    rw [← ENNReal.ofReal_add (sub_nonneg.mpr t.2.2) t.2.1]
    simp

def familyHalf : FamilyProbability := ⟨1 / 2, by norm_num, by norm_num⟩
def familyTheta (P : SymmetricFamilyParameters) : FamilyProbability :=
  ⟨P.theta, P.theta_pos.le, P.theta_le_one⟩
def familyPi (P : SymmetricFamilyParameters) : FamilyProbability :=
  ⟨P.pi, P.pi_pos.le, P.pi_le_one⟩

def familySign (b : Bool) : ℝ := if b then 1 else -1
def familyIndicator (b : Bool) : ℝ := if b then 1 else 0

theorem abs_familySign (b : Bool) : |familySign b| = 1 := by cases b <;> norm_num [familySign]
theorem familySign_sq (b : Bool) : familySign b ^ 2 = 1 := by cases b <;> norm_num [familySign]
theorem familySign_fourth (b : Bool) : familySign b ^ 4 = 1 := by cases b <;> norm_num [familySign]
theorem familySign_not (b : Bool) : familySign (!b) = -familySign b := by cases b <;> norm_num [familySign]
theorem familyIndicator_nonneg (b : Bool) : 0 ≤ familyIndicator b := by cases b <;> norm_num [familyIndicator]
theorem familyIndicator_le_one (b : Bool) : familyIndicator b ≤ 1 := by cases b <;> norm_num [familyIndicator]
theorem familyIndicator_sq (b : Bool) : familyIndicator b ^ 2 = familyIndicator b := by cases b <;> norm_num [familyIndicator]
theorem familyIndicator_fourth (b : Bool) : familyIndicator b ^ 4 = familyIndicator b := by cases b <;> norm_num [familyIndicator]

/-- Every function on this actual finite probability model is genuinely
Bochner integrable; no totalized integral is used as a moment assumption. -/
theorem integrable_family_finite {Ω E : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] [NormedAddCommGroup E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (μ : Measure Ω) [IsFiniteMeasure μ] (f : Ω → E) :
    Integrable f μ := by
  apply (integrable_const (∑ ω : Ω, ‖f ω‖)).mono' (measurable_of_finite f).aestronglyMeasurable
  exact ae_of_all _ (fun ω => Finset.single_le_sum (fun w _ => norm_nonneg (f w)) (Finset.mem_univ ω))

theorem integral_familyBernoulli (t : FamilyProbability) (f : Bool → ℝ) :
    (∫ b, f b ∂familyBernoulli t) = (1 - t.1) * f false + t.1 * f true := by
  rw [familyBernoulli, integral_add_measure
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)
    (integrable_dirac.smul_measure ENNReal.ofReal_ne_top)]
  simp only [integral_smul_measure, integral_dirac, ENNReal.toReal_ofReal
    (sub_nonneg.mpr t.2.2), ENNReal.toReal_ofReal t.2.1, smul_eq_mul]

theorem integral_familySign : (∫ b, familySign b ∂familyBernoulli familyHalf) = 0 := by
  rw [integral_familyBernoulli]
  norm_num [familyHalf, familySign]

theorem integral_familyIndicator (t : FamilyProbability) :
    (∫ b, familyIndicator b ∂familyBernoulli t) = t.1 := by
  rw [integral_familyBernoulli]
  simp [familyIndicator]

theorem familyPi_map_eval {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] (i : ι) :
    (Measure.pi ν).map (fun z => z i) = ν i := by
  classical
  ext s hs
  rw [Measure.map_apply (measurable_pi_apply i) hs, ← Set.univ_pi_update_univ, Measure.pi_pi]
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Function.update_of_ne hji]
  · simp

theorem familyPi_iIndepFun {ι E : Type*} [Fintype ι] [MeasurableSpace E]
    (ν : ι → Measure E) [∀ i, IsProbabilityMeasure (ν i)] :
    iIndepFun (fun i (z : ι → E) => z i) (Measure.pi ν) := by
  apply (iIndepFun_iff_map_fun_eq_pi_map (fun i => (measurable_pi_apply i).aemeasurable)).mpr
  simp_rw [familyPi_map_eval ν]
  exact Measure.map_id

theorem familyBernoulli_half_not_preserving :
    MeasurePreserving Bool.not (familyBernoulli familyHalf) (familyBernoulli familyHalf) := by
  refine ⟨measurable_of_finite _, ?_⟩
  simp only [familyBernoulli, Measure.map_add _ _ (measurable_of_finite _), Measure.map_smul,
    Measure.map_dirac (measurable_of_finite _), Bool.not_false, Bool.not_true]
  norm_num [familyHalf]
  exact add_comm _ _

abbrev FamilySigns (m : ℕ) := Fin m → Bool
abbrev FamilySeed (m : ℕ) := FamilySigns m × (FamilySigns m × (Bool × FamilySigns m))

def familySignLaw (m : ℕ) : Measure (FamilySigns m) := Measure.pi (fun _ => familyBernoulli familyHalf)
def familyMaskLaw (P : SymmetricFamilyParameters) (m : ℕ) : Measure (FamilySigns m) :=
  Measure.pi (fun _ => familyBernoulli (familyPi P))

instance familySignLaw_isProbability (m : ℕ) : IsProbabilityMeasure (familySignLaw m) := by
  unfold familySignLaw
  infer_instance
instance familyMaskLaw_isProbability (P : SymmetricFamilyParameters) (m : ℕ) :
    IsProbabilityMeasure (familyMaskLaw P m) := by
  unfold familyMaskLaw
  infer_instance

def familyRestLaw (P : SymmetricFamilyParameters) (m : ℕ) :
    Measure (FamilySigns m × (Bool × FamilySigns m)) :=
  (familySignLaw m).prod ((familyBernoulli (familyTheta P)).prod (familyMaskLaw P m))

instance familyRestLaw_isProbability (P : SymmetricFamilyParameters) (m : ℕ) :
    IsProbabilityMeasure (familyRestLaw P m) := by unfold familyRestLaw; infer_instance

def familySeedLaw (P : SymmetricFamilyParameters) (m : ℕ) : Measure (FamilySeed m) :=
  (familySignLaw m).prod (familyRestLaw P m)

instance familySeedLaw_isProbability (P : SymmetricFamilyParameters) (m : ℕ) :
    IsProbabilityMeasure (familySeedLaw P m) := by unfold familySeedLaw; infer_instance

def familyActivated (P : SymmetricFamilyParameters) {m : ℕ}
    (z : FamilySigns m × (Bool × FamilySigns m)) (u : Fin m) : ℝ :=
  P.amplitude * familyIndicator z.2.1 * familyIndicator (z.2.2 u) * familySign (z.1 u)

def familyObservation (P : SymmetricFamilyParameters) {m : ℕ} (z : FamilySeed m) : Vector (m * m) :=
  fun r => let ju : Fin m × Fin m := finProdFinEquiv.symm r
    P.scale * familySign (z.1 ju.1) + familyActivated P z.2 ju.2

def familyCovariance (m : ℕ) (v : ℝ) : Matrix (Fin (m * m)) (Fin (m * m)) ℝ :=
  fun r r' => let ju : Fin m × Fin m := finProdFinEquiv.symm r
    let ju' : Fin m × Fin m := finProdFinEquiv.symm r'
    (1 - v) * (if ju.1 = ju'.1 then 1 else 0) + v * (if ju.2 = ju'.2 then 1 else 0)

def familyArrayLaw (P : SymmetricFamilyParameters) (n m : ℕ) : Measure (Fin n → FamilySeed m) :=
  Measure.pi (fun _ => familySeedLaw P m)

instance familyArrayLaw_isProbability (P : SymmetricFamilyParameters) (n m : ℕ) :
    IsProbabilityMeasure (familyArrayLaw P n m) := by
  constructor
  simp [familyArrayLaw, Measure.pi_univ]

def familyRawObservations (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (z : Fin n → FamilySeed m) : Vector (m * m) := familyObservation P (z i)

def familySignFlip {m : ℕ} (z : FamilySigns m) : FamilySigns m := fun j => !(z j)
def familySeedFlip {m : ℕ} (z : FamilySeed m) : FamilySeed m :=
  (familySignFlip z.1, (familySignFlip z.2.1, (z.2.2.1, z.2.2.2)))

theorem familySignFlip_preserving (m : ℕ) :
    MeasurePreserving (familySignFlip (m := m)) (familySignLaw m) (familySignLaw m) :=
  measurePreserving_pi (fun _ : Fin m => familyBernoulli familyHalf)
    (fun _ : Fin m => familyBernoulli familyHalf) (fun _ => familyBernoulli_half_not_preserving)

theorem familySeedFlip_preserving (P : SymmetricFamilyParameters) (m : ℕ) :
    MeasurePreserving (familySeedFlip (m := m)) (familySeedLaw P m) (familySeedLaw P m) := by
  have hp := (familySignFlip_preserving m).prod
    ((familySignFlip_preserving m).prod ((MeasurePreserving.id (familyBernoulli (familyTheta P))).prod
      (MeasurePreserving.id (familyMaskLaw P m))))
  exact hp

theorem familyObservation_seedFlip (P : SymmetricFamilyParameters) {m : ℕ} (z : FamilySeed m) :
    familyObservation P (familySeedFlip z) = -familyObservation P z := by
  ext r
  simp only [familyObservation, familyActivated, familySeedFlip, familySignFlip,
    familySign_not, Pi.neg_apply]
  ring

theorem familyObservation_centrally_symmetric (P : SymmetricFamilyParameters) (m : ℕ) :
    IdentDistrib (familyObservation P : FamilySeed m → Vector (m * m))
      (fun z => -familyObservation P z) (familySeedLaw P m) (familySeedLaw P m) := by
  have hp := familySeedFlip_preserving P m
  have hh : IdentDistrib (familySeedFlip (m := m)) id (familySeedLaw P m) (familySeedLaw P m) :=
    ⟨hp.aemeasurable, measurable_id.aemeasurable, by rw [hp.map_eq, Measure.map_id]⟩
  have hc := hh.comp (measurable_of_finite (familyObservation P))
  simpa only [Function.comp_def, familyObservation_seedFlip, id_eq] using hc.symm

end
end RectangleCLT.Companion.SplitV4
