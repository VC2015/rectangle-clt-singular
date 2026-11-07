import RectangleCLTCompanion.SplitV4.SymmetricFamilyFinite
import Mathlib.Probability.IdentDistrib

/-!
Actual laws and moments of the common centrally symmetric masked family
in Lemma F.3. The inputs are the paper's activation probabilities and
amplitude; no moment, covariance or lower-bound conclusion is assumed.
-/

open MeasureTheory ProbabilityTheory Set
open scoped BigOperators ENNReal

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem familyArray_map_seed (P : SymmetricFamilyParameters) {n m : ℕ} (i : Fin n) :
    (familyArrayLaw P n m).map (fun z => z i) = familySeedLaw P m :=
  familyPi_map_eval (fun _ : Fin n => familySeedLaw P m) i

theorem familyRawObservations_independent (P : SymmetricFamilyParameters) (n m : ℕ) :
    iIndepFun (familyRawObservations P (n := n) (m := m)) (familyArrayLaw P n m) :=
  (familyPi_iIndepFun (fun _ : Fin n => familySeedLaw P m)).comp
    (fun _ => familyObservation P) (fun _ => measurable_of_finite _)

theorem familyRawObservations_identDistrib (P : SymmetricFamilyParameters) {n m : ℕ} (i : Fin n) :
    IdentDistrib (familyRawObservations P i : (Fin n → FamilySeed m) → Vector (m * m))
      (familyObservation P) (familyArrayLaw P n m) (familySeedLaw P m) := by
  refine ⟨(measurable_of_finite _).aemeasurable, (measurable_of_finite _).aemeasurable, ?_⟩
  rw [show familyRawObservations P i = (familyObservation P) ∘ (fun z => z i) from rfl,
    ← Measure.map_map (measurable_of_finite (familyObservation P : FamilySeed m → Vector (m * m)))
      (measurable_pi_apply i), familyArray_map_seed]

theorem familyRawObservations_iid (P : SymmetricFamilyParameters) {n m : ℕ} (i k : Fin n) :
    IdentDistrib (familyRawObservations P i : (Fin n → FamilySeed m) → Vector (m * m))
      (familyRawObservations P k) (familyArrayLaw P n m) (familyArrayLaw P n m) :=
  (familyRawObservations_identDistrib P i).trans (familyRawObservations_identDistrib P k).symm

theorem familyRawObservations_centrally_symmetric (P : SymmetricFamilyParameters)
    {n m : ℕ} (i : Fin n) :
    IdentDistrib (familyRawObservations P i : (Fin n → FamilySeed m) → Vector (m * m))
      (fun z => -familyRawObservations P i z) (familyArrayLaw P n m) (familyArrayLaw P n m) := by
  have hi := familyRawObservations_identDistrib P (m := m) i
  have hn := hi.comp (measurable_neg : Measurable (fun x : Vector (m * m) => -x))
  exact hi.trans ((familyObservation_centrally_symmetric P m).trans hn.symm)

theorem familyObservation_norm_le (P : SymmetricFamilyParameters) {m : ℕ} (z : FamilySeed m) :
    ‖familyObservation P z‖ ≤ P.scale + P.amplitude * familyIndicator z.2.2.1 := by
  have hbound : 0 ≤ P.scale + P.amplitude * familyIndicator z.2.2.1 :=
    add_nonneg P.scale_pos.le (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _))
  apply (pi_norm_le_iff_of_nonneg hbound).mpr
  intro r
  rw [Real.norm_eq_abs]
  unfold familyObservation familyActivated
  let ju : Fin m × Fin m := finProdFinEquiv.symm r
  change |P.scale * familySign (z.1 ju.1) +
    P.amplitude * familyIndicator z.2.2.1 * familyIndicator (z.2.2.2 ju.2) * familySign (z.2.1 ju.2)| ≤ _
  calc
    _ ≤ |P.scale * familySign (z.1 ju.1)| +
        |P.amplitude * familyIndicator z.2.2.1 * familyIndicator (z.2.2.2 ju.2) * familySign (z.2.1 ju.2)| :=
      abs_add _ _
    _ = P.scale + P.amplitude * familyIndicator z.2.2.1 * familyIndicator (z.2.2.2 ju.2) := by
      rw [abs_mul, abs_familySign, abs_of_pos P.scale_pos, mul_one,
        abs_mul, abs_familySign, mul_one,
        abs_of_nonneg (mul_nonneg (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _))
          (familyIndicator_nonneg _))]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (familyIndicator_le_one (z.2.2.2 ju.2))
        (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg z.2.2.1))
      simpa only [mul_one] using add_le_add_left hh P.scale

theorem familyObservation_envelope (P : SymmetricFamilyParameters) {m : ℕ} (z : FamilySeed m) :
    ‖familyObservation P z‖ ≤ P.scale + P.amplitude := by
  exact (familyObservation_norm_le P z).trans
    (add_le_add_left ((mul_le_mul_of_nonneg_left (familyIndicator_le_one _) P.amplitude_pos.le).trans_eq
      (mul_one _)) _)

theorem familyRawObservations_norm_le (P : SymmetricFamilyParameters) {n m : ℕ}
    (i : Fin n) (z : Fin n → FamilySeed m) :
    ‖familyRawObservations P i z‖ ≤ P.scale + P.amplitude * familyIndicator (z i).2.2.1 :=
  familyObservation_norm_le P (z i)

end
end RectangleCLT.Companion.SplitV4
