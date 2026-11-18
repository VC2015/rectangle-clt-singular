import RectangleCLTCompanion.SplitV4.SymmetricFamilyMaximum
import RectangleCLTCompanion.SplitV4.SymmetricFamilyEnvelope

/-! The actual two-count symmetric observations of Appendix F.3.
There are `r` independent leading signs and `m` independent rare signs and
masks. In particular, the construction includes the bounded-width case
`r=1` while the rare maximum still ranges over `m` coordinates. -/

namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Set RectangleCLT RectangleCLT.Companion
open RectangleCLT.Companion.SplitV4
open scoped BigOperators ENNReal
noncomputable section
set_option autoImplicit false

abbrev LowerFamilySeed (r m : ℕ) := FamilySigns r × FamilyRestSeed m

def lowerFamilySeedLaw (P : SymmetricFamilyParameters) (r m : ℕ) :
    Measure (LowerFamilySeed r m) := (familySignLaw r).prod (familyRestLaw P m)

instance lowerFamilySeedLaw_probability (P : SymmetricFamilyParameters) (r m : ℕ) :
    IsProbabilityMeasure (lowerFamilySeedLaw P r m) := by
  unfold lowerFamilySeedLaw
  infer_instance

def lowerFamilyObservation (P : SymmetricFamilyParameters) {r m : ℕ}
    (z : LowerFamilySeed r m) : Vector (r*m) :=
  fun k => P.scale*familySign (z.1 (finProdFinEquiv.symm k).1)+
    familyActivated P z.2 (finProdFinEquiv.symm k).2

def lowerFamilyCovariance (r m : ℕ) (v : ℝ) : Matrix (Fin (r*m)) (Fin (r*m)) ℝ :=
  fun k l => (1-v)*(if (finProdFinEquiv.symm k : Fin r × Fin m).1 =
      (finProdFinEquiv.symm l).1 then 1 else 0)+
    v*(if (finProdFinEquiv.symm k : Fin r × Fin m).2 =
      (finProdFinEquiv.symm l).2 then 1 else 0)

def lowerFamilyArrayLaw (P : SymmetricFamilyParameters) (n r m : ℕ) :
    Measure (Fin n → LowerFamilySeed r m) := Measure.pi (fun _ => lowerFamilySeedLaw P r m)

instance lowerFamilyArrayLaw_probability (P : SymmetricFamilyParameters) (n r m : ℕ) :
    IsProbabilityMeasure (lowerFamilyArrayLaw P n r m) := by
  unfold lowerFamilyArrayLaw
  infer_instance

def lowerFamilyRawObservations (P : SymmetricFamilyParameters) {n r m : ℕ}
    (i : Fin n) (z : Fin n → LowerFamilySeed r m) : Vector (r*m) := lowerFamilyObservation P (z i)

theorem lowerFamilyArray_map_seed (P : SymmetricFamilyParameters) {n r m : ℕ} (i : Fin n) :
    (lowerFamilyArrayLaw P n r m).map (fun z => z i) = lowerFamilySeedLaw P r m :=
  familyPi_map_eval (fun _ : Fin n => lowerFamilySeedLaw P r m) i

theorem lowerFamilyRawObservations_independent (P : SymmetricFamilyParameters) (n r m : ℕ) :
    iIndepFun (lowerFamilyRawObservations P (n := n) (r := r) (m := m))
      (lowerFamilyArrayLaw P n r m) :=
  (familyPi_iIndepFun (fun _ : Fin n => lowerFamilySeedLaw P r m)).comp
    (fun _ => lowerFamilyObservation P) (fun _ => measurable_of_finite _)

theorem lowerFamilyRawObservations_identDistrib (P : SymmetricFamilyParameters)
    {n r m : ℕ} (i : Fin n) :
    IdentDistrib (lowerFamilyRawObservations P i : (Fin n → LowerFamilySeed r m) → Vector (r*m))
      (lowerFamilyObservation P) (lowerFamilyArrayLaw P n r m) (lowerFamilySeedLaw P r m) := by
  refine ⟨(measurable_of_finite _).aemeasurable,(measurable_of_finite _).aemeasurable,?_⟩
  rw [show lowerFamilyRawObservations P i = lowerFamilyObservation P ∘ (fun z => z i) from rfl,
    ← Measure.map_map (measurable_of_finite (lowerFamilyObservation P : LowerFamilySeed r m → Vector (r*m)))
      (measurable_pi_apply i),lowerFamilyArray_map_seed]

theorem lowerFamilyRawObservations_iid (P : SymmetricFamilyParameters)
    {n r m : ℕ} (i j : Fin n) :
    IdentDistrib (lowerFamilyRawObservations P i : (Fin n → LowerFamilySeed r m) → Vector (r*m))
      (lowerFamilyRawObservations P j) (lowerFamilyArrayLaw P n r m) (lowerFamilyArrayLaw P n r m) :=
  (lowerFamilyRawObservations_identDistrib P i).trans (lowerFamilyRawObservations_identDistrib P j).symm

def lowerFamilySeedFlip {r m : ℕ} (z : LowerFamilySeed r m) : LowerFamilySeed r m :=
  (familySignFlip z.1,(familySignFlip z.2.1,(z.2.2.1,z.2.2.2)))

theorem lowerFamilySeedFlip_preserving (P : SymmetricFamilyParameters) (r m : ℕ) :
    MeasurePreserving (lowerFamilySeedFlip (r := r) (m := m))
      (lowerFamilySeedLaw P r m) (lowerFamilySeedLaw P r m) := by
  exact (familySignFlip_preserving r).prod
    ((familySignFlip_preserving m).prod ((MeasurePreserving.id (familyBernoulli (familyTheta P))).prod
      (MeasurePreserving.id (familyMaskLaw P m))))

theorem lowerFamilyObservation_seedFlip (P : SymmetricFamilyParameters) {r m : ℕ}
    (z : LowerFamilySeed r m) :
    lowerFamilyObservation P (lowerFamilySeedFlip z) = -lowerFamilyObservation P z := by
  ext k
  simp only [lowerFamilyObservation,familyActivated,lowerFamilySeedFlip,familySignFlip,
    familySign_not,Pi.neg_apply]
  ring

theorem lowerFamilyObservation_centrally_symmetric (P : SymmetricFamilyParameters) (r m : ℕ) :
    IdentDistrib (lowerFamilyObservation P : LowerFamilySeed r m → Vector (r*m))
      (fun z => -lowerFamilyObservation P z) (lowerFamilySeedLaw P r m) (lowerFamilySeedLaw P r m) := by
  have hp := lowerFamilySeedFlip_preserving P r m
  have hh : IdentDistrib (lowerFamilySeedFlip (r := r) (m := m)) id
      (lowerFamilySeedLaw P r m) (lowerFamilySeedLaw P r m) :=
    ⟨hp.aemeasurable,measurable_id.aemeasurable,by rw [hp.map_eq,Measure.map_id]⟩
  have hc := hh.comp (measurable_of_finite (lowerFamilyObservation P))
  simpa only [Function.comp_def,lowerFamilyObservation_seedFlip,id_eq] using hc.symm

theorem lowerFamilyRawObservations_centrally_symmetric (P : SymmetricFamilyParameters)
    {n r m : ℕ} (i : Fin n) :
    IdentDistrib (lowerFamilyRawObservations P i : (Fin n → LowerFamilySeed r m) → Vector (r*m))
      (fun z => -lowerFamilyRawObservations P i z) (lowerFamilyArrayLaw P n r m)
        (lowerFamilyArrayLaw P n r m) := by
  have hi := lowerFamilyRawObservations_identDistrib P (r := r) (m := m) i
  have hn := hi.comp (measurable_neg : Measurable (fun x : Vector (r*m) => -x))
  exact hi.trans ((lowerFamilyObservation_centrally_symmetric P r m).trans hn.symm)

theorem lowerFamilyObservation_norm_le (P : SymmetricFamilyParameters) {r m : ℕ}
    (z : LowerFamilySeed r m) :
    ‖lowerFamilyObservation P z‖ ≤ P.scale+P.amplitude*familyIndicator z.2.2.1 := by
  apply (pi_norm_le_iff_of_nonneg (add_nonneg P.scale_pos.le
    (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _)))).mpr
  intro k
  rw [Real.norm_eq_abs]
  unfold lowerFamilyObservation familyActivated
  calc
    _ ≤ |P.scale*familySign (z.1 (finProdFinEquiv.symm k).1)|+
        |P.amplitude*familyIndicator z.2.2.1*familyIndicator (z.2.2.2 (finProdFinEquiv.symm k).2)*
          familySign (z.2.1 (finProdFinEquiv.symm k).2)| := abs_add _ _
    _ = P.scale+P.amplitude*familyIndicator z.2.2.1*
        familyIndicator (z.2.2.2 (finProdFinEquiv.symm k).2) := by
      rw [abs_mul,abs_familySign,abs_of_pos P.scale_pos,mul_one,
        abs_mul,abs_familySign,mul_one,abs_of_nonneg
          (mul_nonneg (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg _)) (familyIndicator_nonneg _))]
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left (familyIndicator_le_one (z.2.2.2 (finProdFinEquiv.symm k).2))
        (mul_nonneg P.amplitude_pos.le (familyIndicator_nonneg z.2.2.1))
      simpa only [mul_one] using add_le_add_left hh P.scale

theorem lowerFamilyObservation_envelope (P : SymmetricFamilyParameters) {r m : ℕ}
    (z : LowerFamilySeed r m) : ‖lowerFamilyObservation P z‖ ≤ P.scale+P.amplitude :=
  (lowerFamilyObservation_norm_le P z).trans
    (add_le_add_left ((mul_le_mul_of_nonneg_left (familyIndicator_le_one _) P.amplitude_pos.le).trans_eq
      (mul_one _)) _)

end
end RectangleCLTArxivV1
