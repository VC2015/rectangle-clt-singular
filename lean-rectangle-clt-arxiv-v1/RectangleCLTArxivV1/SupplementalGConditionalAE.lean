import RectangleCLTArxivV1.SupplementalGConditional

/-! Joint almost-sure envelopes suffice for the actual seeded copy shifts.
The clipping below changes none of the iterated expectations. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

def capClippedCoefficient {X : Type*} {p : ℕ} (c : X → ℝ) (v : X → Vector p)
    (b R : ℝ) (x : X) : ℝ := if |c x|≤b ∧ ‖v x‖≤R then c x else 0

def capClippedShift {X : Type*} {p : ℕ} (c : X → ℝ) (v : X → Vector p)
    (b R : ℝ) (x : X) : Vector p := if |c x|≤b ∧ ‖v x‖≤R then v x else 0

theorem capClippedCoefficient_measurable {X : Type*} [MeasurableSpace X] {p : ℕ}
    (c : X → ℝ) (v : X → Vector p) (hc : Measurable c) (hv : Measurable v) (b R : ℝ) :
    Measurable (capClippedCoefficient c v b R) :=
  Measurable.ite ((measurableSet_le hc.abs measurable_const).inter
    (measurableSet_le hv.norm measurable_const)) hc measurable_const

theorem capClippedShift_measurable {X : Type*} [MeasurableSpace X] {p : ℕ}
    (c : X → ℝ) (v : X → Vector p) (hc : Measurable c) (hv : Measurable v) (b R : ℝ) :
    Measurable (capClippedShift c v b R) :=
  Measurable.ite ((measurableSet_le hc.abs measurable_const).inter
    (measurableSet_le hv.norm measurable_const)) hv measurable_const

theorem capClippedCoefficient_abs_le {X : Type*} {p : ℕ} (c : X → ℝ) (v : X → Vector p)
    {b R : ℝ} (hb : 0 ≤ b) (x : X) : |capClippedCoefficient c v b R x| ≤ b := by
  unfold capClippedCoefficient
  split_ifs with h
  · exact h.1
  · simpa only [abs_zero] using hb

theorem capClippedShift_norm_le {X : Type*} {p : ℕ} (c : X → ℝ) (v : X → Vector p)
    {b R : ℝ} (hR : 0 ≤ R) (x : X) : ‖capClippedShift c v b R x‖ ≤ R := by
  unfold capClippedShift
  split_ifs with h
  · exact h.2
  · simpa only [norm_zero] using hR

/-- Global clipping preserves the actual base/copy iterated expectation.
The scalar score is arbitrary, so this applies to both Hermite matrices. -/
theorem cap_joint_clipping_iterated_eq
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (κ : Measure Ξ) [SFinite κ]
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hcb : ∀ i, ∀ᵐ z ∂μ.prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂μ.prod κ, ‖v i z‖ ≤ R)
    (score : Fin n → Ξ → ℝ) (x : Ω → Vector p) (α : Fin k → Face p) :
    (∫ ω, ∑ i, ∫ ξ, (c i (ω,ξ)*score i ξ)*selectorTupleWeight s α (x ω+v i (ω,ξ)) ∂κ ∂μ) =
      ∫ ω, ∑ i, ∫ ξ, (capClippedCoefficient (c i) (v i) b R (ω,ξ)*score i ξ)*
        selectorTupleWeight s α (x ω+capClippedShift (c i) (v i) b R (ω,ξ)) ∂κ ∂μ := by
  have ha (i : Fin n) : ∀ᵐ ω ∂μ, ∀ᵐ ξ ∂κ, |c i (ω,ξ)|≤b ∧ ‖v i (ω,ξ)‖≤R := by
    apply (Measure.ae_prod_iff_ae_ae ((measurableSet_le (hc i).abs measurable_const).inter
      (measurableSet_le (hv i).norm measurable_const))).mp
    exact (hcb i).and (hvb i)
  apply integral_congr_ae
  filter_upwards [ae_all_iff.mpr ha] with ω hω
  apply Finset.sum_congr rfl
  intro i _
  apply integral_congr_ae
  filter_upwards [hω i] with ξ hξ
  simp only [capClippedCoefficient,capClippedShift,if_pos hξ]

/-- Conditional signed restoration under the jointly almost-sure
coefficient and shift bounds satisfied by the actual seeded model. -/
theorem capThirdHermite_conditional_mass_bound_ae
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (κ : Measure Ξ) [SFinite κ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (Z : Fin n → Ξ → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ξ => Z i ξ j*Z i ξ l) κ)
    (c : Fin n → Ω × Ξ → ℝ) (hc : ∀ i, Measurable (c i))
    (v : Fin n → Ω × Ξ → Vector p) (hv : ∀ i, Measurable (v i))
    (α : Fin k → Face p) (u : Vector r)
    {b K R M : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R) (hM : 0 ≤ M)
    (hcb : ∀ i, ∀ᵐ z ∂μ.prod κ, |c i z| ≤ b)
    (hvb : ∀ i, ∀ᵐ z ∂μ.prod κ, ‖v i z‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ξ, (faceDot y (Z i ξ))^2 ∂κ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ))
    (hNi : Integrable (fun g => symmetricNuclearNorm (capThirdHermiteMatrix u g)) (standardGaussian r))
    (hmass : ∀ g, ∫ ω, selectorTupleWeight s α (A.mulVec g+V ω) ∂μ ≤ M) :
    Integrable (fun g => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) (standardGaussian r) ∧
    |∫ g, ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ ∂standardGaussian r| ≤
      (2*3^k*b*K)*M*(∫ g, symmetricNuclearNorm (capThirdHermiteMatrix u g) ∂standardGaussian r) := by
  let c' i := capClippedCoefficient (c i) (v i) b R
  let v' i := capClippedShift (c i) (v i) b R
  have ht := capThirdHermite_conditional_mass_bound s μ κ A V hV Z hZm hZ c'
    (fun i => capClippedCoefficient_measurable _ _ (hc i) (hv i) b R) v'
    (fun i => capClippedShift_measurable _ _ (hc i) (hv i) b R) α u hb hK hR hM
    (fun i _ => ae_of_all _ (fun ξ => capClippedCoefficient_abs_le _ _ hb _))
    (fun i _ => ae_of_all _ (fun ξ => capClippedShift_norm_le _ _ hR _)) hbudget hsmall hNi hmass
  have he : (fun g : Vector r => ∫ ω, ∑ i, ∫ ξ,
      (c i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v i (ω,ξ)) ∂κ ∂μ) =
      (fun g : Vector r => ∫ ω, ∑ i, ∫ ξ,
      (c' i (ω,ξ)*capThirdHermiteScore u (Z i ξ) g)*
        selectorTupleWeight s α (A.mulVec g+V ω+v' i (ω,ξ)) ∂κ ∂μ) := by
    funext g
    exact cap_joint_clipping_iterated_eq s μ κ c hc v hv hcb hvb
      (fun i ξ => capThirdHermiteScore u (Z i ξ) g) (fun ω => A.mulVec g+V ω) α
  rw [he]
  exact ht

end
end RectangleCLTArxivV1
