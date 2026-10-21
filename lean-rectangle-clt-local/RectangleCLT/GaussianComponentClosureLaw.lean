import RectangleCLT.GaussianComponentRestoredArray
import RectangleCLT.ProxyGaussianData

/-! The exact common-space experiment behind the Gaussian-component
limit. Gaussian splitting is an equality of laws. The covariance-restored
bounded array is the image of the raw product experiment under a genuine
coordinatewise truncation map. -/

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace RectangleCLT

noncomputable section

def gaussianComponentRawMarginal
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Measure (Vector p) :=
  Sum.elim (fun i => μ.map (ξ i))
    (Sum.elim (fun _ => gaussianLaw B)
      (restorationColumnMarginal (gaussianComponentRestorationFactor B ((k : ℝ) ^ 2))))

theorem gaussianComponentRawMarginal_isProbability
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ)
    (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
    IsProbabilityMeasure (gaussianComponentRawMarginal μ ξ B k i) := by
  cases i with
  | inl i => exact isProbabilityMeasure_map (hξ i).aemeasurable
  | inr i =>
      cases i with
      | inl i => exact gaussianLaw_isProbability B
      | inr i => exact restorationColumnMarginal_isProbability _ _

def gaussianComponentCutCoordinate {p n : ℕ} (k : ℕ) :
    Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p → Vector p :=
  Sum.elim (fun _ => id) (Sum.elim (fun _ => gaussianComponentIncrement k) (fun _ => id))

def gaussianComponentCutArray {p n : ℕ} (k : ℕ)
    (z : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) :
    Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p :=
  fun i => gaussianComponentCutCoordinate k i (z i)

theorem measurable_gaussianComponentCutArray {p n : ℕ} (k : ℕ) :
    Measurable (gaussianComponentCutArray (p := p) (n := n) k) := by
  apply measurable_pi_lambda
  intro i
  cases i with
  | inl i => exact measurable_pi_apply _
  | inr i =>
      cases i with
      | inl i => exact (measurable_gaussianComponentIncrement k).comp (measurable_pi_apply _)
      | inr i => exact measurable_pi_apply _

theorem gaussianComponentCutArray_measurePreserving
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    MeasurePreserving (gaussianComponentCutArray (p := p) (n := n) k)
      (Measure.pi (gaussianComponentRawMarginal μ ξ B k))
      (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)) := by
  let ν := gaussianComponentRawMarginal μ ξ B k
  let τ := gaussianComponentRestoredMarginal μ ξ B k
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) : IsProbabilityMeasure (τ i) :=
    gaussianComponentRestoredMarginal_isProbability μ ξ hξ B k i
  apply measurePreserving_pi ν τ
  intro i
  cases i with
  | inl i => exact MeasurePreserving.id _
  | inr i =>
      cases i with
      | inl i => exact ⟨measurable_gaussianComponentIncrement k, rfl⟩
      | inr i => exact MeasurePreserving.id _

def gaussianComponentRawOriginalSum {p n : ℕ} (k : ℕ)
    (z : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) : Vector p :=
  (∑ i : Fin n, z (.inl i)) +
    ((k : ℝ) ^ 3)⁻¹ • ∑ i : Fin (k ^ 6), z (.inr (.inl i))

def gaussianComponentRawRestoredSum {p n : ℕ} (k : ℕ)
    (z : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) → Vector p) : Vector p :=
  sumVector (gaussianComponentRestoredArray (p := p) (n := n) k)
    (gaussianComponentCutArray k z)

theorem measurable_gaussianComponentRawOriginalSum {p n : ℕ} (k : ℕ) :
    Measurable (gaussianComponentRawOriginalSum (p := p) (n := n) k) := by
  unfold gaussianComponentRawOriginalSum
  fun_prop

theorem measurable_gaussianComponentRawRestoredSum {p n : ℕ} (k : ℕ) :
    Measurable (gaussianComponentRawRestoredSum (p := p) (n := n) k) := by
  unfold gaussianComponentRawRestoredSum sumVector gaussianComponentRestoredArray
  exact Finset.measurable_sum _ fun i _ =>
    (measurable_pi_apply _).comp (measurable_gaussianComponentCutArray k)

/-- The bounded sum in the raw experiment has exactly the product law
to which the bounded proxy theorem is applied. -/
theorem gaussianComponentRawRestoredSum_law
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (B : Matrix (Fin p) (Fin p) ℝ) (k : ℕ) :
    (Measure.pi (gaussianComponentRawMarginal μ ξ B k)).map
      (gaussianComponentRawRestoredSum (p := p) (n := n) k) =
    (Measure.pi (gaussianComponentRestoredMarginal μ ξ B k)).map
      (sumVector (gaussianComponentRestoredArray (p := p) (n := n) k)) := by
  have hp := gaussianComponentCutArray_measurePreserving μ ξ hξ B k
  rw [← hp.map_eq, Measure.map_map]
  · rfl
  · unfold sumVector gaussianComponentRestoredArray
    exact Finset.measurable_sum _ fun i _ => measurable_pi_apply _
  · exact measurable_gaussianComponentCutArray k

/-- Ignoring the covariance-restoring columns, the raw experiment has
exactly the original bounded-sum Gaussian-convolution law. -/
theorem gaussianComponentRawOriginalSum_law
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (hξ : ∀ i, Measurable (ξ i))
    (hind : iIndepFun ξ μ)
    (B : Matrix (Fin p) (Fin p) ℝ) {k : ℕ} (hk : k ≠ 0) :
    (Measure.pi (gaussianComponentRawMarginal μ ξ B k)).map
      (gaussianComponentRawOriginalSum (p := p) (n := n) k) =
      ((μ.map (sumVector ξ)).prod (gaussianLaw B)).map
        (fun z : Vector p × Vector p => z.1 + z.2) := by
  let ν₀ : Fin n → Measure (Vector p) := fun i => μ.map (ξ i)
  let A := gaussianComponentRestorationFactor B ((k : ℝ) ^ 2)
  let ν₁ : Fin (k ^ 6) ⊕ Fin p → Measure (Vector p) :=
    Sum.elim (fun _ => gaussianLaw B) (restorationColumnMarginal A)
  letI (i : Fin n) : IsProbabilityMeasure (ν₀ i) :=
    isProbabilityMeasure_map (hξ i).aemeasurable
  letI (i : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p)) :
      IsProbabilityMeasure (gaussianComponentRawMarginal μ ξ B k i) :=
    gaussianComponentRawMarginal_isProbability μ ξ hξ B k i
  letI (i : Fin (k ^ 6) ⊕ Fin p) : IsProbabilityMeasure (ν₁ i) := by
    cases i with
    | inl i => exact gaussianLaw_isProbability B
    | inr i => exact restorationColumnMarginal_isProbability A i
  let E₀ := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin n ⊕ (Fin (k ^ 6) ⊕ Fin p) => Vector p)
  let E₁ := MeasurableEquiv.sumPiEquivProdPi
    (fun _ : Fin (k ^ 6) ⊕ Fin p => Vector p)
  have hsplit₀ := measurePreserving_sumPiEquivProdPi
    (gaussianComponentRawMarginal μ ξ B k)
  have hsplit₁ := measurePreserving_sumPiEquivProdPi ν₁
  have hsplit := ((MeasurePreserving.id (Measure.pi ν₀)).prod hsplit₁).comp hsplit₀
  let F : (Fin n → Vector p) ×
      ((Fin (k ^ 6) → Vector p) × (Fin p → Vector p)) → Vector p :=
    fun z => (∑ i, z.1 i) + gaussianComponentSum ((k : ℝ) ^ 3)⁻¹ z.2.1
  have hF : Measurable F := by unfold F gaussianComponentSum; fun_prop
  have hraw : (Measure.pi (gaussianComponentRawMarginal μ ξ B k)).map
      (gaussianComponentRawOriginalSum (p := p) (n := n) k) =
      ((Measure.pi ν₀).prod ((gaussianComponentArrayLaw B (k ^ 6)).prod
        (Measure.pi (restorationColumnMarginal A)))).map F := by
    rw [← hsplit.map_eq, Measure.map_map hF hsplit.measurable]
    rfl
  have horiginal : (Measure.pi ν₀).map (fun z => ∑ i, z i) = μ.map (sumVector ξ) := by
    have harray := (iIndepFun_iff_map_fun_eq_pi_map
      (fun i => (hξ i).aemeasurable)).mp hind
    rw [← harray, Measure.map_map]
    · rfl
    · fun_prop
    · exact measurable_pi_lambda _ hξ
  have hgaussian : ((gaussianComponentArrayLaw B (k ^ 6)).prod
      (Measure.pi (restorationColumnMarginal A))).map
      (fun z => gaussianComponentSum ((k : ℝ) ^ 3)⁻¹ z.1) = gaussianLaw B := by
    calc
      _ = (((gaussianComponentArrayLaw B (k ^ 6)).prod
          (Measure.pi (restorationColumnMarginal A))).map Prod.fst).map
          (gaussianComponentSum ((k : ℝ) ^ 3)⁻¹) := by
        rw [Measure.map_map (measurable_gaussianComponentSum _) measurable_fst]
        rfl
      _ = (gaussianComponentArrayLaw B (k ^ 6)).map
          (gaussianComponentSum ((k : ℝ) ^ 3)⁻¹) := by simp
      _ = gaussianLaw B := gaussianComponentSum_law_sixth B hk
  let H : ((Fin (k ^ 6) → Vector p) × (Fin p → Vector p)) → Vector p :=
    fun z => gaussianComponentSum ((k : ℝ) ^ 3)⁻¹ z.1
  have hH : Measurable H :=
    (measurable_gaussianComponentSum _).comp measurable_fst
  have hprod := Measure.map_prod_map (Measure.pi ν₀)
    ((gaussianComponentArrayLaw B (k ^ 6)).prod (Measure.pi (restorationColumnMarginal A)))
    (f := fun z => ∑ i, z i) (g := H) (by fun_prop) hH
  rw [horiginal, hgaussian] at hprod
  rw [hraw, hprod, Measure.map_map (measurable_fst.add measurable_snd) (by fun_prop)]
  rfl

theorem gaussianComponentRawOriginalSum_law_eq
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (ξ : Fin n → Ω → Vector p) (G : Ω → Vector p) {δ : ℝ}
    (B : Matrix (Fin p) (Fin p) ℝ) (h : ProxyHypotheses μ ξ G δ B)
    {k : ℕ} (hk : k ≠ 0) :
    (Measure.pi (gaussianComponentRawMarginal μ ξ B k)).map
      (gaussianComponentRawOriginalSum (p := p) (n := n) k) =
        μ.map (sumWithGaussian ξ G) := by
  rw [gaussianComponentRawOriginalSum_law μ ξ h.boundedIndependent.measurable
    h.boundedIndependent.independent B hk, h.sumWithGaussian_map]

end

end RectangleCLT
