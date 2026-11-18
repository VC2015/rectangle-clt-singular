import RectangleCLTArxivV1.SupplementalGHermite
import RectangleCLTCompanion.SplitV4.RestorationConditionalInterchange
import RectangleCLTCompanion.SplitV4.NuclearTraceDual

/-! Signed third-Hermite restoration. The random directions need only their
actual second moments; Gaussian polynomial integrability is proved below.
The common-base series is expanded before any absolute trace estimate. -/

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem capThirdHermiteMatrix_integrable {r : ℕ} (u : Vector r) (j k : Fin r) :
    Integrable (fun g => capThirdHermiteMatrix u g j k) (standardGaussian r) := by
  have htrip := standardGaussian_integrable_faceDot_triple u (localBasisVector j) (localBasisVector k)
  have he (l : Fin r) : faceDot (localBasisVector l) = (fun g : Vector r => g l) := by
    funext g
    simp [faceDot, localBasisVector]
  simp_rw [he] at htrip
  have hu := standardGaussian_integrable_faceDot u
  have hj := standardGaussian_integrable_coordinate r j
  have hk := standardGaussian_integrable_coordinate r k
  convert ((htrip.sub (hu.mul_const (if j=k then 1 else 0))).sub (hk.const_mul (u j))).sub
    (hj.mul_const (u k)) using 1
  funext g
  dsimp only [Pi.sub_apply,capThirdHermiteMatrix]
  ring

theorem integrable_matrixQuadratic_product
    {Ω Ξ : Type*} [MeasurableSpace Ω] [MeasurableSpace Ξ] {r : ℕ}
    (μ : Measure Ω) (ν : Measure Ξ) [SFinite ν]
    (Z : Ω → Vector r) (M : Ξ → Matrix (Fin r) (Fin r) ℝ)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) μ)
    (hM : ∀ j k, Integrable (fun x => M x j k) ν) :
    Integrable (fun z : Ω × Ξ => matrixQuadratic (M z.2) (Z z.1)) (μ.prod ν) := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ => (hZ j k).mul_prod (hM j k)))
  convert hi using 1
  funext z
  simp only [matrixQuadratic]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem measurable_capThirdHermiteScore_product
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (u : Vector r)
    (Z : Ω → Vector r) (hZ : Measurable Z) :
    Measurable (fun z : Ω × Vector r => capThirdHermiteScore u (Z z.1) z.2) := by
  unfold capThirdHermiteScore repeatedDirectionScore faceDot vectorNormSq
  fun_prop

theorem integrable_random_capThirdHermiteScore
    {Ω : Type*} [MeasurableSpace Ω] {r : ℕ} (μ : Measure Ω) [IsProbabilityMeasure μ]
    (u : Vector r) (Z : Ω → Vector r)
    (hZ : ∀ j k, Integrable (fun ω => Z ω j*Z ω k) μ) :
    Integrable (fun z : Ω × Vector r => capThirdHermiteScore u (Z z.1) z.2)
      (μ.prod (standardGaussian r)) := by
  simpa only [capThirdHermiteScore_eq_matrixQuadratic] using
    integrable_matrixQuadratic_product μ (standardGaussian r) Z
      (capThirdHermiteMatrix u) hZ (capThirdHermiteMatrix_integrable u)

/-- The finite copy expectation is paired with the actual signed H3 matrix.
Neither the copy-dependent multiplier nor its sign is discarded. -/
theorem capThirdHermite_copy_integral_eq_trace
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) (hb : ∀ i ω, |c i ω| ≤ b)
    (u g : Vector r) :
    (∑ i, ∫ ω, c i ω*capThirdHermiteScore u (Z i ω) g ∂μ) =
      Matrix.trace (restorationCoefficient μ Z c*capThirdHermiteMatrix u g) := by
  simp_rw [capThirdHermiteScore_eq_matrixQuadratic]
  exact (trace_restorationCoefficient_mul μ Z c hZ hc hb _).symm

theorem capThirdHermite_copy_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b K : ℝ}
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) (hb : ∀ i ω, |c i ω| ≤ b) (hb0 : 0 ≤ b)
    (hbudget : ∀ x : Vector r, ∑ i, ∫ ω, (faceDot x (Z i ω))^2 ∂μ ≤ K*vectorNormSq x)
    (u g : Vector r) :
    |∑ i, ∫ ω, c i ω*capThirdHermiteScore u (Z i ω) g ∂μ| ≤
      (b*K)*symmetricNuclearNorm (capThirdHermiteMatrix u g) := by
  rw [capThirdHermite_copy_integral_eq_trace μ Z c hZ hc hb]
  apply abs_trace_mul_le_nuclear_of_quadratic
  · simpa only [Matrix.IsHermitian,Matrix.conjTranspose_eq_transpose_of_trivial] using
      capThirdHermiteMatrix_symmetric u g
  · exact abs_matrixQuadratic_restorationCoefficient_le μ Z c hZ hc hb hb0 hbudget

theorem integrable_weighted_capThirdHermiteScore_copy
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) (hb : ∀ i ω, |c i ω| ≤ b)
    (u g : Vector r) (i : Fin n) :
    Integrable (fun ω => c i ω*capThirdHermiteScore u (Z i ω) g) μ := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (integrable_restorationCoefficient_entry μ Z c hZ hc hb i j k).mul_const
        (capThirdHermiteMatrix u g j k)))
  convert hi using 1
  funext ω
  rw [capThirdHermiteScore_eq_matrixQuadratic]
  simp only [matrixQuadratic,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

/-- At one common Gaussian point, a complete translation-series order
is controlled after the signed copy averages, without counting the extra
selector tuples. The original selector weight is retained. -/
theorem capThirdHermite_restoration_order_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (α : Fin k → Face p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (hc : ∀ i, Measurable (c i)) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i ω, |c i ω| ≤ b) (hvb : ∀ i ω, ‖v i ω‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ω, (faceDot y (Z i ω))^2 ∂μ ≤ K*vectorNormSq y)
    (x : Vector p) (u g : Vector r) (ℓ : ℕ) :
    |∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      restorationSeriesTerm s α x (v i ω) ℓ ∂μ| ≤
      (((k+ℓ).choose ℓ : ℝ)*(Real.exp (R/s.bandwidth)-1)^ℓ)*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (capThirdHermiteMatrix u g))*
        selectorTupleWeight s α x := by
  let η := Real.exp (R/s.bandwidth)-1
  let E := Real.exp ((k : ℝ)*R/s.bandwidth)
  let a : ℝ := (-1 : ℝ)^ℓ*((k+ℓ).choose ℓ : ℝ)
  let w (β : Fin ℓ → Face p) := selectorTupleWeight s α x*∏ j, s.pi x (β j)
  let d (β : Fin ℓ → Face p) (i : Fin n) (ω : Ω) :=
    c i ω*restorationTranslationCoefficient s α β (v i ω)
  let D := b*E*η^ℓ*K*symmetricNuclearNorm (capThirdHermiteMatrix u g)
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hN := symmetricNuclearNorm_nonneg (capThirdHermiteMatrix u g)
  have hD : 0 ≤ D := by dsimp only [D,E]; positivity
  have hdm (β : Fin ℓ → Face p) (i : Fin n) : Measurable (d β i) :=
    (hc i).mul (measurable_restorationTranslationCoefficient_comp s α β (v i) (hv i))
  have hdb (β : Fin ℓ → Face p) (i : Fin n) (ω : Ω) : |d β i ω| ≤ b*E*η^ℓ := by
    dsimp only [d]
    rw [abs_mul]
    exact (mul_le_mul (hcb i ω) (abs_restorationTranslationCoefficient_le s α β hR (hvb i ω))
      (abs_nonneg _) hb).trans_eq (by dsimp only [E,η]; ring)
  have hi (β : Fin ℓ → Face p) (i : Fin n) :
      Integrable (fun ω => d β i ω*capThirdHermiteScore u (Z i ω) g) μ :=
    integrable_weighted_capThirdHermiteScore_copy μ Z (d β) hZ
      (fun i => (hdm β i).aestronglyMeasurable) (hdb β) u g i
  have ht (β : Fin ℓ → Face p) :
      |∑ i, ∫ ω, d β i ω*capThirdHermiteScore u (Z i ω) g ∂μ| ≤ D := by
    exact capThirdHermite_copy_integral_bound μ Z (d β) hZ
      (fun i => (hdm β i).aestronglyMeasurable) (hdb β) (by positivity) hbudget u g
  have hw (β : Fin ℓ → Face p) : 0 ≤ w β := mul_nonneg (selectorTupleWeight_nonneg s α x)
    (Finset.prod_nonneg (fun j _ => (s.weights x).pi_nonneg _))
  have hs : (∑ β : Fin ℓ → Face p, w β) ≤ selectorTupleWeight s α x := by
    dsimp only [w]
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (sum_prod_pi_le_one s ℓ x)
      (selectorTupleWeight_nonneg s α x)
  have he (i : Fin n) (ω : Ω) :
      (c i ω*capThirdHermiteScore u (Z i ω) g)*restorationSeriesTerm s α x (v i ω) ℓ =
      a*∑ β : Fin ℓ → Face p, w β*(d β i ω*capThirdHermiteScore u (Z i ω) g) := by
    unfold restorationSeriesTerm
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    dsimp only [a,w,d]
    ring
  have heq : (∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      restorationSeriesTerm s α x (v i ω) ℓ ∂μ) =
      a*∑ β : Fin ℓ → Face p, w β*(∑ i, ∫ ω, d β i ω*capThirdHermiteScore u (Z i ω) g ∂μ) := by
    simp_rw [he,integral_const_mul]
    rw [← Finset.mul_sum]
    congr 1
    simp_rw [integral_finset_sum _ (fun β _ => (hi β _).const_mul (w β)),integral_const_mul]
    rw [Finset.sum_comm]
    simp only [Finset.mul_sum]
  rw [heq,abs_mul]
  have ha : |a| = ((k+ℓ).choose ℓ : ℝ) := by dsimp only [a]; simp [abs_mul,abs_pow]
  rw [ha]
  calc
    _ ≤ ((k+ℓ).choose ℓ : ℝ)*∑ β : Fin ℓ → Face p, w β*D := by
      apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro β _
      rw [abs_mul,abs_of_nonneg (hw β)]
      exact mul_le_mul_of_nonneg_left (ht β) (hw β)
    _ ≤ ((k+ℓ).choose ℓ : ℝ)*(D*selectorTupleWeight s α x) := by
      rw [← Finset.sum_mul]
      exact mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_right hs hD).trans_eq (mul_comm _ _)) (Nat.cast_nonneg _)
    _ = _ := by dsimp only [D,E,η]; ring

/-- A fixed selector tuple may be restored against any genuinely
integrable signed coefficient. -/
theorem cap_single_restoration_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) (α : Fin k → Face p)
    (d : Ω → ℝ) (hdm : Measurable d) (hdi : Integrable d μ)
    (v : Ω → Vector p) (hv : Measurable v) (x : Vector p)
    {R : ℝ} (hR : 0 ≤ R) (hvb : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun ω => d ω*selectorTupleWeight s α (x+v ω)) μ ∧
    (∀ ℓ, Integrable (fun ω => d ω*restorationSeriesTerm s α x (v ω) ℓ) μ) ∧
    HasSum (fun ℓ => ∫ ω, d ω*restorationSeriesTerm s α x (v ω) ℓ ∂μ)
      (∫ ω, d ω*selectorTupleWeight s α (x+v ω) ∂μ) := by
  classical
  let c (β : Fin k → Face p) (ω : Ω) := if β=α then d ω else 0
  have hcm (β : Fin k → Face p) : Measurable (c β) := by
    dsimp only [c]
    split_ifs <;> fun_prop
  have hcb (β : Fin k → Face p) : ∀ᵐ ω ∂μ, |c β ω| ≤ |d ω| :=
    ae_of_all _ (fun ω => by dsimp only [c]; split_ifs <;> simp)
  have hi := integrable_translated_selector_sum_of_domination s μ c (fun _ => x) v
    (fun ω => |d ω|) hcm measurable_const hv hdi.abs (fun _ => abs_nonneg _) hcb
  have ho := integrable_restorationSeries_sum_of_domination s μ c (fun _ => x) v
    (fun ω => |d ω|) hcm measurable_const hv hdi.abs (fun _ => abs_nonneg _) hcb hR hvb
  have hs := hasSum_integral_restorationSeries_ae s μ c (fun _ => x) v
    (fun ω => |d ω|) hcm measurable_const hv hdi.abs (fun _ => abs_nonneg _) hcb hR hvb hsmall
  simpa [c] using And.intro hi (And.intro ho hs)

/-- Signed copy averaging is performed before the absolute estimate. The
entire convergent restoration series preserves the original selector weight. -/
theorem capThirdHermite_translated_copy_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (α : Fin k → Face p)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (hc : ∀ i, Measurable (c i)) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i ω, |c i ω| ≤ b) (hvb : ∀ i ω, ‖v i ω‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ω, (faceDot y (Z i ω))^2 ∂μ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth < Real.log 2) (x : Vector p) (u g : Vector r) :
    |∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (capThirdHermiteMatrix u g))*
        selectorTupleWeight s α x := by
  have hm (i : Fin n) : Measurable (fun ω => c i ω*capThirdHermiteScore u (Z i ω) g) := by
    unfold capThirdHermiteScore repeatedDirectionScore faceDot vectorNormSq
    fun_prop
  have hi (i : Fin n) := cap_single_restoration_series_interchange s μ α
    (fun ω => c i ω*capThirdHermiteScore u (Z i ω) g) (hm i)
    (integrable_weighted_capThirdHermiteScore_copy μ Z c hZ
      (fun i => (hc i).aestronglyMeasurable) hcb u g i)
    (v i) (hv i) x hR (ae_of_all _ (hvb i)) hsmall
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => (hi i).2.2)
  let η := Real.exp (R/s.bandwidth)-1
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hη₁ : η < 1 := by
    have he := Real.exp_lt_exp.mpr hsmall
    rw [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at he
    dsimp only [η]
    linarith
  have ht := hasSum_restoration_matrix_majorant k (C := 1) (η := η)
    (by norm_num) hη (by simpa only [one_mul] using hη₁)
  simp only [one_mul] at ht
  have hh := hs.norm_le_of_bounded
    ((ht.mul_right (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*
      symmetricNuclearNorm (capThirdHermiteMatrix u g))).mul_right (selectorTupleWeight s α x))
    (fun ℓ => by
      rw [Real.norm_eq_abs]
      exact capThirdHermite_restoration_order_bound s μ Z c v α hZ hc hv hb hK hR hcb hvb
        hbudget x u g ℓ)
  simpa only [Real.norm_eq_abs,η] using hh

/-- The sharp translated copy bound requires only almost-sure coefficient
and displacement bounds. Null-set clipping leaves the actual expectation intact. -/
theorem capThirdHermite_translated_copy_bound_ae
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (α : Fin k → Face p)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (hc : ∀ i, Measurable (c i)) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ω, (faceDot y (Z i ω))^2 ∂μ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth < Real.log 2) (x : Vector p) (u g : Vector r) :
    |∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (capThirdHermiteMatrix u g))*
        selectorTupleWeight s α x := by
  classical
  let c' (i : Fin n) (ω : Ω) := if |c i ω|≤b ∧ ‖v i ω‖≤R then c i ω else 0
  let v' (i : Fin n) (ω : Ω) := if |c i ω|≤b ∧ ‖v i ω‖≤R then v i ω else 0
  have hm (i : Fin n) : MeasurableSet {ω | |c i ω|≤b ∧ ‖v i ω‖≤R} :=
    (measurableSet_le (hc i).abs measurable_const).inter
      (measurableSet_le (hv i).norm measurable_const)
  have hcm (i : Fin n) : Measurable (c' i) := Measurable.ite (hm i) (hc i) measurable_const
  have hvm (i : Fin n) : Measurable (v' i) := Measurable.ite (hm i) (hv i) measurable_const
  have hcc (i : Fin n) (ω : Ω) : |c' i ω| ≤ b := by
    dsimp only [c']
    split_ifs with h
    · exact h.1
    · simpa only [abs_zero] using hb
  have hvv (i : Fin n) (ω : Ω) : ‖v' i ω‖ ≤ R := by
    dsimp only [v']
    split_ifs with h
    · exact h.2
    · simpa only [norm_zero] using hR
  have he : (∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      selectorTupleWeight s α (x+v i ω) ∂μ) =
      ∑ i, ∫ ω, (c' i ω*capThirdHermiteScore u (Z i ω) g)*
        selectorTupleWeight s α (x+v' i ω) ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hcb i,hvb i] with ω hcω hvω
    simp only [c',v',if_pos (And.intro hcω hvω)]
  rw [he]
  exact capThirdHermite_translated_copy_bound s μ Z c' v' α hZm hZ hcm hvm
    hb hK hR hcc hvv hbudget hsmall x u g

theorem cap_restoration_factor_bound {p : ℕ} (s : FaceSmoother p)
    (k : ℕ) {R : ℝ} (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) :
    (1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*
      Real.exp ((k : ℝ)*R/s.bandwidth) ≤ 2*3^k := by
  have he : Real.exp (R/s.bandwidth) ≤ (3/2 : ℝ) := by
    exact (Real.exp_le_exp.mpr hsmall).trans_eq (Real.exp_log (by norm_num))
  have hd : 0 < 1-(Real.exp (R/s.bandwidth)-1) := by linarith
  have hq : 1/(1-(Real.exp (R/s.bandwidth)-1)) ≤ (2 : ℝ) :=
    (div_le_iff₀ hd).mpr (by linarith)
  have hp := pow_le_pow_left₀ (le_of_lt (one_div_pos.mpr hd)) hq (k+1)
  have hk : Real.exp ((k : ℝ)*R/s.bandwidth) ≤ (3/2 : ℝ)^k := by
    rw [show (k : ℝ)*R/s.bandwidth = (k : ℝ)*(R/s.bandwidth) by ring,
      Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos _).le he k
  calc
    _ ≤ 2^(k+1)*(3/2 : ℝ)^k := by
      rw [one_div_pow] at hp
      exact mul_le_mul hp hk (Real.exp_pos _).le (by positivity)
    _ = 2*3^k := by
      rw [pow_succ]
      calc
        2^k*2*(3/2 : ℝ)^k = 2*(2^k*(3/2 : ℝ)^k) := by ring
        _ = _ := by rw [← mul_pow]; norm_num

/-- A numerical version of the signed translated-copy estimate. -/
theorem capThirdHermite_translated_copy_bound_numeric
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (α : Fin k → Face p)
    (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (hc : ∀ i, Measurable (c i)) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i, ∀ᵐ ω ∂μ, |c i ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ω, (faceDot y (Z i ω))^2 ∂μ ≤ K*vectorNormSq y)
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) (x : Vector p) (u g : Vector r) :
    |∑ i, ∫ ω, (c i ω*capThirdHermiteScore u (Z i ω) g)*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (2*3^k*b*K)*symmetricNuclearNorm (capThirdHermiteMatrix u g)*selectorTupleWeight s α x := by
  have hsmall' : R/s.bandwidth < Real.log 2 := hsmall.trans_lt
    (Real.log_lt_log (by norm_num) (by norm_num))
  have ht := capThirdHermite_translated_copy_bound_ae s μ Z c v α hZm hZ hc hv
    hb hK hR hcb hvb hbudget hsmall' x u g
  have hn := symmetricNuclearNorm_nonneg (capThirdHermiteMatrix u g)
  have hw := selectorTupleWeight_nonneg s α x
  apply ht.trans
  calc
    _ = ((1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*Real.exp ((k : ℝ)*R/s.bandwidth))*
        (b*K*symmetricNuclearNorm (capThirdHermiteMatrix u g)*selectorTupleWeight s α x) := by ring
    _ ≤ (2*3^k)*(b*K*symmetricNuclearNorm (capThirdHermiteMatrix u g)*selectorTupleWeight s α x) :=
      mul_le_mul_of_nonneg_right (cap_restoration_factor_bound s k hsmall) (by positivity)
    _ = _ := by ring

/-- The actual translated H3 contraction has an absolutely dominated
common-base selector series. Its signs are retained through this identity. -/
theorem capThirdHermite_translated_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (u : Vector r) (Z : Ω → Vector r) (hZm : Measurable Z)
    (hZ : ∀ j l, Integrable (fun ω => Z ω j*Z ω l) μ)
    (c : (Fin k → Face p) → Ω → ℝ) (hc : ∀ α, Measurable (c α))
    (v : Ω → Vector p) (hv : Measurable v) {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ α, ∀ᵐ ω ∂μ, |c α ω| ≤ b) (hvb : ∀ᵐ ω ∂μ, ‖v ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ α : Fin k → Face p,
      (c α z.1*capThirdHermiteScore u (Z z.1) z.2)*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ α : Fin k → Face p,
      (c α z.1*capThirdHermiteScore u (Z z.1) z.2)*
        restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v z.1) ℓ)
          (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
      (c α z.1*capThirdHermiteScore u (Z z.1) z.2)*
        restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
        (c α z.1*capThirdHermiteScore u (Z z.1) z.2)*
          selectorTupleWeight s α (A.mulVec z.2+V z.1+v z.1) ∂μ.prod (standardGaussian r)) := by
  let ρ := μ.prod (standardGaussian r)
  let U : Ω × Vector r → Vector p := fun z => A.mulVec z.2+V z.1
  let v' : Ω × Vector r → Vector p := fun z => v z.1
  let c' : (Fin k → Face p) → Ω × Vector r → ℝ :=
    fun α z => c α z.1*capThirdHermiteScore u (Z z.1) z.2
  let D : Ω × Vector r → ℝ := fun z => b*|capThirdHermiteScore u (Z z.1) z.2|
  have hscore := measurable_capThirdHermiteScore_product u Z hZm
  have hc' (α : Fin k → Face p) : Measurable (c' α) :=
    ((hc α).comp measurable_fst).mul hscore
  have hU : Measurable U :=
    ((continuous_const.matrix_mulVec continuous_id).measurable.comp measurable_snd).add
      (hV.comp measurable_fst)
  have hv' : Measurable v' := hv.comp measurable_fst
  have hDi : Integrable D ρ :=
    (integrable_random_capThirdHermiteScore μ u Z hZ).abs.const_mul b
  have hD : ∀ z, 0 ≤ D z := fun _ => mul_nonneg hb (abs_nonneg _)
  have hDm : Measurable D := hscore.abs.const_mul b
  have hcb' (α : Fin k → Face p) : ∀ᵐ z ∂ρ, |c' α z| ≤ D z := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le (hc' α).abs hDm)).mpr
    filter_upwards [hcb α] with ω hω
    exact ae_of_all _ (fun g => by
      change |c α ω*capThirdHermiteScore u (Z ω) g| ≤ b*|capThirdHermiteScore u (Z ω) g|
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hω (abs_nonneg _))
  have hvb' : ∀ᵐ z ∂ρ, ‖v' z‖ ≤ R := by
    apply (Measure.ae_prod_iff_ae_ae (measurableSet_le hv'.norm measurable_const)).mpr
    exact hvb.mono (fun _ hω => ae_of_all _ (fun _ => hω))
  exact ⟨integrable_translated_selector_sum_of_domination s ρ c' U v' D hc' hU hv' hDi hD hcb',
    fun ℓ => integrable_restorationSeries_sum_of_domination s ρ c' U v' D hc' hU hv' hDi hD hcb' hR hvb' ℓ,
    hasSum_integral_restorationSeries_ae s ρ c' U v' D hc' hU hv' hDi hD hcb' hR hvb' hsmall⟩

theorem capThirdHermite_translated_array_series_interchange
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω) [IsProbabilityMeasure μ]
    (A : Matrix (Fin p) (Fin r) ℝ) (V : Ω → Vector p) (hV : Measurable V)
    (u : Vector r) (Z : Fin n → Ω → Vector r) (hZm : ∀ i, Measurable (Z i))
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (c : Fin n → (Fin k → Face p) → Ω → ℝ) (hc : ∀ i α, Measurable (c i α))
    (v : Fin n → Ω → Vector p) (hv : ∀ i, Measurable (v i))
    {b R : ℝ} (hb : 0 ≤ b) (hR : 0 ≤ R)
    (hcb : ∀ i α, ∀ᵐ ω ∂μ, |c i α ω| ≤ b) (hvb : ∀ i, ∀ᵐ ω ∂μ, ‖v i ω‖ ≤ R)
    (hsmall : R/s.bandwidth < Real.log 2) :
    Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
        selectorTupleWeight s α (A.mulVec z.2+V z.1+v i z.1)) (μ.prod (standardGaussian r)) ∧
    (∀ ℓ, Integrable (fun z : Ω × Vector r => ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
        restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v i z.1) ℓ)
          (μ.prod (standardGaussian r))) ∧
    HasSum (fun ℓ => ∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
        restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r))
      (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
        (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
          selectorTupleWeight s α (A.mulVec z.2+V z.1+v i z.1) ∂μ.prod (standardGaussian r)) := by
  have hi (i : Fin n) := capThirdHermite_translated_series_interchange s μ A V hV u
    (Z i) (hZm i) (hZ i) (c i) (hc i) (v i) (hv i) hb hR (hcb i) (hvb i) hsmall
  refine ⟨integrable_finset_sum _ (fun i _ => (hi i).1),
    fun ℓ => integrable_finset_sum _ (fun i _ => (hi i).2.1 ℓ), ?_⟩
  have hs := hasSum_sum (s := Finset.univ) (fun i _ => (hi i).2.2)
  have he (ℓ : ℕ) : (∫ z : Ω × Vector r, ∑ i, ∑ α : Fin k → Face p,
      (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
        restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r)) =
      ∑ i, ∫ z : Ω × Vector r, ∑ α : Fin k → Face p,
        (c i α z.1*capThirdHermiteScore u (Z i z.1) z.2)*
          restorationSeriesTerm s α (A.mulVec z.2+V z.1) (v i z.1) ℓ ∂μ.prod (standardGaussian r) :=
    integral_finset_sum _ (fun i _ => (hi i).2.1 ℓ)
  rw [integral_finset_sum Finset.univ (fun i _ => (hi i).1)]
  simp_rw [he]
  exact hs

end
end RectangleCLTArxivV1
