import RectangleCLTArxivV1.SupplementalGScoreRestoration

/-! Signed restoration for an arbitrary symmetric matrix score. Both H2
and H3 use the same actual copy averaging and common-base series. -/
namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section
set_option autoImplicit false

theorem capMatrixScore_copy_integrable
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b : ℝ}
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) (hb : ∀ i ω, |c i ω| ≤ b)
    (M : Matrix (Fin r) (Fin r) ℝ) (i : Fin n) :
    Integrable (fun ω => c i ω*matrixQuadratic M (Z i ω)) μ := by
  have hi := integrable_finset_sum Finset.univ (fun j _ =>
    integrable_finset_sum Finset.univ (fun k _ =>
      (integrable_restorationCoefficient_entry μ Z c hZ hc hb i j k).mul_const (M j k)))
  convert hi using 1
  funext ω
  simp only [matrixQuadratic,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  ring

theorem capMatrix_copy_integral_bound
    {Ω : Type*} [MeasurableSpace Ω] {n r : ℕ} (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ) {b K : ℝ}
    (hZ : ∀ i j k, Integrable (fun ω => Z i ω j*Z i ω k) μ)
    (hc : ∀ i, AEStronglyMeasurable (c i) μ) (hb : ∀ i ω, |c i ω| ≤ b) (hb0 : 0 ≤ b)
    (hbudget : ∀ x : Vector r, ∑ i, ∫ ω, (faceDot x (Z i ω))^2 ∂μ ≤ K*vectorNormSq x)
    (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    |∑ i, ∫ ω, c i ω*matrixQuadratic M (Z i ω) ∂μ| ≤ (b*K)*symmetricNuclearNorm M := by
  rw [← trace_restorationCoefficient_mul μ Z c hZ hc hb M]
  exact abs_trace_mul_le_nuclear_of_quadratic _ M hM
    (abs_matrixQuadratic_restorationCoefficient_le μ Z c hZ hc hb hb0 hbudget)

theorem capMatrix_restoration_order_bound
    {Ω : Type*} [MeasurableSpace Ω] {p r n k : ℕ}
    (s : FaceSmoother p) (μ : Measure Ω)
    (Z : Fin n → Ω → Vector r) (c : Fin n → Ω → ℝ)
    (v : Fin n → Ω → Vector p) (α : Fin k → Face p)
    (hZ : ∀ i j l, Integrable (fun ω => Z i ω j*Z i ω l) μ)
    (hc : ∀ i, Measurable (c i)) (hv : ∀ i, Measurable (v i))
    {b K R : ℝ} (hb : 0 ≤ b) (hK : 0 ≤ K) (hR : 0 ≤ R)
    (hcb : ∀ i ω, |c i ω| ≤ b) (hvb : ∀ i ω, ‖v i ω‖ ≤ R)
    (hbudget : ∀ y : Vector r, ∑ i, ∫ ω, (faceDot y (Z i ω))^2 ∂μ ≤ K*vectorNormSq y)
    (x : Vector p) (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) (ℓ : ℕ) :
    |∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      restorationSeriesTerm s α x (v i ω) ℓ ∂μ| ≤
      (((k+ℓ).choose ℓ : ℝ)*(Real.exp (R/s.bandwidth)-1)^ℓ)*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (M))*
        selectorTupleWeight s α x := by
  let η := Real.exp (R/s.bandwidth)-1
  let E := Real.exp ((k : ℝ)*R/s.bandwidth)
  let a : ℝ := (-1 : ℝ)^ℓ*((k+ℓ).choose ℓ : ℝ)
  let w (β : Fin ℓ → Face p) := selectorTupleWeight s α x*∏ j, s.pi x (β j)
  let d (β : Fin ℓ → Face p) (i : Fin n) (ω : Ω) :=
    c i ω*restorationTranslationCoefficient s α β (v i ω)
  let D := b*E*η^ℓ*K*symmetricNuclearNorm (M)
  have hη : 0 ≤ η := sub_nonneg.mpr (Real.one_le_exp_iff.mpr (div_nonneg hR s.bandwidth_pos.le))
  have hN := symmetricNuclearNorm_nonneg (M)
  have hD : 0 ≤ D := by dsimp only [D,E]; positivity
  have hdm (β : Fin ℓ → Face p) (i : Fin n) : Measurable (d β i) :=
    (hc i).mul (measurable_restorationTranslationCoefficient_comp s α β (v i) (hv i))
  have hdb (β : Fin ℓ → Face p) (i : Fin n) (ω : Ω) : |d β i ω| ≤ b*E*η^ℓ := by
    dsimp only [d]
    rw [abs_mul]
    exact (mul_le_mul (hcb i ω) (abs_restorationTranslationCoefficient_le s α β hR (hvb i ω))
      (abs_nonneg _) hb).trans_eq (by dsimp only [E,η]; ring)
  have hi (β : Fin ℓ → Face p) (i : Fin n) :
      Integrable (fun ω => d β i ω*matrixQuadratic M (Z i ω)) μ :=
    capMatrixScore_copy_integrable μ Z (d β) hZ
      (fun i => (hdm β i).aestronglyMeasurable) (hdb β) M i
  have ht (β : Fin ℓ → Face p) :
      |∑ i, ∫ ω, d β i ω*matrixQuadratic M (Z i ω) ∂μ| ≤ D := by
    exact capMatrix_copy_integral_bound μ Z (d β) hZ
      (fun i => (hdm β i).aestronglyMeasurable) (hdb β) (by positivity) hbudget M hM
  have hw (β : Fin ℓ → Face p) : 0 ≤ w β := mul_nonneg (selectorTupleWeight_nonneg s α x)
    (Finset.prod_nonneg (fun j _ => (s.weights x).pi_nonneg _))
  have hs : (∑ β : Fin ℓ → Face p, w β) ≤ selectorTupleWeight s α x := by
    dsimp only [w]
    rw [← Finset.mul_sum]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (sum_prod_pi_le_one s ℓ x)
      (selectorTupleWeight_nonneg s α x)
  have he (i : Fin n) (ω : Ω) :
      (c i ω*matrixQuadratic M (Z i ω))*restorationSeriesTerm s α x (v i ω) ℓ =
      a*∑ β : Fin ℓ → Face p, w β*(d β i ω*matrixQuadratic M (Z i ω)) := by
    unfold restorationSeriesTerm
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro β _
    dsimp only [a,w,d]
    ring
  have heq : (∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      restorationSeriesTerm s α x (v i ω) ℓ ∂μ) =
      a*∑ β : Fin ℓ → Face p, w β*(∑ i, ∫ ω, d β i ω*matrixQuadratic M (Z i ω) ∂μ) := by
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


theorem capMatrix_translated_copy_bound
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
    (hsmall : R/s.bandwidth < Real.log 2) (x : Vector p) (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    |∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (M))*
        selectorTupleWeight s α x := by
  have hm (i : Fin n) : Measurable (fun ω => c i ω*matrixQuadratic M (Z i ω)) := by
    unfold matrixQuadratic
    fun_prop
  have hi (i : Fin n) := cap_single_restoration_series_interchange s μ α
    (fun ω => c i ω*matrixQuadratic M (Z i ω)) (hm i)
    (capMatrixScore_copy_integrable μ Z c hZ
      (fun i => (hc i).aestronglyMeasurable) hcb M i)
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
      symmetricNuclearNorm (M))).mul_right (selectorTupleWeight s α x))
    (fun ℓ => by
      rw [Real.norm_eq_abs]
      exact capMatrix_restoration_order_bound s μ Z c v α hZ hc hv hb hK hR hcb hvb
        hbudget x M hM ℓ)
  simpa only [Real.norm_eq_abs,η] using hh


theorem capMatrix_translated_copy_bound_ae
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
    (hsmall : R/s.bandwidth < Real.log 2) (x : Vector p) (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    |∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*
        (b*K*Real.exp ((k : ℝ)*R/s.bandwidth)*symmetricNuclearNorm (M))*
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
  have he : (∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      selectorTupleWeight s α (x+v i ω) ∂μ) =
      ∑ i, ∫ ω, (c' i ω*matrixQuadratic M (Z i ω))*
        selectorTupleWeight s α (x+v' i ω) ∂μ := by
    apply Finset.sum_congr rfl
    intro i _
    apply integral_congr_ae
    filter_upwards [hcb i,hvb i] with ω hcω hvω
    simp only [c',v',if_pos (And.intro hcω hvω)]
  rw [he]
  exact capMatrix_translated_copy_bound s μ Z c' v' α hZm hZ hcm hvm
    hb hK hR hcc hvv hbudget hsmall x M hM


theorem capMatrix_translated_copy_bound_numeric
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
    (hsmall : R/s.bandwidth ≤ Real.log (3/2 : ℝ)) (x : Vector p) (M : Matrix (Fin r) (Fin r) ℝ) (hM : M.IsHermitian) :
    |∑ i, ∫ ω, (c i ω*matrixQuadratic M (Z i ω))*
      selectorTupleWeight s α (x+v i ω) ∂μ| ≤
      (2*3^k*b*K)*symmetricNuclearNorm (M)*selectorTupleWeight s α x := by
  have hsmall' : R/s.bandwidth < Real.log 2 := hsmall.trans_lt
    (Real.log_lt_log (by norm_num) (by norm_num))
  have ht := capMatrix_translated_copy_bound_ae s μ Z c v α hZm hZ hc hv
    hb hK hR hcb hvb hbudget hsmall' x M hM
  have hn := symmetricNuclearNorm_nonneg (M)
  have hw := selectorTupleWeight_nonneg s α x
  apply ht.trans
  calc
    _ = ((1/(1-(Real.exp (R/s.bandwidth)-1))^(k+1))*Real.exp ((k : ℝ)*R/s.bandwidth))*
        (b*K*symmetricNuclearNorm (M)*selectorTupleWeight s α x) := by ring
    _ ≤ (2*3^k)*(b*K*symmetricNuclearNorm (M)*selectorTupleWeight s α x) :=
      mul_le_mul_of_nonneg_right (cap_restoration_factor_bound s k hsmall) (by positivity)
    _ = _ := by ring


end
end RectangleCLTArxivV1
