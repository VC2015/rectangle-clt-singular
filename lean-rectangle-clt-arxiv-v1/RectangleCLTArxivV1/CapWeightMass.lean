import RectangleCLTArxivV1.CapLogisticMajorant

/-! Actual single and pair logistic masses from Supplemental G.2. The
intermediate local averaging lemmas are discharged by the proved Fourier
small-box estimates in the raw projected-model endpoints below. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def capPairLaplace (z : ℝ × ℝ) : ℝ := capLaplace z.1*capLaplace z.2

theorem integrable_capPairLaplace : Integrable capPairLaplace :=
  integrable_capLaplace.mul_prod integrable_capLaplace

theorem integral_capPairLaplace : (∫ z : ℝ × ℝ, capPairLaplace z) = 16 := by
  change (∫ z : ℝ × ℝ, capLaplace z.1*capLaplace z.2 ∂(volume : Measure ℝ).prod volume) = 16
  rw [integral_prod_mul,integral_capLaplace]
  norm_num

theorem capLaplace_nonneg (x : ℝ) : 0 ≤ capLaplace x := (Real.exp_pos _).le

theorem capLaplace_le_one (x : ℝ) : capLaplace x ≤ 1 := by
  exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr (by positivity))

theorem capPairLaplace_local (x t : ℝ × ℝ)
    (h0 : |x.1-t.1| ≤ 1) (h1 : |x.2-t.2| ≤ 1) :
    capPairLaplace x ≤ Real.exp 1*capPairLaplace t := by
  have hm := mul_le_mul (capLaplace_local x.1 t.1 h0) (capLaplace_local x.2 t.2 h1)
    (capLaplace_nonneg _) (mul_nonneg (Real.exp_pos _).le (capLaplace_nonneg _))
  have he : Real.exp (1/2)*Real.exp (1/2) = Real.exp 1 := by rw [← Real.exp_add]; norm_num
  unfold capPairLaplace
  apply hm.trans_eq
  calc
    _ = (Real.exp (1/2)*Real.exp (1/2))*(capLaplace t.1*capLaplace t.2) := by ring
    _ = _ := by rw [he]

theorem abs_normalized_sub_le_one (z a t h : ℝ) (hh : 0 < h) :
    |(z-a)/h-t| ≤ 1 ↔ |z-(a+h*t)| ≤ h := by
  have he : (z-a)/h-t = (z-(a+h*t))/h := by field_simp; ring
  rw [he,abs_div,abs_of_pos hh,div_le_iff₀ hh,one_mul]

/-- Uniform interval probabilities control a genuine single Laplace weight. -/
theorem integral_capLaplace_le_of_intervals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (a h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (hsmall : ∀ t, μ.real {ω | |f ω-t| ≤ h} ≤ M) :
    (∫ ω, capLaplace ((f ω-a)/h) ∂μ) ≤ 2*Real.exp (1/2)*M := by
  let F := fun ω => (f ω-a)/h
  have hFm : Measurable F := (hf.sub_const a).div_const h
  have hFi : Integrable (fun ω => capLaplace (F ω)) μ :=
    (integrable_const (1:ℝ)).mono' (hFm.abs.div_const 2 |>.neg.exp).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (capLaplace_nonneg _)]; exact capLaplace_le_one _))
  have hQm : Measurable capLaplace := by unfold capLaplace; fun_prop
  have hp := integral_weight_le_of_local_probability (volume : Measure ℝ) μ F hFm
    (Set.Icc (-1) 1) measurableSet_Icc (by norm_num [Real.volume_Icc])
    capLaplace integrable_capLaplace hQm capLaplace_nonneg (Real.exp (1/2)) M (by positivity) hM
    (fun x t ht => capLaplace_local x t (abs_le.mpr ht))
    (fun t => by
      have he : {ω | F ω-t ∈ Set.Icc (-1) 1} = {ω | |f ω-(a+h*t)| ≤ h} := by
        ext ω
        exact (abs_le.symm).trans (abs_normalized_sub_le_one (f ω) a t h hh)
      rw [he]
      exact hsmall _) hFi
  rw [integral_capLaplace] at hp
  have hvol : (volume (Set.Icc (-1:ℝ) 1)).toReal = 2 := by norm_num [Real.volume_Icc]
  rw [hvol] at hp
  dsimp only [F] at hp
  linarith

/-- Uniform two-coordinate box probabilities control a genuine product weight. -/
theorem integral_capPairLaplace_le_of_boxes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (f : Ω → ℝ × ℝ) (hf : Measurable f) (a b h M : ℝ) (hh : 0 < h) (hM : 0 ≤ M)
    (hsmall : ∀ s t, μ.real {ω | |(f ω).1-s| ≤ h ∧ |(f ω).2-t| ≤ h} ≤ M) :
    (∫ ω, capPairLaplace (((f ω).1-a)/h,((f ω).2-b)/h) ∂μ) ≤ 4*Real.exp 1*M := by
  let F := fun ω => (((f ω).1-a)/h,((f ω).2-b)/h)
  have hFm : Measurable F :=
    ((measurable_fst.comp hf).sub_const a |>.div_const h).prodMk
      ((measurable_snd.comp hf).sub_const b |>.div_const h)
  have hQm : Measurable capPairLaplace := by unfold capPairLaplace capLaplace; fun_prop
  have hQ0 (t : ℝ × ℝ) : 0 ≤ capPairLaplace t := mul_nonneg (capLaplace_nonneg _) (capLaplace_nonneg _)
  have hFi : Integrable (fun ω => capPairLaplace (F ω)) μ :=
    (integrable_const (1:ℝ)).mono' (hQm.comp hFm).aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        rw [Real.norm_eq_abs,abs_of_nonneg (hQ0 _)]
        exact (mul_le_mul (capLaplace_le_one _) (capLaplace_le_one _) (capLaplace_nonneg _) zero_le_one).trans_eq (one_mul _)))
  let B := Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1
  have hB : MeasurableSet B := measurableSet_Icc.prod measurableSet_Icc
  have hvol : (volume B).toReal = 4 := by
    change (((volume : Measure ℝ).prod volume) B).toReal = 4
    dsimp only [B]
    rw [Measure.prod_prod]
    norm_num [Real.volume_Icc]
  have hBfinite : volume B ≠ ⊤ := by
    change ((volume : Measure ℝ).prod volume) B ≠ ⊤
    dsimp only [B]
    rw [Measure.prod_prod]
    norm_num [Real.volume_Icc]
  have hp := integral_weight_le_of_local_probability (volume : Measure (ℝ × ℝ)) μ F hFm B hB hBfinite
    capPairLaplace integrable_capPairLaplace hQm hQ0 (Real.exp 1) M (by positivity) hM
    (fun x t ht => capPairLaplace_local x t (abs_le.mpr ht.1) (abs_le.mpr ht.2))
    (fun t => by
      have he : {ω | F ω-t ∈ B} =
          {ω | |(f ω).1-(a+h*t.1)| ≤ h ∧ |(f ω).2-(b+h*t.2)| ≤ h} := by
        ext ω
        exact and_congr ((abs_le.symm).trans (abs_normalized_sub_le_one (f ω).1 a t.1 h hh))
          ((abs_le.symm).trans (abs_normalized_sub_le_one (f ω).2 b t.2 h hh))
      rw [he]
      exact hsmall _ _) hFi
  rw [integral_capPairLaplace,hvol] at hp
  dsimp only [F] at hp
  linarith

/-- The logistic single-face mass from a uniform actual interval bound. -/
theorem integral_logistic_single_le_of_intervals
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m p : ℕ} (U : Fin m → Vector p) (a : Vector m) {h M : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (Y : Ω → Vector p) (hY : Measurable Y) (j : Fin m)
    (hsmall : ∀ t, μ.real {ω | |faceDot (U j) (Y ω)-t| ≤ h} ≤ M) :
    (∫ ω, logisticTupleWeight U a h ![j] (Y ω) ∂μ) ≤ 2*Real.exp (1/2)*M := by
  have hfj : Measurable (fun ω => faceDot (U j) (Y ω)) := by unfold faceDot; fun_prop
  have hp := integral_capLaplace_le_of_intervals μ _ hfj (a j) h M hh hM hsmall
  have hLi : Integrable (fun ω => logisticTupleWeight U a h ![j] (Y ω)) μ :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_logisticTupleWeight U a h hh ![j]).measurable.comp hY).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact logisticTupleWeight_abs_le_one U a h hh ![j] _))
  have hQi : Integrable (fun ω => capLaplace ((faceDot (U j) (Y ω)-a j)/h)) μ :=
    (integrable_const (1:ℝ)).mono' (((hfj.sub_const (a j)).div_const h).abs.div_const 2 |>.neg.exp).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs,abs_of_nonneg (capLaplace_nonneg _)]; exact capLaplace_le_one _))
  exact (integral_mono hLi hQi (fun ω => logisticTupleWeight_single_le_capLaplace U a h j (Y ω))).trans hp

/-- The logistic pair-face mass from a uniform actual box bound. -/
theorem integral_logistic_pair_le_of_boxes
    {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    {m p : ℕ} (U : Fin m → Vector p) (a : Vector m) {h M : ℝ}
    (hh : 0 < h) (hM : 0 ≤ M) (Y : Ω → Vector p) (hY : Measurable Y) (j k : Fin m)
    (hsmall : ∀ s t, μ.real {ω |
      |faceDot (U j) (Y ω)-s| ≤ h ∧ |faceDot (U k) (Y ω)-t| ≤ h} ≤ M) :
    (∫ ω, logisticTupleWeight U a h ![j,k] (Y ω) ∂μ) ≤ 4*Real.exp 1*M := by
  let f := fun ω => (faceDot (U j) (Y ω),faceDot (U k) (Y ω))
  have hfm : Measurable f := by unfold f faceDot; fun_prop
  have hp := integral_capPairLaplace_le_of_boxes μ f hfm (a j) (a k) h M hh hM hsmall
  have hLi : Integrable (fun ω => logisticTupleWeight U a h ![j,k] (Y ω)) μ :=
    (integrable_const (1:ℝ)).mono'
      ((continuous_logisticTupleWeight U a h hh ![j,k]).measurable.comp hY).aestronglyMeasurable
      (ae_of_all _ (fun ω => by rw [Real.norm_eq_abs]; exact logisticTupleWeight_abs_le_one U a h hh ![j,k] _))
  have hQm : Measurable (fun ω => capPairLaplace (((f ω).1-a j)/h,((f ω).2-a k)/h)) := by
    unfold capPairLaplace capLaplace f faceDot; fun_prop
  have hQi : Integrable (fun ω => capPairLaplace (((f ω).1-a j)/h,((f ω).2-a k)/h)) μ :=
    (integrable_const (1:ℝ)).mono' hQm.aestronglyMeasurable
      (ae_of_all _ (fun ω => by
        unfold capPairLaplace
        rw [Real.norm_eq_abs,abs_of_nonneg (mul_nonneg (capLaplace_nonneg _) (capLaplace_nonneg _))]
        exact (mul_le_mul (capLaplace_le_one _) (capLaplace_le_one _) (capLaplace_nonneg _) zero_le_one).trans_eq (one_mul _)))
  exact (integral_mono hLi hQi (fun ω => logisticTupleWeight_pair_le_capLaplace U a h j k (Y ω))).trans hp

/-- Actual one-face tuple mass: no interval-concentration premise remains. -/
theorem cap_one_face_tuple_mass
    {Ω : Type*} [MeasurableSpace Ω] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {h : ℝ}
    (hvar : (1/2 : ℝ) ≤ capMixedCovariance μ X A 0 0)
    (hh : 0 < h) (hband : δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c : ℝ)
    (hproj : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+c) :
    (∫ z, logisticTupleWeight U a h ![j] (Y z) ∂μ.prod (standardGaussian r)) ≤
      16*Real.exp (1/2)*h*Real.sqrt (Real.pi/capGaussianExponent) := by
  have hp := integral_logistic_single_le_of_intervals (μ.prod (standardGaussian r)) U a hh
    (by positivity : 0 ≤ 8*h*Real.sqrt (Real.pi/capGaussianExponent)) Y hY j (fun t => by
      have he : {z | |faceDot (U j) (Y z)-t| ≤ h} = {z | |capMixedValue X A z 0-(t-c)| ≤ h} := by
        ext z
        simp only [Set.mem_setOf_eq,hproj]
        have he : capMixedValue X A z 0+c-t = capMixedValue X A z 0-(t-c) := by ring
        rw [he]
      rw [he]
      exact cap_one_projection_small_interval hdata A hvar hh hband (t-c))
  exact hp.trans_eq (by ring)

/-- Actual pair-face tuple mass, with the inverse correlation angle and
no small-box-concentration premise. -/
theorem cap_two_face_tuple_mass
    {Ω : Type*} [MeasurableSpace Ω] {r n m p : ℕ}
    {μ : Measure Ω} [IsProbabilityMeasure μ] {X : Fin n → Ω → Vector 2} {δ : ℝ}
    (hdata : BoundedIndependentHypotheses μ X δ)
    (A : Matrix (Fin 2) (Fin r) ℝ) {v ρ h : ℝ}
    (hv : (1/2 : ℝ) ≤ v) (hρ : ρ^2 < 1)
    (hcov : capMixedCovariance μ X A = !![v,v*ρ;v*ρ,v])
    (hh : 0 < h) (hband : 2*δ ≤ h)
    (U : Fin m → Vector p) (a : Vector m) (j k : Fin m)
    (Y : Ω × Vector r → Vector p) (hY : Measurable Y) (c₀ c₁ : ℝ)
    (hproj₀ : ∀ z, faceDot (U j) (Y z) = capMixedValue X A z 0+c₀)
    (hproj₁ : ∀ z, faceDot (U k) (Y z) = capMixedValue X A z 1+c₁) :
    (∫ z, logisticTupleWeight U a h ![j,k] (Y z) ∂μ.prod (standardGaussian r)) ≤
      64*Real.exp 1*Real.pi^3*h^2/Real.sqrt (1-ρ^2) := by
  have hp := integral_logistic_pair_le_of_boxes (μ.prod (standardGaussian r)) U a hh
    (by positivity : 0 ≤ 16*Real.pi^3*h^2/Real.sqrt (1-ρ^2)) Y hY j k (fun s t => by
      have he : {z | |faceDot (U j) (Y z)-s| ≤ h ∧ |faceDot (U k) (Y z)-t| ≤ h} =
          {z | |capMixedValue X A z 0-(s-c₀)| ≤ h ∧ |capMixedValue X A z 1-(t-c₁)| ≤ h} := by
        ext z
        simp only [Set.mem_setOf_eq,hproj₀,hproj₁]
        have he0 : capMixedValue X A z 0+c₀-s = capMixedValue X A z 0-(s-c₀) := by ring
        have he1 : capMixedValue X A z 1+c₁-t = capMixedValue X A z 1-(t-c₁) := by ring
        rw [he0,he1]
      rw [he]
      exact cap_two_projection_small_box hdata A hv hρ hcov hh hband (s-c₀) (t-c₁))
  exact hp.trans_eq (by ring)

end
end RectangleCLTArxivV1
