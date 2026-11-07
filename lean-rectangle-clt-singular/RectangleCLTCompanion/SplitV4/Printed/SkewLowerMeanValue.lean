import RectangleCLTCompanion.SplitV4.Printed.SkewLowerProduct
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! The literal intermediate mean-value point used in the printed product
argument. The prefactor limit is checked through the generic first-order
power calculus, independently of every old skew-tail or final lower bound. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4.Printed
noncomputable section

theorem product_power_mean_value (p : ℕ) {t q : ℝ} (htq : t<q) :
    ∃ u∈Ioo t q,(1-q)^p-(1-t)^p=-(p : ℝ)*(1-u)^(p-1)*(q-t) := by
  have hd : ∀x∈Ioo t q,HasDerivAt (fun y : ℝ => (1-y)^p) (-(p : ℝ)*(1-x)^(p-1)) x := by
    intro x hx
    convert (((hasDerivAt_const x (1:ℝ)).sub (hasDerivAt_id x)).pow p) using 1 <;> simp only [id_eq] <;> ring
  obtain ⟨u,hu,he⟩ := exists_hasDerivAt_eq_slope (fun y : ℝ => (1-y)^p)
    (fun x => -(p : ℝ)*(1-x)^(p-1)) htq (by fun_prop) hd
  exact ⟨u,hu,((eq_div_iff (sub_ne_zero.mpr htq.ne')).mp he).symm⟩

def productMeanValuePoint (p : ℕ) (t q : ℝ) : ℝ :=
  if h : t<q then Classical.choose (product_power_mean_value p h) else t

theorem productMeanValuePoint_spec (p : ℕ) {t q : ℝ} (htq : t<q) :
    productMeanValuePoint p t q∈Ioo t q ∧
    (1-q)^p-(1-t)^p=-(p : ℝ)*(1-productMeanValuePoint p t q)^(p-1)*(q-t) := by
  simpa only [productMeanValuePoint,dif_pos htq] using Classical.choose_spec (product_power_mean_value p htq)

/-- The printed intermediate points exist for the actual two-point tails,
and their exact leading prefactor tends to `exp(-1)`. -/
theorem skew_mean_value_prefactor_from_F1 {B : ℕ → ℝ} {p : ℕ → ℕ}
    (hB : ∀ n,2≤B n) (hp : Tendsto p atTop atTop)
    (hr : Tendsto (fun n => lowerSkewRate (B n) (p n) n) atTop (𝓝 0)) :
    ∃ u : ℕ → ℝ,
      (∀ᶠ n in atTop,
        u n∈Ioo (standardNormalUpperTail (normalMaxThreshold (p n)))
          (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))) ∧
        (1-lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n)))^(p n)-Real.exp (-1)=
          -(p n : ℝ)*standardNormalUpperTail (normalMaxThreshold (p n))*(1-u n)^(p n-1)*
            (lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))/
              standardNormalUpperTail (normalMaxThreshold (p n))-1)) ∧
      Tendsto (fun n => (p n : ℝ)*standardNormalUpperTail (normalMaxThreshold (p n))*
        (1-u n)^(p n-1)) atTop (𝓝 (Real.exp (-1))) := by
  let t := fun n => standardNormalUpperTail (normalMaxThreshold (p n))
  let q := fun n => lowerCoordinateUpperTail (B n) n (normalMaxThreshold (p n))
  let u := fun n => productMeanValuePoint (p n) (t n) (q n)
  have hs := skew_relative_tail_facts_from_F1 hB hp hr
  have hqt : ∀ᶠ n in atTop,t n<q n := by
    filter_upwards [hs.2.2.1] with n hn
    have htn : 0<t n := standardNormalUpperTail_pos _
    have hh : 1<q n/t n := by change 0<q n/t n-1 at hn; linarith
    simpa only [one_mul] using (lt_div_iff₀ htn).mp hh
  have hspec : ∀ᶠ n in atTop,u n∈Ioo (t n) (q n) ∧
      (1-q n)^(p n)-Real.exp (-1)=
        -(p n : ℝ)*t n*(1-u n)^(p n-1)*(q n/t n-1) := by
    filter_upwards [hqt,hp.eventually (eventually_ge_atTop 1)] with n hqn hpn
    have hm := productMeanValuePoint_spec (p n) hqn
    refine ⟨hm.1,?_⟩
    have hbase : (1-t n)^(p n)=Real.exp (-1) := by
      rw [show 1-t n=standardNormalCDF (normalMaxThreshold (p n)) by dsimp [t]; rw [standardNormalUpperTail_eq_one_sub]; ring]
      exact standardNormalCDF_normalMaxThreshold_pow hpn
    rw [hbase] at hm
    rw [hm.2]
    dsimp only [u]
    have htne : t n≠0 := (standardNormalUpperTail_pos _).ne'
    have hfactor : t n*(q n/t n-1)=q n-t n := by
      rw [mul_sub,mul_one,←mul_div_assoc,mul_div_cancel_left₀ _ htne]
    rw [←hfactor]
    ring
  refine ⟨u,hspec,?_⟩
  have hd := tendsto_normal_maximum_CDF_relativePerturbation hp hs.2.1
    (hs.2.2.1.mono (fun _ hn => hn.ne'))
  apply hd.congr'
  filter_upwards [hspec,hs.2.2.1] with n hn hsn
  change 0<q n/t n-1 at hsn
  change (Real.exp (-1)-(1-q n)^(p n))/(q n/t n-1)=_
  have hneg := hn.2
  have hg : Real.exp (-1)-(1-q n)^(p n)=
      ((p n : ℝ)*t n*(1-u n)^(p n-1))*(q n/t n-1) := by linarith
  rw [hg,mul_div_cancel_right₀ _ hsn.ne']

end
end RectangleCLT.Companion.SplitV4.Printed
