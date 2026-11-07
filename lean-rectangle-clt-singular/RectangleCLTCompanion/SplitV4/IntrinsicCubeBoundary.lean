import RectangleCLTCompanion.SplitV4.IntrinsicCubeMaximum
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.MeasureTheory.Integral.Bochner.Set

/-! The intrinsic Rademacher boundary estimate of Lemma C.1. Active affine
branches are supporting subgradients at cube vertices. Their edge
inequalities hold for any maximizing selection, including ties. -/

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

/-- An unnormalized ramp avoids division by its width in the edge proof. -/
def cubeRamp (c H x : ℝ) : ℝ := max 0 (min H (x - c))

theorem cubeRamp_nonneg (c H x : ℝ) : 0 ≤ cubeRamp c H x := le_max_left _ _

theorem cubeRamp_le_width (c H x : ℝ) (hH : 0 ≤ H) : cubeRamp c H x ≤ H :=
  max_le hH (min_le_left _ _)

theorem cubeRamp_monotone (c H : ℝ) : Monotone (cubeRamp c H) := by
  intro x y hxy
  exact max_le_max le_rfl (min_le_min le_rfl (sub_le_sub_right hxy c))

theorem cubeRamp_eq_linear (c H x : ℝ) (hx₀ : c ≤ x) (hx₁ : x ≤ c + H) :
    cubeRamp c H x = x - c := by
  unfold cubeRamp
  rw [min_eq_right (by linarith), max_eq_right (by linarith)]

def cubeEdgeFlux (c H fm fp dm dp : ℝ) : ℝ :=
  (cubeRamp c H fp * dp - cubeRamp c H fm * dm) / 2

/-- Monotonicity of supporting subgradients after composition with the
integrated ramp. This algebraic proof does not need differentiability or a
unique affine maximizer at either endpoint. -/
theorem cubeEdgeFlux_nonneg (c H fm fp dm dp : ℝ)
    (hm : dm ≤ (fp - fm) / 2) (hp : (fp - fm) / 2 ≤ dp) :
    0 ≤ cubeEdgeFlux c H fm fp dm dp := by
  have horder : dm ≤ dp := hm.trans hp
  have hprod : cubeRamp c H fm * dm ≤ cubeRamp c H fp * dp := by
    by_cases hdm : 0 ≤ dm
    · have hmf : fm ≤ fp := by linarith
      exact (mul_le_mul_of_nonneg_right (cubeRamp_monotone c H hmf) hdm).trans
        (mul_le_mul_of_nonneg_left horder (cubeRamp_nonneg _ _ _))
    · have hdm' : dm ≤ 0 := le_of_lt (lt_of_not_ge hdm)
      by_cases hdp : 0 ≤ dp
      · exact (mul_nonpos_of_nonneg_of_nonpos (cubeRamp_nonneg _ _ _) hdm').trans
          (mul_nonneg (cubeRamp_nonneg _ _ _) hdp)
      · have hpm : fp ≤ fm := by have := lt_of_not_ge hdp; linarith
        exact (mul_le_mul_of_nonpos_right (cubeRamp_monotone c H hpm) hdm').trans
          (mul_le_mul_of_nonneg_left horder (cubeRamp_nonneg _ _ _))
  exact div_nonneg (sub_nonneg.mpr hprod) (by norm_num)

/-- On the expanded boundary window, one edge flux controls the squared
slope at both endpoints. The constants are the manuscript's `h+8b` and
`t-6b`, and the inequalities hold for supporting subgradients at ties. -/
theorem cubeEdgeFlux_controls_squares (t h b fm fp dm dp : ℝ) (hb : 0 ≤ b)
    (hdm : -b ≤ dm) (hdp : dp ≤ b)
    (hm : dm ≤ (fp - fm) / 2) (hp : (fp - fm) / 2 ≤ dp)
    (hfm : t - 2 * b ≤ fm ∧ fm ≤ t + h + 2 * b)
    (hfp : t - 2 * b ≤ fp ∧ fp ≤ t + h + 2 * b) :
    dm ^ 2 ≤ cubeEdgeFlux (t - 6 * b) (h + 8 * b) fm fp dm dp ∧
      dp ^ 2 ≤ cubeEdgeFlux (t - 6 * b) (h + 8 * b) fm fp dm dp := by
  let q := (fp - fm) / 2
  have hV : 0 ≤ dp - dm := sub_nonneg.mpr (hm.trans hp)
  have hrm : cubeRamp (t - 6 * b) (h + 8 * b) fm = fm - (t - 6 * b) :=
    cubeRamp_eq_linear _ _ _ (by linarith [hfm.1]) (by linarith [hfm.2])
  have hrp : cubeRamp (t - 6 * b) (h + 8 * b) fp = fp - (t - 6 * b) :=
    cubeRamp_eq_linear _ _ _ (by linarith [hfp.1]) (by linarith [hfp.2])
  have hminus : dm ^ 2 - b * (dp - dm) ≤ q * dm := by
    have h₁ := mul_le_mul_of_nonneg_right (show -dm ≤ b by linarith)
      (show 0 ≤ q - dm by dsimp [q]; linarith)
    have h₂ := mul_le_mul_of_nonneg_left (show q - dm ≤ dp - dm by dsimp [q]; linarith) hb
    nlinarith
  have hplus : dp ^ 2 - b * (dp - dm) ≤ q * dp := by
    have h₁ := mul_le_mul_of_nonneg_right hdp (show 0 ≤ dp - q by dsimp [q]; linarith)
    have h₂ := mul_le_mul_of_nonneg_left (show dp - q ≤ dp - dm by dsimp [q]; linarith) hb
    nlinarith
  have hcostm : b * (dp - dm) ≤ (fm - (t - 6 * b)) / 2 * (dp - dm) :=
    mul_le_mul_of_nonneg_right (by linarith [hfm.1]) hV
  have hcostp : b * (dp - dm) ≤ (fp - (t - 6 * b)) / 2 * (dp - dm) :=
    mul_le_mul_of_nonneg_right (by linarith [hfp.1]) hV
  have hfluxm : cubeEdgeFlux (t - 6 * b) (h + 8 * b) fm fp dm dp =
      q * dp + (fm - (t - 6 * b)) / 2 * (dp - dm) := by
    rw [cubeEdgeFlux, hrm, hrp]
    dsimp only [q]
    ring
  have hfluxp : cubeEdgeFlux (t - 6 * b) (h + 8 * b) fm fp dm dp =
      q * dm + (fp - (t - 6 * b)) / 2 * (dp - dm) := by
    rw [cubeEdgeFlux, hrm, hrp]
    dsimp only [q]
    ring
  constructor
  · rw [hfluxp]
    linarith
  · rw [hfluxm]
    linarith

/-- Exact discrete integration by parts on the uniform Boolean cube. -/
theorem cube_avg_signed_coordinate {n : ℕ} (k : Kane.Cube n → ℝ) (i : Fin n) :
    Kane.avg (fun x => cubeSign x i * k x) =
      Kane.avg (fun x => (k (Function.update x i true) - k (Function.update x i false)) / 2) := by
  have hpoint (x : Kane.Cube n) : cubeSign x i * k x + cubeSign (Kane.flip x i) i * k (Kane.flip x i) =
      k (Function.update x i true) - k (Function.update x i false) := by
    cases hx : x i
    · have hs : Function.update x i false = x := by simpa only [hx] using Function.update_eq_self i x
      simp [cubeSign, Kane.flip, hx, hs]
      ring
    · have hs : Function.update x i true = x := by simpa only [hx] using Function.update_eq_self i x
      simp [cubeSign, Kane.flip, hx, hs]
      ring
  have havg := Kane.avg_congr hpoint
  have hflip := Kane.avg_flip (fun x => cubeSign x i * k x) i
  rw [Kane.avg_add, hflip] at havg
  have hhalf := Kane.avg_const_mul (1 / 2 : ℝ)
    (fun x => k (Function.update x i true) - k (Function.update x i false))
  have he : Kane.avg (fun x => (k (Function.update x i true) - k (Function.update x i false)) / 2) =
      (1 / 2 : ℝ) * Kane.avg (fun x => k (Function.update x i true) - k (Function.update x i false)) := by
    simpa only [div_eq_mul_inv, mul_comm, one_mul] using hhalf
  rw [he]
  linarith

section Affine

variable {m n : ℕ} [NeZero m]

def affineCubeMaximum (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (x : Kane.Cube n) : ℝ :=
  (Finset.univ : Finset (Fin m)).sup' Finset.univ_nonempty (fun α => cubeLinear (b α) x - a α)

def activeCubeBranch (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (x : Kane.Cube n) : Fin m :=
  Classical.choose (Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
    Finset.univ_nonempty (fun α => cubeLinear (b α) x - a α))

theorem activeCubeBranch_attains (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (x : Kane.Cube n) :
    affineCubeMaximum b a x = cubeLinear (b (activeCubeBranch b a x)) x - a (activeCubeBranch b a x) :=
  (Classical.choose_spec (Finset.exists_mem_eq_sup' (s := (Finset.univ : Finset (Fin m)))
    Finset.univ_nonempty (fun α => cubeLinear (b α) x - a α))).2

theorem affineCubeMaximum_supports (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (x : Kane.Cube n) (α : Fin m) : cubeLinear (b α) x - a α ≤ affineCubeMaximum b a x :=
  Finset.le_sup' (s := (Finset.univ : Finset (Fin m)))
    (f := fun α => cubeLinear (b α) x - a α) (Finset.mem_univ α)

theorem cubeLinear_edge_difference (b : Fin n → ℝ) (x : Kane.Cube n) (i : Fin n) :
    cubeLinear b (Function.update x i true) - cubeLinear b (Function.update x i false) = 2 * b i := by
  classical
  unfold cubeLinear
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp [cubeSign]
    ring
  · intro j _ hji
    simp only [cubeSign, Function.update_of_ne hji, sub_self]
  · intro hi
    exact False.elim (hi (Finset.mem_univ i))

def activeCubeSlope (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (x : Kane.Cube n) (i : Fin n) : ℝ :=
  b (activeCubeBranch b a x) i

def affineCubeEdgeFlux (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (c H : ℝ) (x : Kane.Cube n) (i : Fin n) : ℝ :=
  cubeEdgeFlux c H
    (affineCubeMaximum b a (Function.update x i false))
    (affineCubeMaximum b a (Function.update x i true))
    (activeCubeSlope b a (Function.update x i false) i)
    (activeCubeSlope b a (Function.update x i true) i)

def cubeBoundaryIndicator (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (t h : ℝ) (x : Kane.Cube n) : ℝ :=
  if t ≤ affineCubeMaximum b a x ∧ affineCubeMaximum b a x ≤ t + h then 1 else 0

/-- Supporting affine branches give the edge subgradient inequalities even
when several branches maximize at one or both endpoints. -/
theorem affineCube_edge_support (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (x : Kane.Cube n) (i : Fin n) :
    activeCubeSlope b a (Function.update x i false) i ≤
      (affineCubeMaximum b a (Function.update x i true) -
        affineCubeMaximum b a (Function.update x i false)) / 2 ∧
    (affineCubeMaximum b a (Function.update x i true) -
        affineCubeMaximum b a (Function.update x i false)) / 2 ≤
      activeCubeSlope b a (Function.update x i true) i := by
  let xm := Function.update x i false
  let xp := Function.update x i true
  have hAm := activeCubeBranch_attains b a xm
  have hAp := activeCubeBranch_attains b a xp
  have hSm := affineCubeMaximum_supports b a xp (activeCubeBranch b a xm)
  have hSp := affineCubeMaximum_supports b a xm (activeCubeBranch b a xp)
  have hDm := cubeLinear_edge_difference (b (activeCubeBranch b a xm)) x i
  have hDp := cubeLinear_edge_difference (b (activeCubeBranch b a xp)) x i
  change cubeLinear (b (activeCubeBranch b a xm)) xp -
    cubeLinear (b (activeCubeBranch b a xm)) xm = _ at hDm
  change cubeLinear (b (activeCubeBranch b a xp)) xp -
    cubeLinear (b (activeCubeBranch b a xp)) xm = _ at hDp
  change b (activeCubeBranch b a xm) i ≤ (affineCubeMaximum b a xp - affineCubeMaximum b a xm) / 2 ∧
    (affineCubeMaximum b a xp - affineCubeMaximum b a xm) / 2 ≤ b (activeCubeBranch b a xp) i
  constructor <;> linarith

theorem affineCubeEdgeFlux_nonneg (b : Fin m → Fin n → ℝ) (a : Fin m → ℝ)
    (c H : ℝ) (x : Kane.Cube n) (i : Fin n) : 0 ≤ affineCubeEdgeFlux b a c H x i :=
  cubeEdgeFlux_nonneg _ _ _ _ _ _ (affineCube_edge_support b a x i).1
    (affineCube_edge_support b a x i).2

theorem affineCube_edge_oscillation (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (b : ℝ)
    (hcoeff : ∀ α i, |B α i| ≤ b) (x : Kane.Cube n) (i : Fin n) :
    |affineCubeMaximum B a (Function.update x i true) -
      affineCubeMaximum B a (Function.update x i false)| ≤ 2 * b := by
  have hs := affineCube_edge_support B a x i
  have hm := (abs_le.mp (hcoeff (activeCubeBranch B a (Function.update x i false)) i)).1
  have hp := (abs_le.mp (hcoeff (activeCubeBranch B a (Function.update x i true)) i)).2
  dsimp only [activeCubeSlope] at hs
  apply abs_le.mpr
  constructor <;> linarith [hs.1, hs.2]

theorem boundary_active_slope_square_le_flux
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b : ℝ) (hb : 0 ≤ b)
    (hcoeff : ∀ α i, |B α i| ≤ b) (x : Kane.Cube n) (i : Fin n)
    (hevent : t ≤ affineCubeMaximum B a x ∧ affineCubeMaximum B a x ≤ t + h) :
    (activeCubeSlope B a x i) ^ 2 ≤ affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i := by
  let xm := Function.update x i false
  let xp := Function.update x i true
  have hs := affineCube_edge_support B a x i
  have hosc := abs_le.mp (affineCube_edge_oscillation B a b hcoeff x i)
  have hdm : -b ≤ activeCubeSlope B a xm i :=
    (abs_le.mp (hcoeff (activeCubeBranch B a xm) i)).1
  have hdp : activeCubeSlope B a xp i ≤ b :=
    (abs_le.mp (hcoeff (activeCubeBranch B a xp) i)).2
  cases hx : x i
  · have hxself : xm = x := by simpa only [xm, hx] using Function.update_eq_self i x
    have hem : t ≤ affineCubeMaximum B a xm ∧ affineCubeMaximum B a xm ≤ t + h := by
      rw [hxself]
      exact hevent
    have hfm : t - 2 * b ≤ affineCubeMaximum B a xm ∧ affineCubeMaximum B a xm ≤ t + h + 2 * b :=
      ⟨by linarith [hem.1], by linarith [hem.2]⟩
    have hfp : t - 2 * b ≤ affineCubeMaximum B a xp ∧ affineCubeMaximum B a xp ≤ t + h + 2 * b :=
      ⟨by linarith [hem.1, hosc.1], by linarith [hem.2, hosc.2]⟩
    have hh := (cubeEdgeFlux_controls_squares t h b _ _ _ _ hb hdm hdp hs.1 hs.2 hfm hfp).1
    change (activeCubeSlope B a xm i) ^ 2 ≤ affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i at hh
    rwa [hxself] at hh
  · have hxself : xp = x := by simpa only [xp, hx] using Function.update_eq_self i x
    have hep : t ≤ affineCubeMaximum B a xp ∧ affineCubeMaximum B a xp ≤ t + h := by
      rw [hxself]
      exact hevent
    have hfp : t - 2 * b ≤ affineCubeMaximum B a xp ∧ affineCubeMaximum B a xp ≤ t + h + 2 * b :=
      ⟨by linarith [hep.1], by linarith [hep.2]⟩
    have hfm : t - 2 * b ≤ affineCubeMaximum B a xm ∧ affineCubeMaximum B a xm ≤ t + h + 2 * b :=
      ⟨by linarith [hep.1, hosc.2], by linarith [hep.2, hosc.1]⟩
    have hh := (cubeEdgeFlux_controls_squares t h b _ _ _ _ hb hdm hdp hs.1 hs.2 hfm hfp).2
    change (activeCubeSlope B a xp i) ^ 2 ≤ affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i at hh
    rwa [hxself] at hh

theorem cube_boundary_indicator_energy_le_flux
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b : ℝ) (hb : 0 ≤ b)
    (hcoeff : ∀ α i, |B α i| ≤ b) (x : Kane.Cube n) (i : Fin n) :
    cubeBoundaryIndicator B a t h x * (activeCubeSlope B a x i) ^ 2 ≤
      affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i := by
  by_cases he : t ≤ affineCubeMaximum B a x ∧ affineCubeMaximum B a x ≤ t + h
  · simp only [cubeBoundaryIndicator, if_pos he, one_mul]
    exact boundary_active_slope_square_le_flux B a t h b hb hcoeff x i he
  · simp only [cubeBoundaryIndicator, if_neg he, zero_mul]
    exact affineCubeEdgeFlux_nonneg B a _ _ x i

theorem avg_affineCubeEdgeFlux_sum
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (c H : ℝ) :
    Kane.avg (fun x => ∑ i, affineCubeEdgeFlux B a c H x i) =
      Kane.avg (fun x => cubeRamp c H (affineCubeMaximum B a x) *
        cubeLinear (B (activeCubeBranch B a x)) x) := by
  rw [Kane.avg_sum]
  have he (i : Fin n) : Kane.avg (fun x => affineCubeEdgeFlux B a c H x i) =
      Kane.avg (fun x => cubeSign x i *
        (cubeRamp c H (affineCubeMaximum B a x) * activeCubeSlope B a x i)) := by
    exact (cube_avg_signed_coordinate
      (fun x => cubeRamp c H (affineCubeMaximum B a x) * activeCubeSlope B a x i) i).symm
  simp_rw [he]
  rw [← Kane.avg_sum]
  apply Kane.avg_congr
  intro x
  simp only [cubeLinear, Finset.mul_sum, activeCubeSlope]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- The intrinsic boundary estimate, before converting the finite average
to the actual uniform probability law. No uniqueness of active faces is
required. The positive number `v` is the lower bound on squared row norms. -/
theorem intrinsic_cube_boundary_avg
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b v : ℝ)
    (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    Kane.avg (cubeBoundaryIndicator B a t h) ≤
      (h + 8 * b) / v * intrinsicCubeMean B := by
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have := hrow (0 : Fin m)
    simp only [Finset.univ_eq_empty, Finset.sum_empty] at this
    linarith
  let i₀ : Fin n := ⟨0, Nat.pos_of_ne_zero hn⟩
  have hb : 0 ≤ b := (abs_nonneg (B (0 : Fin m) i₀)).trans (hcoeff _ _)
  have hH : 0 ≤ h + 8 * b := by linarith
  have hlower (x : Kane.Cube n) :
      v * cubeBoundaryIndicator B a t h x ≤
        ∑ i, affineCubeEdgeFlux B a (t - 6 * b) (h + 8 * b) x i := by
    have hI : 0 ≤ cubeBoundaryIndicator B a t h x := by
      unfold cubeBoundaryIndicator
      split_ifs <;> norm_num
    calc
      v * cubeBoundaryIndicator B a t h x ≤
          (∑ i, (activeCubeSlope B a x i) ^ 2) * cubeBoundaryIndicator B a t h x :=
        mul_le_mul_of_nonneg_right (hrow (activeCubeBranch B a x)) hI
      _ = ∑ i, cubeBoundaryIndicator B a t h x * (activeCubeSlope B a x i) ^ 2 := by
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ ≤ _ := Finset.sum_le_sum (fun i _ =>
        cube_boundary_indicator_energy_le_flux B a t h b hb hcoeff x i)
  have hupper (x : Kane.Cube n) :
      cubeRamp (t - 6 * b) (h + 8 * b) (affineCubeMaximum B a x) *
        cubeLinear (B (activeCubeBranch B a x)) x ≤
      (h + 8 * b) * positiveLinearMaximum B x := by
    exact (mul_le_mul_of_nonneg_left (cubeLinear_le_positiveMaximum B x _) (cubeRamp_nonneg _ _ _)).trans
      (mul_le_mul_of_nonneg_right (cubeRamp_le_width _ _ _ hH) (positiveLinearMaximum_nonneg B x))
  have hbound : v * Kane.avg (cubeBoundaryIndicator B a t h) ≤
      (h + 8 * b) * intrinsicCubeMean B := by
    calc
      _ = Kane.avg (fun x => v * cubeBoundaryIndicator B a t h x) :=
        (Kane.avg_const_mul _ _).symm
      _ ≤ _ := Kane.avg_mono hlower
      _ = _ := avg_affineCubeEdgeFlux_sum B a _ _
      _ ≤ _ := Kane.avg_mono hupper
      _ = _ := Kane.avg_const_mul _ _
  have hd : Kane.avg (cubeBoundaryIndicator B a t h) ≤
      ((h + 8 * b) * intrinsicCubeMean B) / v :=
    (le_div_iff₀ hv).mpr (by nlinarith [hbound])
  convert hd using 1
  ring

end Affine

/-- The actual uniform probability measure on all sign vectors. -/
def cubeUniformLaw (n : ℕ) : Measure (Kane.Cube n) :=
  (PMF.uniformOfFintype (Kane.Cube n)).toMeasure

instance cubeUniformLaw_isProbabilityMeasure (n : ℕ) :
    IsProbabilityMeasure (cubeUniformLaw n) := by
  unfold cubeUniformLaw
  infer_instance

/-- The finite average used in the edge calculation is the actual
expectation under the uniform sign law. -/
theorem integral_cubeUniformLaw_eq_avg {n : ℕ} (f : Kane.Cube n → ℝ) :
    ∫ x, f x ∂cubeUniformLaw n = Kane.avg f := by
  rw [cubeUniformLaw, PMF.integral_eq_sum]
  simp only [PMF.uniformOfFintype_apply, ENNReal.toReal_inv, ENNReal.toReal_natCast,
    smul_eq_mul, Kane.avg, Finset.mul_sum]

theorem cubeUniformLaw_boundary_eq_avg {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h : ℝ) :
    (cubeUniformLaw n).real {x | t ≤ affineCubeMaximum B a x ∧
      affineCubeMaximum B a x ≤ t + h} = Kane.avg (cubeBoundaryIndicator B a t h) := by
  rw [← integral_cubeUniformLaw_eq_avg]
  have hm : MeasurableSet {x : Kane.Cube n | t ≤ affineCubeMaximum B a x ∧
      affineCubeMaximum B a x ≤ t + h} := Set.toFinite _ |>.measurableSet
  simpa only [Set.indicator, Set.mem_setOf_eq, cubeBoundaryIndicator, Pi.one_apply] using
    (integral_indicator_one (μ := cubeUniformLaw n) hm).symm

/-- **Lemma C.1, intrinsic estimate.** This is an actual probability of a
closed boundary window under uniform independent signs, with the intrinsic
expected positive maximum retained on the right. `v` denotes `σ²`. -/
theorem intrinsic_cube_boundary {m n : ℕ} [NeZero m]
    (B : Fin m → Fin n → ℝ) (a : Fin m → ℝ) (t h b v : ℝ)
    (hh : 0 ≤ h) (hv : 0 < v)
    (hcoeff : ∀ α i, |B α i| ≤ b) (hrow : ∀ α, v ≤ ∑ i, (B α i) ^ 2) :
    (cubeUniformLaw n).real {x | t ≤ affineCubeMaximum B a x ∧
      affineCubeMaximum B a x ≤ t + h} ≤
      (h + 8 * b) / v * ∫ x, positiveLinearMaximum B x ∂cubeUniformLaw n := by
  rw [cubeUniformLaw_boundary_eq_avg, integral_cubeUniformLaw_eq_avg]
  exact intrinsic_cube_boundary_avg B a t h b v hh hv hcoeff hrow

/-- **Lemma C.1, logarithmic specialization of the intrinsic mean.** -/
theorem intrinsic_cube_mean_le_sqrt_log {m n : ℕ}
    (B : Fin m → Fin n → ℝ) (hrow : ∀ α, ∑ i, (B α i) ^ 2 ≤ 1) :
    ∫ x, positiveLinearMaximum B x ∂cubeUniformLaw n ≤
      Real.sqrt (2 * Real.log ((m : ℝ) + 1)) := by
  rw [integral_cubeUniformLaw_eq_avg]
  exact intrinsicCubeMean_le_sqrt_log B hrow

end

end RectangleCLT.Companion.SplitV4
