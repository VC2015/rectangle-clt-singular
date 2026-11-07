import RectangleCLTCompanion.SplitV4.LogisticScalarJets
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-! All-order logistic derivatives from the genuine Faà di Bruno formula. -/
open Filter Set
open scoped Topology BigOperators
namespace RectangleCLT.Companion.SplitV4
noncomputable section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {m : ℕ}

def linearExpTotal (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) (x : E) : ℝ :=
  ∑ j, Real.exp (L j x+b j)
def linearLogistic (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) (x : E) : ℝ :=
  reciprocalOnePlus (linearExpTotal L b x)
def linearFaceNorm (L : Fin m → E →L[ℝ] ℝ) (v : E) : ℝ := ‖fun j => L j v‖

theorem linearExpTotal_nonneg (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) (x : E) :
    0 ≤ linearExpTotal L b x := Finset.sum_nonneg (fun j _ => Real.exp_nonneg _)

theorem contDiff_linearExpTotal (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ) :
    ContDiff ℝ ⊤ (linearExpTotal L b) := by
  apply ContDiff.sum
  intro j _
  exact Real.contDiff_exp.comp ((L j).contDiff.add contDiff_const)

theorem iteratedFDeriv_linearExpTotal_apply (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ)
    (q : ℕ) (x : E) (z : Fin q → E) :
    iteratedFDeriv ℝ q (linearExpTotal L b) x z =
      ∑ j, Real.exp (L j x+b j)*∏ i, L j (z i) := by
  have hs := iteratedFDeriv_sum (𝕜 := ℝ) (i := q) (u := (Finset.univ : Finset (Fin m)))
    (f := fun j y => Real.exp (L j y+b j))
    (fun j _ => Real.contDiff_exp.comp ((L j).contDiff.add contDiff_const))
  have hh := congrArg (fun J => J x z) hs
  simpa only [linearExpTotal, Finset.sum_apply, ContinuousMultilinearMap.sum_apply,
    iteratedFDeriv_exp_linear_apply] using hh

theorem abs_linear_apply_le_faceNorm (L : Fin m → E →L[ℝ] ℝ) (v : E) (j : Fin m) :
    |L j v| ≤ linearFaceNorm L v := by
  simpa only [Real.norm_eq_abs] using norm_le_pi_norm (fun j => L j v) j

theorem abs_iteratedFDeriv_linearExpTotal_le (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ)
    (q : ℕ) (x : E) (z : Fin q → E) :
    |iteratedFDeriv ℝ q (linearExpTotal L b) x z| ≤
      linearExpTotal L b x*∏ i, linearFaceNorm L (z i) := by
  rw [iteratedFDeriv_linearExpTotal_apply]
  calc
    _ ≤ ∑ j, |Real.exp (L j x+b j)*∏ i, L j (z i)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ j, Real.exp (L j x+b j)*∏ i, linearFaceNorm L (z i) := by
      apply Finset.sum_le_sum
      intro j _
      rw [abs_mul,abs_of_pos (Real.exp_pos _),Finset.abs_prod]
      apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg _)
      exact Finset.prod_le_prod (fun i _ => abs_nonneg _) (fun i _ => abs_linear_apply_le_faceNorm L (z i) j)
    _ = _ := by rw [← Finset.sum_mul]; rfl

/-- Literal finite partition formula, with every tensor a genuine iterated
Fréchet derivative and no supplied derivative or Taylor identity. -/
theorem iteratedFDeriv_linearLogistic_partition (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ)
    (q : ℕ) (x : E) (z : Fin q → E) :
    iteratedFDeriv ℝ q (linearLogistic L b) x z =
      ∑ c : OrderedFinpartition q, reciprocalOnePlusJet c.length (linearExpTotal L b x) *
        ∏ j : Fin c.length,
          iteratedFDeriv ℝ (c.partSize j) (linearExpTotal L b) x (z ∘ c.emb j) := by
  have ht := linearExpTotal_nonneg L b x
  have hg : ContDiffAt ℝ ⊤ reciprocalOnePlus (linearExpTotal L b x) := by
    change ContDiffAt ℝ ⊤ (fun t : ℝ => 1/(1+t)) (linearExpTotal L b x)
    simpa only [one_div] using
      (show ContDiffAt ℝ ⊤ (fun t : ℝ => 1+t) (linearExpTotal L b x) from
        contDiffAt_const.add contDiffAt_id).inv (ne_of_gt (by linarith : 0 < 1+linearExpTotal L b x))
  have hh := congrArg (fun J => J z) (iteratedFDeriv_comp hg (contDiff_linearExpTotal L b).contDiffAt (i := q) le_top)
  change iteratedFDeriv ℝ q (linearLogistic L b) x z = _ at hh
  rw [hh]
  simp only [FormalMultilinearSeries.taylorComp, ContinuousMultilinearMap.sum_apply,
    FormalMultilinearSeries.compAlongOrderedFinpartition_apply,
    OrderedFinpartition.applyOrderedFinpartition_apply, ftaylorSeries]
  apply Finset.sum_congr rfl
  intro c _
  rw [iteratedFDeriv_reciprocalOnePlus_apply c.length (by linarith : -1 < linearExpTotal L b x)]
  ring

private theorem partition_product_identity {q : ℕ} (c : OrderedFinpartition q) (w : Fin q → ℝ) :
    (∏ j : Fin c.length, ∏ i : Fin (c.partSize j), w (c.emb j i)) = ∏ i, w i := by
  let e : (Σ j : Fin c.length, Fin (c.partSize j)) ≃ Fin q :=
    Equiv.ofBijective (fun p => c.emb p.1 p.2) ⟨c.emb_injective,c.exists_inverse⟩
  have hs := Fintype.prod_sigma (f := fun p : (Σ j : Fin c.length, Fin (c.partSize j)) => w (c.emb p.1 p.2))
  rw [← hs]
  exact Fintype.prod_equiv e _ _ (fun p => rfl)

private theorem reciprocal_partition_coefficient_le {T : ℝ} (hT : 0 ≤ T)
    (k : ℕ) (hk : 1 ≤ k) :
    ((k.factorial : ℝ)/(1+T)^(k+1))*T^k ≤
      (k.factorial : ℝ)*reciprocalOnePlus T*(1-reciprocalOnePlus T) := by
  have hb : 0 < 1+T := by linarith
  let θ := T/(1+T)
  have hθ0 : 0 ≤ θ := div_nonneg hT hb.le
  have hθ1 : θ ≤ 1 := (div_le_one hb).mpr (by linarith)
  have hθ : θ = 1-reciprocalOnePlus T := by
    dsimp [θ,reciprocalOnePlus]
    field_simp [ne_of_gt hb]
  have hpow : θ^k ≤ θ := by
    obtain ⟨j,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [pow_succ]
    exact (mul_le_mul_of_nonneg_right (pow_le_one₀ hθ0 hθ1) hθ0).trans_eq (one_mul _)
  calc
    _ = (k.factorial : ℝ)*reciprocalOnePlus T*θ^k := by
      dsimp [θ,reciprocalOnePlus]
      rw [div_pow,pow_succ]
      field_simp [ne_of_gt hb]
      <;> ring_nf <;> simp
    _ ≤ (k.factorial : ℝ)*reciprocalOnePlus T*θ :=
      mul_le_mul_of_nonneg_left hpow (mul_nonneg (Nat.cast_nonneg _) (by
        dsimp [reciprocalOnePlus]; positivity))
    _ = _ := by rw [hθ]

def logisticDerivativePartitionConstant (q : ℕ) : ℝ :=
  ∑ c : OrderedFinpartition q, (c.length.factorial : ℝ)

theorem logisticDerivativePartitionConstant_nonneg (q : ℕ) :
    0 ≤ logisticDerivativePartitionConstant q := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)

/-- Dimension-free all-order bound. The constant depends only on q, and
all directions are measured in the exact projected face seminorm. -/
theorem abs_iteratedFDeriv_linearLogistic_le (L : Fin m → E →L[ℝ] ℝ) (b : Fin m → ℝ)
    {q : ℕ} (hq : 1 ≤ q) (x : E) (z : Fin q → E) :
    |iteratedFDeriv ℝ q (linearLogistic L b) x z| ≤
      logisticDerivativePartitionConstant q*linearLogistic L b x*(1-linearLogistic L b x)*
        ∏ i, linearFaceNorm L (z i) := by
  let T := linearExpTotal L b x
  have hT : 0 ≤ T := linearExpTotal_nonneg L b x
  let P := ∏ i, linearFaceNorm L (z i)
  have hP : 0 ≤ P := Finset.prod_nonneg (fun i _ => norm_nonneg _)
  have hterm (c : OrderedFinpartition q) :
      |reciprocalOnePlusJet c.length T * ∏ j : Fin c.length,
        iteratedFDeriv ℝ (c.partSize j) (linearExpTotal L b) x (z ∘ c.emb j)| ≤
      (c.length.factorial : ℝ)*reciprocalOnePlus T*(1-reciprocalOnePlus T)*P := by
    have hprod : (∏ j : Fin c.length,
        |iteratedFDeriv ℝ (c.partSize j) (linearExpTotal L b) x (z ∘ c.emb j)|) ≤ T^c.length*P := by
      calc
        _ ≤ ∏ j : Fin c.length, (T*∏ i : Fin (c.partSize j), linearFaceNorm L (z (c.emb j i))) := by
          exact Finset.prod_le_prod (fun j _ => abs_nonneg _)
            (fun j _ => abs_iteratedFDeriv_linearExpTotal_le L b (c.partSize j) x (z ∘ c.emb j))
        _ = T^c.length*(∏ j : Fin c.length, ∏ i : Fin (c.partSize j), linearFaceNorm L (z (c.emb j i))) := by
          simp only [Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
        _ = T^c.length*P := by rw [partition_product_identity c (fun i => linearFaceNorm L (z i))]
    rw [abs_mul,Finset.abs_prod,abs_reciprocalOnePlusJet c.length (by linarith : -1 < T)]
    calc
      _ ≤ ((c.length.factorial : ℝ)/(1+T)^(c.length+1))*(T^c.length*P) :=
        mul_le_mul_of_nonneg_left hprod (by positivity)
      _ = (((c.length.factorial : ℝ)/(1+T)^(c.length+1))*T^c.length)*P := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (reciprocal_partition_coefficient_le hT c.length (c.length_pos (by omega))) hP
  rw [iteratedFDeriv_linearLogistic_partition]
  calc
    _ ≤ ∑ c : OrderedFinpartition q, |reciprocalOnePlusJet c.length (linearExpTotal L b x)*
        ∏ j : Fin c.length, iteratedFDeriv ℝ (c.partSize j) (linearExpTotal L b) x (z ∘ c.emb j)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c : OrderedFinpartition q,
        (c.length.factorial : ℝ)*reciprocalOnePlus T*(1-reciprocalOnePlus T)*P :=
      Finset.sum_le_sum (fun c _ => hterm c)
    _ = _ := by
      simp only [← Finset.sum_mul,logisticDerivativePartitionConstant,linearLogistic,T,P]

end
end RectangleCLT.Companion.SplitV4
