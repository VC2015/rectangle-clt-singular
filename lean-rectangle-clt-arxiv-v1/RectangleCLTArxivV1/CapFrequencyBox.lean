import RectangleCLTArxivV1.CapFourierKernel
import RectangleCLTArxivV1.CapGaussianIntegral
import RectangleCLTArxivV1.CapMixedCharacteristic

namespace RectangleCLTArxivV1
open MeasureTheory RectangleCLT
open scoped BigOperators
noncomputable section

def capFrequencyRadius (h : ℝ) : ℝ := 1/(4*h)

def capFrequencyInterval (h : ℝ) : Set ℝ :=
  Set.Icc (-capFrequencyRadius h) (capFrequencyRadius h)

def capFrequencySquare (h : ℝ) : Set (ℝ × ℝ) :=
  capFrequencyInterval h ×ˢ capFrequencyInterval h

def capPairWeight (t : ℝ × ℝ) : Vector 2 := ![t.1,t.2]

def capPairPhase (x y : ℝ) (t : ℝ × ℝ) (v : Vector 2) : ℝ :=
  t.1*(v 0-x)+t.2*(v 1-y)

theorem measurableSet_capFrequencySquare (h : ℝ) : MeasurableSet (capFrequencySquare h) :=
  measurableSet_Icc.prod measurableSet_Icc

theorem capFrequencyRadius_pos {h : ℝ} (hh : 0 < h) : 0 < capFrequencyRadius h := by
  unfold capFrequencyRadius
  positivity

theorem volume_capFrequencyInterval {h : ℝ} (_hh : 0 < h) :
    volume (capFrequencyInterval h) = ENNReal.ofReal (2*capFrequencyRadius h) := by
  unfold capFrequencyInterval
  rw [Real.volume_Icc]
  congr 1
  ring

theorem capFrequencyInterval_volume_ne_zero {h : ℝ} (hh : 0 < h) :
    volume (capFrequencyInterval h) ≠ 0 := by
  rw [volume_capFrequencyInterval hh]
  have ha := capFrequencyRadius_pos hh
  positivity

theorem capFrequencyInterval_volume_ne_top {h : ℝ} (hh : 0 < h) :
    volume (capFrequencyInterval h) ≠ ⊤ := by
  rw [volume_capFrequencyInterval hh]
  exact ENNReal.ofReal_ne_top

theorem volume_capFrequencySquare {h : ℝ} (hh : 0 < h) :
    volume (capFrequencySquare h) = ENNReal.ofReal (4*(capFrequencyRadius h)^2) := by
  have ha := (capFrequencyRadius_pos hh).le
  change ((volume : Measure ℝ).prod volume) (capFrequencyInterval h ×ˢ capFrequencyInterval h) = _
  rw [Measure.prod_prod,volume_capFrequencyInterval hh,← ENNReal.ofReal_mul (by positivity)]
  congr 1
  ring

theorem capFrequencySquare_volume_ne_zero {h : ℝ} (hh : 0 < h) :
    volume (capFrequencySquare h) ≠ 0 := by
  rw [volume_capFrequencySquare hh]
  have ha := capFrequencyRadius_pos hh
  positivity

theorem capFrequencySquare_volume_ne_top {h : ℝ} (hh : 0 < h) :
    volume (capFrequencySquare h) ≠ ⊤ := by
  rw [volume_capFrequencySquare hh]
  exact ENNReal.ofReal_ne_top

theorem capFrequency_square_member_abs {h : ℝ} {s : ℝ × ℝ}
    (hs : s ∈ capFrequencySquare h) :
    |s.1| ≤ capFrequencyRadius h ∧ |s.2| ≤ capFrequencyRadius h :=
  ⟨abs_le.mpr hs.1,abs_le.mpr hs.2⟩

theorem capFrequency_square_sub_abs {h : ℝ} {s t : ℝ × ℝ}
    (hs : s ∈ capFrequencySquare h) (ht : t ∈ capFrequencySquare h) :
    |s.1-t.1| ≤ 2*capFrequencyRadius h ∧ |s.2-t.2| ≤ 2*capFrequencyRadius h := by
  have hs' := capFrequency_square_member_abs hs
  have ht' := capFrequency_square_member_abs ht
  constructor
  · exact (abs_sub _ _).trans (by linarith [hs'.1,ht'.1])
  · exact (abs_sub _ _).trans (by linarith [hs'.2,ht'.2])

theorem abs_capPairPhase_le_one {h : ℝ} (hh : 0 < h) (x y : ℝ)
    {s : ℝ × ℝ} (hs : s ∈ capFrequencySquare h) (v : Vector 2)
    (hx : |v 0-x| ≤ h) (hy : |v 1-y| ≤ h) : |capPairPhase x y s v| ≤ 1 := by
  have hf := capFrequency_square_member_abs hs
  have ha := (capFrequencyRadius_pos hh).le
  have h₁ := mul_le_mul hf.1 hx (abs_nonneg _) ha
  have h₂ := mul_le_mul hf.2 hy (abs_nonneg _) ha
  have he : capFrequencyRadius h*h = 1/4 := by unfold capFrequencyRadius; field_simp; ring
  unfold capPairPhase
  apply (abs_add _ _).trans
  rw [abs_mul,abs_mul]
  nlinarith [h₁,h₂]

theorem abs_capPairWeight_projection_le_half {h δ : ℝ} (hh : 0 < h)
    (_hδ : 0 ≤ δ) (hband : 2*δ ≤ h)
    {s t : ℝ × ℝ} (hs : s ∈ capFrequencySquare h) (ht : t ∈ capFrequencySquare h)
    (v : Vector 2) (hv0 : |v 0| ≤ δ) (hv1 : |v 1| ≤ δ) :
    |dotProduct (capPairWeight (s-t)) v| ≤ 1/2 := by
  have hf := capFrequency_square_sub_abs hs ht
  have ha := (capFrequencyRadius_pos hh).le
  have h₁ := mul_le_mul hf.1 hv0 (abs_nonneg _) (by positivity : 0 ≤ 2*capFrequencyRadius h)
  have h₂ := mul_le_mul hf.2 hv1 (abs_nonneg _) (by positivity : 0 ≤ 2*capFrequencyRadius h)
  have he : 4*capFrequencyRadius h*δ = δ/h := by unfold capFrequencyRadius; field_simp; ring
  have hd : δ/h ≤ 1/2 := (div_le_iff₀ hh).mpr (by linarith)
  simp only [dotProduct,Fin.sum_univ_two,capPairWeight,Matrix.cons_val_zero,
    Matrix.cons_val_one,Prod.fst_sub,Prod.snd_sub]
  apply (abs_add _ _).trans
  rw [abs_mul,abs_mul]
  nlinarith [h₁,h₂]

theorem cap_pair_matrixQuadratic {M : Matrix (Fin 2) (Fin 2) ℝ} {v ρ : ℝ}
    (hM : M = !![v,v*ρ;v*ρ,v]) (t : ℝ × ℝ) :
    matrixQuadratic M (capPairWeight t) = v*(t.1^2+2*ρ*t.1*t.2+t.2^2) := by
  rw [hM]
  simp only [matrixQuadratic,Fin.sum_univ_two,capPairWeight,Matrix.of_apply,
    Matrix.cons_val_zero,Matrix.cons_val_one]
  ring

end
end RectangleCLTArxivV1
