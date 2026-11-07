import RectangleCLTCompanion.SplitV4.SparseMaskLogAsymptotics

/-! Exact scalar parameters of the sparse polynomial lower construction.
The original envelope and coordinate fourth-moment constraints are kept
as genuine power identities, and the copy/coverage laws are separate. -/

open Filter
open scoped Topology
namespace RectangleCLT.Companion.SplitV4
noncomputable section

def sparseLowerK (n : ℕ) (ell q B : ℝ) : ℝ := B*((n : ℝ)/(1+2*ell))^(2/q-1/2)
def sparseLowerRate (n : ℕ) (ell q B : ℝ) : ℝ :=
  B*(1+2*ell)^(3/2-1/q)/((n : ℝ)^(1/2-1/q)*Real.log (Real.exp 1+sparseLowerK n ell q B)^(1-1/q))
def sparseLowerKhat (n : ℕ) (ell q B : ℝ) : ℝ := B*((n : ℝ)/ell)^(2/q-1/2)
def sparseLowerLog (n : ℕ) (ell q B : ℝ) : ℝ := maskedFourthLog (sparseLowerKhat n ell q B)
def sparseLowerCount (n : ℕ) (ell q B : ℝ) : ℝ := ell/(4*sparseLowerLog n ell q B)
def sparseLowerTheta (n : ℕ) (ell q B : ℝ) : ℝ := sparseLowerCount n ell q B/(n : ℝ)
def sparseLowerPi (n : ℕ) (ell q B : ℝ) : ℝ := (1/B^2)*(sparseLowerTheta n ell q B)^(4/q-1)
def sparseLowerAmplitude (n : ℕ) (ell q B : ℝ) : ℝ := (B/2)*(sparseLowerTheta n ell q B)^(-1/q)
def sparseLowerVariance (n : ℕ) (ell q B : ℝ) : ℝ :=
  sparseLowerTheta n ell q B*sparseLowerPi n ell q B*sparseLowerAmplitude n ell q B^2
def sparseLowerScale (n : ℕ) (ell q B : ℝ) : ℝ :=
  sparseLowerAmplitude n ell q B*sparseLowerCount n ell q B*Real.sqrt ell/Real.sqrt n
def sparseLowerCoordinateRate (n : ℕ) (ell B : ℝ) : ℝ :=
  Real.sqrt B*ell^(5/4 : ℝ)/(n : ℝ)^(1/4 : ℝ)
def sparseLowerCutoff (n : ℕ) (ell q B : ℝ) : ℕ :=
  Nat.ceil (2*((n : ℝ)*sparseLowerTheta n ell q B))

theorem sparseLowerCount_pos {n : ℕ} {ell q B : ℝ} (he : 0 < ell)
    (hK : 2 ≤ sparseLowerKhat n ell q B) : 0 < sparseLowerCount n ell q B :=
  maskedFourthCount_pos he hK

theorem sparseLowerTheta_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ} (he : 0 < ell)
    (hK : 2 ≤ sparseLowerKhat n ell q B) : 0 < sparseLowerTheta n ell q B :=
  div_pos (sparseLowerCount_pos he hK) (by exact_mod_cast hn)

theorem sparseLowerAmplitude_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ} (he : 0 < ell)
    (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) : 0 < sparseLowerAmplitude n ell q B :=
  mul_pos (div_pos hB (by norm_num)) (Real.rpow_pos_of_pos (sparseLowerTheta_pos hn he hK) _)

theorem sparseLowerScale_pos {n : ℕ} (hn : 0 < n) {ell q B : ℝ} (he : 0 < ell)
    (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) : 0 < sparseLowerScale n ell q B := by
  unfold sparseLowerScale
  exact div_pos (mul_pos (mul_pos (sparseLowerAmplitude_pos hn he hB hK) (sparseLowerCount_pos he hK))
    (Real.sqrt_pos.mpr he)) (Real.sqrt_pos.mpr (by exact_mod_cast hn))

theorem sparseLowerTheta_count {n : ℕ} (hn : 0 < n) (ell q B : ℝ) :
    (n : ℝ)*sparseLowerTheta n ell q B = sparseLowerCount n ell q B := by
  unfold sparseLowerTheta
  have hN : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

private theorem sparse_theta_power {θ : ℝ} (hθ : 0 < θ) (q : ℝ) (k : ℕ) :
    θ*θ^(4/q-1)*(θ^(-1/q))^k = θ^((4-(k : ℝ))/q) := by
  have hp : (θ^(-1/q))^k = θ^((-1/q)*(k : ℝ)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hθ.le]
  rw [hp]
  calc
    _ = (θ^(1 : ℝ)*θ^(4/q-1))*θ^((-1/q)*(k : ℝ)) := by rw [Real.rpow_one]
    _ = θ^((1+(4/q-1))+(-1/q)*(k : ℝ)) := by rw [Real.rpow_add hθ, Real.rpow_add hθ]
    _ = _ := by congr 1; ring

theorem sparseLower_envelope_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerAmplitude n ell q B*sparseLowerTheta n ell q B^(1/q) = B/2 := by
  unfold sparseLowerAmplitude
  rw [mul_assoc, ← Real.rpow_add (sparseLowerTheta_pos hn he hK)]
  have hh : -1/q+1/q = (0 : ℝ) := by ring
  rw [hh, Real.rpow_zero, mul_one]

theorem sparseLower_variance_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerVariance n ell q B = sparseLowerTheta n ell q B^(2/q)/4 := by
  have hp := sparse_theta_power (sparseLowerTheta_pos hn he hK) q 2
  unfold sparseLowerVariance sparseLowerPi sparseLowerAmplitude
  calc
    _ = (sparseLowerTheta n ell q B*sparseLowerTheta n ell q B^(4/q-1)*
        (sparseLowerTheta n ell q B^(-1/q))^2)/4 := by
      have hBNZ := hB.ne'
      field_simp
      <;> ring
    _ = _ := by rw [hp]; norm_num

theorem sparseLower_fourth_identity {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerTheta n ell q B*sparseLowerPi n ell q B*sparseLowerAmplitude n ell q B^4 = B^2/16 := by
  have hp := sparse_theta_power (sparseLowerTheta_pos hn he hK) q 4
  unfold sparseLowerPi sparseLowerAmplitude
  calc
    _ = (B^2/16)*(sparseLowerTheta n ell q B*sparseLowerTheta n ell q B^(4/q-1)*
        (sparseLowerTheta n ell q B^(-1/q))^4) := by
      have hBNZ := hB.ne'
      field_simp
      <;> ring
    _ = _ := by rw [hp]; norm_num

theorem sparseLowerPi_eq_mask {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hB : 0 < B) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerPi n ell q B = sparseMaskPi (sparseLowerKhat n ell q B) (1-4/q) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 < sparseLowerLog n ell q B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  have hKsq : sparseLowerKhat n ell q B^2 = B^2*((n : ℝ)/ell)^(4/q-1) := by
    unfold sparseLowerKhat
    rw [mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (div_pos hN he).le]
    congr 1
    ring
  have hw : (4*sparseLowerLog n ell q B)^(1-4/q) =
      ((4*sparseLowerLog n ell q B)^(4/q-1))⁻¹ := by
    convert Real.rpow_neg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΛ.le) (4/q-1) using 1 <;> congr 1 <;> ring
  unfold sparseLowerPi sparseMaskPi
  rw [hKsq]
  change (1/B^2)*(ell/(4*sparseLowerLog n ell q B)/(n : ℝ))^(4/q-1) =
    (1/(B^2*((n : ℝ)/ell)^(4/q-1)))*(4*sparseLowerLog n ell q B)^(1-4/q)
  rw [hw, Real.div_rpow (div_nonneg he.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΛ.le)) hN.le,
    Real.div_rpow he.le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΛ.le), Real.div_rpow hN.le he.le]
  have heNZ := (Real.rpow_pos_of_pos he (4/q-1)).ne'
  have hnNZ := (Real.rpow_pos_of_pos hN (4/q-1)).ne'
  have hwNZ := (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ) (4/q-1)).ne'
  have hBNZ := hB.ne'
  field_simp
  <;> ring
  all_goals simp

theorem sparseLowerScale_factor {n : ℕ} (hn : 0 < n) {ell q B : ℝ}
    (he : 0 < ell) (hK : 2 ≤ sparseLowerKhat n ell q B) :
    sparseLowerScale n ell q B =
      B*ell^(3/2-1/q)/(2*(4*sparseLowerLog n ell q B)^(1-1/q)*(n : ℝ)^(1/2-1/q)) := by
  have hN : (0 : ℝ) < n := by exact_mod_cast hn
  have hΛ : 0 < sparseLowerLog n ell q B := lt_of_lt_of_le (by norm_num) (maskedFourthLog_bounds hK).1
  have hθ := sparseLowerTheta_pos hn he hK
  have ha : sparseLowerTheta n ell q B^(-1/q) =
      (4*sparseLowerLog n ell q B)^(1/q)*(n : ℝ)^(1/q)/ell^(1/q) := by
    calc
      _ = ((sparseLowerTheta n ell q B)^(1/q))⁻¹ := by
        convert Real.rpow_neg hθ.le (1/q) using 1 <;> congr 1 <;> ring
      _ = ((sparseLowerTheta n ell q B)⁻¹)^(1/q) := (Real.inv_rpow hθ.le _).symm
      _ = (4*sparseLowerLog n ell q B*(n : ℝ)/ell)^(1/q) := by
        congr 1
        unfold sparseLowerTheta sparseLowerCount
        field_simp
      _ = _ := by rw [Real.div_rpow (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΛ.le) hN.le) he.le,
        Real.mul_rpow (mul_nonneg (by norm_num : (0 : ℝ) ≤ 4) hΛ.le) hN.le]
  have hePow : ell^(3/2-1/q)*ell^(1/q) = ell*Real.sqrt ell := by
    rw [← Real.rpow_add he]
    have hh : (3/2 : ℝ)-1/q+1/q = 1+1/2 := by ring
    rw [hh, Real.rpow_add he, Real.rpow_one, ← Real.sqrt_eq_rpow]
  have hnPow : (n : ℝ)^(1/2-1/q)*(n : ℝ)^(1/q) = Real.sqrt n := by
    rw [← Real.rpow_add hN]
    have hh : (1/2 : ℝ)-1/q+1/q = 1/2 := by ring
    rw [hh, ← Real.sqrt_eq_rpow]
  have hwPow : (4*sparseLowerLog n ell q B)^(1-1/q)*(4*sparseLowerLog n ell q B)^(1/q) = 4*sparseLowerLog n ell q B := by
    rw [← Real.rpow_add (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ)]
    have hh : (1 : ℝ)-1/q+1/q = 1 := by ring
    rw [hh, Real.rpow_one]
  unfold sparseLowerScale sparseLowerAmplitude sparseLowerCount
  rw [ha]
  have hW : 4*sparseLowerLog n ell q B ≠ 0 := (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ).ne'
  have heNZ := (Real.rpow_pos_of_pos he (1/q)).ne'
  have hnNZ := (Real.rpow_pos_of_pos hN (1/q)).ne'
  have hnNZ' := (Real.rpow_pos_of_pos hN (1/2-1/q)).ne'
  have hwNZ := (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ) (1/q)).ne'
  have hwNZ' := (Real.rpow_pos_of_pos (mul_pos (by norm_num : (0 : ℝ) < 4) hΛ) (1-1/q)).ne'
  have hCount : ell/(4*sparseLowerLog n ell q B) =
      ell/((4*sparseLowerLog n ell q B)^(1-1/q)*(4*sparseLowerLog n ell q B)^(1/q)) := by rw [hwPow]
  rw [← hnPow, hCount]
  have heSqrt : Real.sqrt ell = ell^(3/2-1/q)*ell^(1/q)/ell := by rw [hePow]; field_simp
  rw [heSqrt]
  field_simp
  <;> ring

end
end RectangleCLT.Companion.SplitV4
