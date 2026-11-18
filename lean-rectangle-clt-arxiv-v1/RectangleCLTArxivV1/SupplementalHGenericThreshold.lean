import RectangleCLTArxivV1.SupplementalHLocalThreshold

/-! Ordinary affine exceptional threshold configurations are null for
Euclidean threshold volume, independently of the rank of the normals. -/
namespace RectangleCLTArxivV1
open MeasureTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

/-- A nonzero Gaussian linear form has no atom; positivity of the actual
Gaussian density transfers this fact to ordinary Euclidean volume. -/
theorem ae_volume_faceDot_ne {m : ℕ} (w : Vector m) (hw : w≠0) (c : ℝ) :
    ∀ᵐ b : Vector m ∂volume, faceDot w b≠c := by
  have hn := standardGaussian_affine_hyperplane_zero w hw c
  have ha : ∀ᵐ b ∂standardGaussian m, faceDot w b≠c := by
    simpa only [ae_iff,not_not] using hn
  rw [standardGaussian_eq_withDensity,ae_withDensity_iff
    (standardGaussianDensity_measurable m).ennreal_ofReal] at ha
  exact ha.mono (fun b h => h (ENNReal.ofReal_pos.mpr (standardGaussianDensity_pos _ _)).ne')

/-- A threshold with coefficient one cannot be canceled identically by
any fixed combination of two different threshold coordinates. -/
theorem ae_threshold_ne_two_coordinate_combination {m : ℕ}
    (j k l : Fin m) (hlj : l≠j) (hlk : l≠k) (a d : ℝ) :
    ∀ᵐ b : Vector m ∂volume, b l-a*b j-d*b k≠0 := by
  let w : Vector m := (Pi.single l (1:ℝ) : Vector m)-a • (Pi.single j (1:ℝ) : Vector m)-d • (Pi.single k (1:ℝ) : Vector m)
  have hw : w≠0 := by
    intro h
    have hh := congrFun h l
    simp [w,Pi.single_apply,hlj,hlk] at hh
  have he (b : Vector m) : faceDot w b=b l-a*b j-d*b k := by
    simp only [w,threshold_faceDot_sub_left,threshold_faceDot_smul_left]
    have hs (i : Fin m) : faceDot (Pi.single i 1) b=b i := by
      simp [faceDot,Pi.single_apply,ite_mul]
    rw [hs,hs,hs]
  simpa only [he] using ae_volume_faceDot_ne w hw 0

/-- The one-coordinate version covers parallel or duplicate normal
families without a rank assumption. -/
theorem ae_threshold_ne_coordinate_multiple {m : ℕ}
    (j l : Fin m) (hlj : l≠j) (a : ℝ) :
    ∀ᵐ b : Vector m ∂volume, b l-a*b j≠0 := by
  simpa only [zero_mul,sub_zero] using
    ae_threshold_ne_two_coordinate_combination j j l hlj hlj a 0

/-- The local regularity used for actual unit-normal hard threshold
calculus holds at almost every threshold, even for dependent normals. -/
theorem ae_localThresholdRegularity {m r : ℕ} (u : Fin m → Vector r) :
    ∀ᵐ b : Vector m ∂volume, LocalThresholdRegularity u b := by
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro l
  by_cases hlj : l=j
  · exact ae_of_all _ (fun _ h => False.elim (h hlj))
  · exact (ae_threshold_ne_coordinate_multiple j l hlj (faceDot (u l) (u j))).mono
      (fun b h _ => Or.inr (by simpa only [mul_comm] using h))

/-- All fixed two- and three-face affine coincidences can be discarded
simultaneously. The exceptional set is independent of a sampled base. -/
theorem ae_threshold_all_two_coordinate_combinations {m : ℕ}
    (a d : Fin m → Fin m → Fin m → ℝ) :
    ∀ᵐ b : Vector m ∂volume, ∀ j k l, l≠j → l≠k →
      b l-a j k l*b j-d j k l*b k≠0 := by
  apply Filter.eventually_all.mpr
  intro j
  apply Filter.eventually_all.mpr
  intro k
  apply Filter.eventually_all.mpr
  intro l
  by_cases hlj : l=j
  · exact ae_of_all _ (fun _ h _ => False.elim (h hlj))
  · by_cases hlk : l=k
    · exact ae_of_all _ (fun _ _ h => False.elim (h hlk))
    · exact (ae_threshold_ne_two_coordinate_combination j k l hlj hlk (a j k l) (d j k l)).mono
        (fun _ h _ _ => h)

end
end RectangleCLTArxivV1
