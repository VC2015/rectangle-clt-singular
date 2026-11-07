import RectangleCLTCompanion.SplitV4.SeededPathBase

open MeasureTheory
open scoped BigOperators

namespace RectangleCLT.Companion.SplitV4

noncomputable section

theorem map_sum_standardGaussian_factor
    {Ω : Type*} [MeasurableSpace Ω] {p : ℕ}
    (ν : Measure Ω) [SFinite ν] (V : Ω → Vector p) (hV : Measurable V)
    (M : Matrix (Fin p) (Fin p) ℝ) :
    (ν.prod (standardGaussian p)).map (fun z => V z.1 + M.mulVec z.2) =
      Measure.conv (ν.map V) (gaussianLaw M) := by
  have hm : (ν.map V).prod (gaussianLaw M) =
      (ν.prod (standardGaussian p)).map (Prod.map V M.mulVec) :=
    Measure.map_prod_map ν (standardGaussian p) hV (measurable_mulVec M)
  rw [Measure.conv, hm, Measure.map_map (measurable_fst.add measurable_snd)
    (hV.prodMap (measurable_mulVec M))]
  rfl

theorem map_add_left_conv {p : ℕ} (μ ν : Measure (Vector p)) [SFinite μ] [SFinite ν] (x : Vector p) :
    (Measure.conv μ ν).map (fun y => x + y) =
      Measure.conv (μ.map (fun y => x + y)) ν := by
  have hshift : Measurable (fun y : Vector p => x + y) := measurable_const.add measurable_id
  have hm : (μ.map (fun y => x + y)).prod ν =
      (μ.prod ν).map (Prod.map (fun y => x + y) id) := by
    simpa only [Measure.map_id] using
      Measure.map_prod_map μ ν hshift measurable_id
  simp only [Measure.conv]
  rw [hm, Measure.map_map (measurable_fst.add measurable_snd)
    (hshift.prodMap measurable_id),
    Measure.map_map hshift
      (measurable_fst.add measurable_snd)]
  congr 1
  funext z
  change x + (z.1 + z.2) = (x + z.1) + z.2
  exact (add_assoc _ _ _).symm

theorem seededSplitBaseDistribution_eq_conv
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) (ξ : Fin n → Ω → Vector p)
    (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p) (ε t : ℝ)
    [SFinite (bernoulliArrayLaw μ ξ t)] :
    seededSplitBaseDistribution μ ξ A x ε t =
      Measure.conv ((bernoulliArrayLaw μ ξ t).map (fun b => x + arraySum b))
        (gaussianLaw (seededSplitGaussianScale ε t • A)) := by
  change ((bernoulliArrayLaw μ ξ t).prod (standardGaussian p)).map
    (fun z => (x + arraySum z.1) + (seededSplitGaussianScale ε t • A).mulVec z.2) = _
  exact map_sum_standardGaussian_factor _ _ (measurable_const.add (measurable_arraySum p n)) _

theorem seededGaussianHalves_conv {p : ℕ} (A : Matrix (Fin p) (Fin p) ℝ)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) :
    Measure.conv (gaussianLaw (seededSplitGaussianScale ε t • A))
      (gaussianLaw (seededSplitGaussianScale ε t • A)) =
        gaussianLaw (Real.sqrt (t + ε) • A) := by
  have hhalf : 0 ≤ (t + ε) / 2 := by positivity
  have hh := gaussian_seed_conv A hhalf hhalf
  simpa only [seededSplitGaussianScale, add_halves] using hh

/-- The genuine seeded law equals the actual full retained-array base
plus a second independent standard Gaussian half. -/
theorem seededGaussianSplit_law
    {Ω : Type*} [MeasurableSpace Ω] {p n : ℕ}
    (μ : Measure Ω) [IsProbabilityMeasure μ] (ξ : Fin n → Ω → Vector p)
    (hξ : ∀ i, Measurable (ξ i)) (A : Matrix (Fin p) (Fin p) ℝ) (x : Vector p)
    {ε t : ℝ} (hε : 0 ≤ ε) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    ((splitBaseLaw μ ξ t).prod (standardGaussian p)).map
      (fun z => seededSplitBaseValue A x ε t z.1 +
        (seededSplitGaussianScale ε t • A).mulVec z.2) =
      (seededInterpolationLaw μ ξ A ε t).map (fun y => x + y) := by
  let B := bernoulliArrayLaw μ ξ t
  letI : IsProbabilityMeasure B := bernoulliArrayLaw_isProbability μ ξ hξ t ht ht1
  letI := splitBaseLaw_isProbability μ ξ hξ ht ht1
  rw [map_sum_standardGaussian_factor _ _ (measurable_seededSplitBaseValue A x ε t)]
  change Measure.conv (seededSplitBaseDistribution μ ξ A x ε t)
    (gaussianLaw (seededSplitGaussianScale ε t • A)) = _
  rw [seededSplitBaseDistribution_eq_conv, Measure.conv_assoc, seededGaussianHalves_conv A hε ht,
    seededInterpolationLaw_eq_shifted_heat μ ξ hξ A hε ht ht1]
  change Measure.conv (B.map (fun b => x + arraySum b)) (gaussianLaw (Real.sqrt (t + ε) • A)) =
    (Measure.conv (B.map arraySum) (gaussianLaw (Real.sqrt (t + ε) • A))).map (fun y => x + y)
  rw [map_add_left_conv]
  have he : (B.map arraySum).map (fun y => x + y) = B.map (fun b => x + arraySum b) :=
    Measure.map_map (measurable_const.add measurable_id) (measurable_arraySum p n)
  rw [he]

end

end RectangleCLT.Companion.SplitV4
