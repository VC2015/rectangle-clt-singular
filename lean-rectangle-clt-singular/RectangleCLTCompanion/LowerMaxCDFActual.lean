import RectangleCLTCompanion.LowerMaxCDFProduct
import RectangleCLTCompanion.LowerMaxCDFLimits

/-! Maximum-CDF transfer on the genuine lower arrays and the identity
Gaussian target. These wrappers discharge the product-distribution step;
the analytic scalar-tail limits remain explicit intermediate inputs. -/

open MeasureTheory ProbabilityTheory Set Filter
open scoped Topology
namespace RectangleCLT.Companion
noncomputable section

/-- A critical scalar-tail limit transfers to an actual rectangle error,
including a maximum over fewer coordinates than the ambient dimension. -/
theorem tendsto_lowerMaximum_rectangleError_critical
    {B : ℕ → ℝ} {N d P : ℕ → ℕ} {a : ℝ}
    (hd : Tendsto d atTop atTop) (hactive : ∀ᶠ n in atTop,d n≤P n)
    (htail : Tendsto (fun n =>
      lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))) atTop (𝓝 a)) :
    Tendsto (fun n => rectangleError (lowerArrayLaw (B n) (N n) (P n))
      (sumVector (lowerNormalizedRows (n := N n) (p := P n))) 1
      (partialMaximumRectangle (P n) (d n) (normalMaxThreshold (d n))))
      atTop (𝓝 |Real.exp (-1)-Real.exp (-a)|) := by
  have hh := tendsto_normal_maximum_CDF_critical_gap hd htail
  apply hh.congr'
  filter_upwards [hactive,hd.eventually (eventually_ge_atTop 1)] with n hn hdn
  rw [lowerArrayLaw_partialMaximum_rectangleError _ _ hn,
    standardNormalCDF_normalMaxThreshold_pow hdn,abs_sub_comm]

/-- The exact first-order coefficient for the actual lower maximum
rectangle. Moment and sample scales belong to the separate scalar proof. -/
theorem tendsto_lowerMaximum_rectangleError_firstOrder
    {B r : ℕ → ℝ} {N d P : ℕ → ℕ} {k : ℝ}
    (hd : Tendsto d atTop atTop) (hactive : ∀ᶠ n in atTop,d n≤P n)
    (hr : Tendsto r atTop (𝓝 0)) (hrpos : ∀ᶠ n in atTop,0<r n)
    (htail : Tendsto (fun n =>
      (lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))-1)/r n) atTop (𝓝 k)) :
    Tendsto (fun n => rectangleError (lowerArrayLaw (B n) (N n) (P n))
      (sumVector (lowerNormalizedRows (n := N n) (p := P n))) 1
      (partialMaximumRectangle (P n) (d n) (normalMaxThreshold (d n)))/r n)
      atTop (𝓝 (Real.exp (-1)*|k|)) := by
  have hh := tendsto_normal_maximum_CDF_firstOrder_abs hd hr hrpos htail
  apply hh.congr'
  filter_upwards [hactive,hd.eventually (eventually_ge_atTop 1)] with n hn hdn
  rw [lowerArrayLaw_partialMaximum_rectangleError _ _ hn,
    standardNormalCDF_normalMaxThreshold_pow hdn,abs_sub_comm]


/-- Lower limits transfer without imposing convergence of the skewness
coefficient along the sample sequence. -/
theorem lowerMaximum_rectangleError_liminf
    {B r : ℕ → ℝ} {N d P : ℕ → ℕ} {K : ℝ}
    (hd : Tendsto d atTop atTop) (hactive : ∀ᶠ n in atTop,d n≤P n)
    (hpert : Tendsto (fun n =>
      lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))-1) atTop (𝓝 0))
    (hpos : ∀ᶠ n in atTop,0<
      lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))-1)
    (hrpos : ∀ᶠ n in atTop,0<r n)
    (hupper : atTop.IsBoundedUnder (·≤·) (fun n =>
      (lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))-1)/r n))
    (hlower : K≤liminf (fun n =>
      (lowerCoordinateUpperTail (B n) (N n) (normalMaxThreshold (d n))/
        standardNormalUpperTail (normalMaxThreshold (d n))-1)/r n) atTop) :
    Real.exp (-1)*K≤liminf (fun n => rectangleError (lowerArrayLaw (B n) (N n) (P n))
      (sumVector (lowerNormalizedRows (n := N n) (p := P n))) 1
      (partialMaximumRectangle (P n) (d n) (normalMaxThreshold (d n)))/r n) atTop := by
  have hh := normal_maximum_CDF_liminf_from_relativeTail hd hpert hpos hrpos hupper hlower
  apply hh.trans_eq
  apply liminf_congr
  filter_upwards [hactive,hd.eventually (eventually_ge_atTop 1)] with n hn hdn
  rw [lowerArrayLaw_partialMaximum_rectangleError _ _ hn,
    standardNormalCDF_normalMaxThreshold_pow hdn,abs_sub_comm]

end
end RectangleCLT.Companion
