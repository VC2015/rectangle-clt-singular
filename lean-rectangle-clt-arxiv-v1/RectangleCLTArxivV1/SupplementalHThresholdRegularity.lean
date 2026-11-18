import RectangleCLTCompanion.SplitV4.GaussianRadialScaling
import RectangleCLTCompanion.SplitV4.GaussianFiniteThresholdDerivatives

/-! Genuine hard Gaussian threshold regularity under pairwise
nonparallelism. No independence of the full normal family is imposed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators Topology
noncomputable section

def PairwiseNonparallelNormals {m r : ℕ} (u : Fin m → Vector r) : Prop :=
  ∀ j l, l≠j → gaussianNormalProjection (u j) (u l)≠0

theorem gaussianThresholdFirst_eq_section_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    gaussianThresholdFirst u b j=gaussianPDFReal 0 1 (b j)*
      gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) (b j) :=
  (hasDerivAt_gaussianThresholdCDF_update u b j hu
    (fun l hl => hp j l (Finset.mem_erase.mp hl).1) (b j)).deriv

theorem continuous_gaussianThresholdFirst_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) :
    Continuous (fun b => gaussianThresholdFirst u b j) := by
  have hc := continuous_gaussianFiniteThresholdCDF (Finset.univ.erase j)
    (fun l => gaussianNormalProjection (u j) (u l))
    (fun l hl => hp j l (Finset.mem_erase.mp hl).1)
  have hb : Continuous (fun b : Vector m => fun l => b l-b j*faceDot (u l) (u j)) := by fun_prop
  have hpdf : Continuous (fun b : Vector m => gaussianPDFReal 0 1 (b j)) :=
    (continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_standardRealGaussian_density t).continuousAt)).comp
      (continuous_apply j)
  have he : (fun b => gaussianThresholdFirst u b j)=fun b => gaussianPDFReal 0 1 (b j)*
      gaussianFiniteThresholdCDF (Finset.univ.erase j)
        (fun l => gaussianNormalProjection (u j) (u l))
        (fun l => b l-b j*faceDot (u l) (u j)) :=
    funext (fun b => gaussianThresholdFirst_eq_section_nonparallel u b j hu hp)
  rw [he]
  exact hpdf.mul (hc.comp hb)

theorem hasDerivAt_gaussianThresholdCDF_update_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j : Fin m)
    (hu : vectorNormSq (u j)=1) (hp : PairwiseNonparallelNormals u) (c : ℝ) :
    HasDerivAt (fun t => gaussianThresholdCDF u (Function.update b j t))
      (gaussianThresholdFirst u (Function.update b j c) j) c := by
  have hd := hasDerivAt_gaussianThresholdCDF_update u b j hu
    (fun l hl => hp j l (Finset.mem_erase.mp hl).1) c
  have he : gaussianThresholdFirst u (Function.update b j c) j=
      gaussianPDFReal 0 1 c*gaussianThresholdSectionProbability (Finset.univ.erase j) u b (u j) c := by
    unfold gaussianThresholdFirst
    simp only [Function.update_self,Function.update_idem]
    exact hd.deriv
  rwa [he]

theorem hasFDerivAt_gaussianThresholdCDF_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, vectorNormSq (u j)=1)
    (hp : PairwiseNonparallelNormals u) (b : Vector m) :
    HasFDerivAt (gaussianThresholdCDF u)
      (∑ j, gaussianThresholdFirst u b j • (ContinuousLinearMap.proj j : Vector m →L[ℝ] ℝ)) b :=
  hasFDerivAt_of_continuous_coordinate_derivatives (gaussianThresholdCDF u)
    (fun a j => gaussianThresholdFirst u a j)
    (fun a j c => hasDerivAt_gaussianThresholdCDF_update_nonparallel u a j (hu j) hp c)
    (fun j => continuous_gaussianThresholdFirst_nonparallel u j (hu j) hp) b

/-- The actual translated threshold CDF has the expected signed boundary
sum derivative, for any number of pairwise nonparallel normals. -/
theorem hasDerivAt_gaussianThresholdCDF_translate_nonparallel {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, vectorNormSq (u j)=1)
    (hp : PairwiseNonparallelNormals u) (b : Vector m) (v : Vector (n+1)) :
    HasDerivAt (fun t : ℝ => gaussianThresholdCDF u (fun j => b j-t*faceDot (u j) v))
      (-(∑ j, faceDot (u j) v*gaussianThresholdFirst u b j)) 0 := by
  have hc := hasFDerivAt_gaussianThresholdCDF_nonparallel u hu hp b
  have ht : HasDerivAt (fun t : ℝ => fun j : Fin m => b j-t*faceDot (u j) v)
      (fun j => -faceDot (u j) v) 0 := by
    apply hasDerivAt_pi.mpr
    intro j
    simpa using (hasDerivAt_const (0:ℝ) (b j)).sub
      ((hasDerivAt_id (0:ℝ)).mul_const (faceDot (u j) v))
  have hh := hc.comp_hasDerivAt_of_eq 0 ht (by simp)
  convert hh using 1
  · simp only [ContinuousLinearMap.sum_apply,ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.proj_apply,smul_eq_mul,←Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring

end
end RectangleCLTArxivV1
