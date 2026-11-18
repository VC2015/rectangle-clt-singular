import RectangleCLTArxivV1.SupplementalHGenericPairGreen

/-! The actual angle-weighted signed Gaussian ridge quantity and its
codimension-three Green remainder. No abstract surface identity is assumed. -/
namespace RectangleCLTArxivV1
open MeasureTheory ProbabilityTheory Filter RectangleCLT RectangleCLT.Companion.SplitV4
open scoped BigOperators
noncomputable section

def hardGaussianRidgeNormalWeight {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ :=
  Real.arccos (faceDot (u j) (u l))*
    gaussianPDFReal 0 1 (thresholdPairFirstLevel u b j l)*
    gaussianPDFReal 0 1 (thresholdPairSecondLevel u b j l)

def hardGaussianRidgeNonparallel {m r : ℕ} (u : Fin m → Vector r) (j l : Fin m) : Prop :=
  projectionEuclideanVector (u j)+projectionEuclideanVector (u l)≠0 ∧
    projectionEuclideanVector (u j)-projectionEuclideanVector (u l)≠0

def hardGaussianSignedRidgeTerm {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ := by
  classical
  exact if hardGaussianRidgeNonparallel u j l then
    hardGaussianRidgeNormalWeight u b j l*
      hardGaussianPairSignedSection ((Finset.univ.erase j).erase l) u b
        (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)
  else 0

def hardGaussianRidgeLeadingTerm {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ := by
  classical
  exact if hardGaussianRidgeNonparallel u j l then
    ((thresholdPairFirstLevel u b j l)^2+(thresholdPairSecondLevel u b j l)^2-2)*
      (hardGaussianRidgeNormalWeight u b j l*
        hardGaussianPairSectionProbability ((Finset.univ.erase j).erase l) u b
          (thresholdPairBisector u j l) (thresholdPairDifference u j l)
          (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))
  else 0

def hardGaussianRidgeThirdBoundaryTerm {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) (j l : Fin m) : ℝ := by
  classical
  exact if hardGaussianRidgeNonparallel u j l then
    ∑ k∈(Finset.univ.erase j).erase l,
      hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l) k*
      (hardGaussianRidgeNormalWeight u b j l*
        gaussianFiniteThresholdFirst ((Finset.univ.erase j).erase l)
          (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
          (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
            (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l)) k)
  else 0

/-- Half the ordered pair sum is the genuine angle-weighted ridge
quantity: its scalar prefactor is the two-dimensional Gaussian normal
density, with no extra Gram denominator. -/
def hardGaussianWeightedRidgeIntegral {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (1/2:ℝ)*∑ q : Fin m × Fin m, hardGaussianSignedRidgeTerm u b q.1 q.2

def hardGaussianRidgeLeadingIntegral {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (1/2:ℝ)*∑ q : Fin m × Fin m, hardGaussianRidgeLeadingTerm u b q.1 q.2

def hardGaussianRidgeThirdBoundaryIntegral {m r : ℕ} (u : Fin m → Vector r) (b : Vector m) : ℝ :=
  (1/2:ℝ)*∑ q : Fin m × Fin m, hardGaussianRidgeThirdBoundaryTerm u b q.1 q.2

/-- Actual signed ridge Green decomposition at locally regular residual
thresholds. All remaining hard inequalities are retained. -/
theorem hardGaussianSignedRidgeTerm_Green_of_slack {m n : ℕ}
    (u : Fin m → Vector (n+1)) (b : Vector m) (j l : Fin m)
    (hu : vectorNormSq (u j)=1) (hv : vectorNormSq (u l)=1)
    (hreg : LocalFiniteThresholdRegularity ((Finset.univ.erase j).erase l)
      (hardPairResidualNormals u (thresholdPairBisector u j l) (thresholdPairDifference u j l))
      (hardPairResidualLevels u b (thresholdPairBisector u j l) (thresholdPairDifference u j l)
        (thresholdPairFirstLevel u b j l) (thresholdPairSecondLevel u b j l))) :
    hardGaussianSignedRidgeTerm u b j l=
      hardGaussianRidgeLeadingTerm u b j l-hardGaussianRidgeThirdBoundaryTerm u b j l := by
  classical
  unfold hardGaussianSignedRidgeTerm hardGaussianRidgeLeadingTerm hardGaussianRidgeThirdBoundaryTerm
  split_ifs with hp
  · exact hardGaussianPairSection_Green_weighted_of_slack _ u b _ _
      (thresholdPairBisector_unit u j l hp.1) (thresholdPairDifference_unit u j l hp.2)
      (thresholdPair_frame_orthogonal u j l hu hv) _ _ _ hreg
  · ring

/-- The genuine ridge quantity has the signed codimension-three Green
remainder at almost every threshold, for arbitrary dependent unit normals. -/
theorem ae_hardGaussianWeightedRidgeIntegral_Green {m n : ℕ}
    (u : Fin m → Vector (n+1)) (hu : ∀ j, vectorNormSq (u j)=1) :
    ∀ᵐ b : Vector m ∂volume, hardGaussianWeightedRidgeIntegral u b=
      hardGaussianRidgeLeadingIntegral u b-hardGaussianRidgeThirdBoundaryIntegral u b := by
  filter_upwards [ae_pairResidualThresholdRegularity u] with b hb
  unfold hardGaussianWeightedRidgeIntegral hardGaussianRidgeLeadingIntegral hardGaussianRidgeThirdBoundaryIntegral
  simp_rw [hardGaussianSignedRidgeTerm_Green_of_slack u b _ _ (hu _) (hu _) (hb _ _),Finset.sum_sub_distrib]
  ring

end
end RectangleCLTArxivV1
