from pathlib import Path
import json,re
R=Path(__file__).resolve().parents[2];O=Path(__file__).resolve().parent
S=R/'../lean-rectangle-clt-singular'
B4='''RectangleCLTArxivV1.SmoothingMatrixIntrinsic
RectangleCLTCompanion.TiltContraction
RectangleCLTCompanion.SelectorMatrixReduction
RectangleCLTCompanion.SelectorMeanBound
RectangleCLTCompanion.SelectorProjectionMoment
RectangleCLTCompanion.SplitV4.LogisticMatrixEstimate
RectangleCLTCompanion.SplitV4.LogisticGammaTrace
RectangleCLTCompanion.SplitV4.LogisticMatrixBound
RectangleCLTCompanion.SplitV4.LogisticNormalRegularization
RectangleCLTCompanion.SplitV4.LogisticMatrixLimits
RectangleCLTCompanion.SplitV4.LogisticPaddingLimits
RectangleCLTCompanion.SplitV4.LogisticMatrixRegularizedBound'''.split()
B5='''RectangleCLTArxivV1.AveragedThresholdIntrinsic
RectangleCLTCompanion.SplitV4.GaussianThresholdIdentity
RectangleCLTCompanion.SplitV4.GaussianThresholdDiagonal
RectangleCLTCompanion.SplitV4.GaussianRadialScaling
RectangleCLTCompanion.SplitV4.GaussianThresholdPairCoarea
RectangleCLTCompanion.SplitV4.GaussianThresholdTubes
RectangleCLTCompanion.SplitV4.GaussianThresholdPairTubes
RectangleCLTCompanion.SplitV4.GaussianThresholdTubeGeometry
RectangleCLTCompanion.SplitV4.AveragedThreshold
RectangleCLTCompanion.SplitV4.AveragedThresholdBound'''.split()
E3='''RectangleCLTArxivV1.PairedGaussianEndpointSmoothing
RectangleCLTArxivV1.PublishedPairedEndpoints
RectangleCLTCompanion.SplitV4.ClockCutoff'''.split()
LOWER='''RectangleCLTArxivV1.LowerLeadingCalibration
RectangleCLTArxivV1.LowerLeadingDensity
RectangleCLTArxivV1.GaussianIdentityWidth
RectangleCLTArxivV1.LowerRectangularFamilyMaximum
RectangleCLTArxivV1.LowerRectangularFamilyShifts
RectangleCLTArxivV1.LowerRectangularFamilyMaster
RectangleCLTArxivV1.LowerRectangularFamilyOrthant
RectangleCLTArxivV1.LowerWidthCalibration
RectangleCLTArxivV1.LowerRectangularDetection
RectangleCLTCompanion.SplitV4.Printed.RademacherMaximumGlobal
RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumQuantile
RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumMomentsConvergence
RectangleCLTCompanion.SplitV4.Printed.GaussianMaximumSmoothness
RectangleCLTCompanion.SplitV4.SymmetricFamilyAllActive
RectangleCLTCompanion.SplitV4.SymmetricFamilyActivation
RectangleCLTCompanion.SplitV4.SymmetricFamilyShifts
RectangleCLTCompanion.SplitV4.CoordinateDuplication'''.split()
def file(m):return (R if m.startswith('RectangleCLTArxivV1.') else S)/ (m.replace('.','/')+'.lean')
missing=[m for m in B4+B5+E3+LOWER if not file(m).exists()]
assert not missing,missing
spec={};names=[]
for group,mods in [('B4',B4),('B5',B5),('E3',E3),('Lower',LOWER)]:
 spec[group]=[]
 for m in mods:
  s=file(m).read_text();ns=re.search(r'^namespace ([\w.]+)',s,re.M).group(1)
  for n in re.findall(r'^(?:theorem|lemma|def|noncomputable def)\s+([\w.]+)',s,re.M):
   if m.endswith('PublishedPairedEndpoints') and n!='lemma_E3_intrinsic_smoothing':continue
   q=ns+'.'+n;names.append(q);spec[group].append(q)
(O/'public-targets.json').write_text(json.dumps(list(dict.fromkeys(names)),indent=2)+'\n')
(O/'module-groups.json').write_text(json.dumps({'groups':{'B4':B4,'B5':B5,'E3':E3,'Lower':LOWER},'target_groups':spec},indent=2)+'\n')
print({g:len(n) for g,n in spec.items()})
