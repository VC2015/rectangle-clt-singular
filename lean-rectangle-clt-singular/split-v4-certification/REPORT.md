# Split-V4 Lean certification — 7 November 2026

## Summary

The certificate covers **all 31 proved named statements** in the exact
unrestricted-covariance split-V4 manuscript identified below, together with
its required analytic dependencies. The final frozen-source run passed all
167 commands; independent CI passed the eight-command pristine baseline
and the same 167 checkpoint commands. The local and CI dependency records
agree exactly. No in-scope result-level proof obligation remains open.

**Conjecture 1 is excluded and is never an assumption.** Optional companion
extensions, including the separate covariance-mismatch extension, are outside
this certificate's 31-statement scope. Earlier companion certifications retain
their own scope and records.

This is certification of the **mapped mathematical results and their formal
arguments**, not a claim that every printed proof paragraph has been translated
literally. Section 5 identifies the equivalent implementations and alternative
arguments. The TeX-to-Lean correspondence is a reviewed mapping; Lean checks
the formal statements and proof terms, rather than parsing the manuscript.

A separate extension is mapping and verifying the substantive printed routes
against the same frozen source. It will retain the result certificate and
issue its own coverage and evidence. **Complete printed-route coverage is not
claimed by this report or by the existing result certificate.**

The manuscript, its magenta markings, the original inventory and analytic
audit, and the three October verification records are preserved. The report
adds documentation; it does not alter the paper or any Lean proof.

## 1. Frozen sources and publication boundary

| Item | Exact identifier |
| --- | --- |
| Manuscript and handoff commit | `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd` |
| Manuscript path | `research-rectangle-clt-singular/Unrestricted_CLT-split-V4.tex` |
| Manuscript SHA-256 | `f2c1252531e21642c5e1e6ca99e2b32a5ae63895d9e51ff075a8f23505eea2b1` |
| Manuscript Git blob | `3dd7ea1a9c92e1d8d7ddfcbb6438b20a65ebc78e` |
| Complete Lean proof commit | `69f89747f4b845491b75cb23134c056bfbcd40f7` |
| Certificate and evidence commit | `69363df233f20632d73e953d09981ab495abfb50` |
| Merge PR | [VC2015/HDCLTs #14](https://github.com/VC2015/HDCLTs/pull/14) |
| Published merged snapshot | Annotated tag `split-v4-lean-certified-2026-11-07` |

The [certificate commit](https://github.com/VC2015/HDCLTs/commit/69363df233f20632d73e953d09981ab495abfb50)
records the results of executing the separate
[proof commit](https://github.com/VC2015/HDCLTs/commit/69f89747f4b845491b75cb23134c056bfbcd40f7).
A report-bearing commit follows those immutable records. The annotated
[tagged snapshot](https://github.com/VC2015/HDCLTs/tree/split-v4-lean-certified-2026-11-07)
is placed on the PR #14 **merge commit only after the final PR-head checks
pass**. Its annotation records the actual merge commit, checked PR head,
final CI run, and report hashes. The merge preserves the existing history;
it is neither a squash nor a rebase merge.

The tag, rather than a moving `main`, identifies this publication. Resolve its
exact merge commit and inspect the annotation with:

```sh
git rev-parse split-v4-lean-certified-2026-11-07^{commit}
git cat-file -p refs/tags/split-v4-lean-certified-2026-11-07
```

Yuta's pending [PR #15](https://github.com/VC2015/HDCLTs/pull/15) and Denis's
forthcoming editorial edits are **not incorporated into this snapshot**.
At report preparation, PR #15 was open and unmerged, with head
`f694f6a24ecaf3f98a32e2befa2c5ef676be12d9`; its two commits were absent from
PR #14 and `main`. The merge boundary is checked against the unchanged
handoff base before publication. No claim is made here about the correctness
or correspondence of those later manuscript bytes.

## 2. All 31 statement correspondences

Printed numbers and stable labels refer to the frozen manuscript, not to older
numbering retained in source comments. In the table, an unqualified declaration
uses the namespace **`RectangleCLT.Companion.SplitV4`**. The two historical primary
endpoints are qualified in full. Links identify the actual declarations at the
immutable proof commit.

Each primary name was checked against its actual source, its elaborated type
in the fresh dependency log, and a successful statement audit. The primary
type equals the type recorded in the statement map. Essential companion
endpoints are explained after the table.

| Manuscript statement and stable label | Primary Lean declaration |
| --- | --- |
| Theorem 1 — Unrestricted covariance<br>`thm:unrestricted` | [`relativeFourthMomentCLT`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeMain.lean#L87) |
| Corollary 1 — Normalized observations<br>`cor:observations` | [`normalizedObservationsCLTExists`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ObservationNormalization.lean#L98) |
| Corollary 2 — Sub-exponential transfer<br>`cor:subexponential` | [`subexponentialRectangleDistanceCLTExists`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SubexponentialTransfer.lean#L41) |
| Theorem 2 — Polynomial moment envelopes<br>`thm:polynomial` | [`polynomialMomentCLTExists`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/PolynomialMain.lean#L110) |
| Corollary 3 — Polyhedral transfer<br>`cor:polyhedral-transfer` | [`relativePolyhedralCLT`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeFaceTransfer.lean#L57) |
| Lemma 1 — Rectangle anti-concentration<br>`lem:concentration` | [`lemma_concentration`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Concentration.lean#L136) |
| Lemma 2 — Smoothing error<br>`lem:endpoint` | [`smoothingLemma2`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Smoothing.lean#L190) |
| Proposition 1 — Initialization and seeded derivative estimates<br>`an:prop:derivative` | [`proposition_relative_derivatives`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/RelativeDerivativeProposition.lean#L163) |
| Proposition 2 — Polynomial envelope transfer<br>`poly:transfer` | [`polynomialEnvelopeTransfer`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ConditionalPolynomialOptimization.lean#L175) |
| Proposition 3 — Bennett refinement<br>`poly:bennett` | [`bennettPolynomialCLT_observations`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettPolynomial.lean#L862) |
| Theorem 3 — Bounded observations with independent coordinates<br>`opt:skew-lower` | [`RectangleCLT.Companion.skewedTwoPointLowerScale`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/LowerScaleMain.lean#L45) |
| Theorem 4 — Centrally symmetric lower bound<br>`opt:symmetric-lower` | [`boundedSymmetricLower`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricBoundedLower.lean#L193) |
| Theorem 5 — Fourth-moment lower bound<br>`opt:q4-lower` | [`fourthMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L34) |
| Theorem 6 — Growing fourth-moment envelope<br>`opt:q4-growing` | [`maskedFourthLower`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/MaskedFourthLower.lean#L120) |
| Theorem 7 — Lower bound for fixed B and q>4<br>`lower:dense` | [`denseMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L69) |
| Theorem 8 — Sparse polynomial-moment lower bound<br>`lower:sparse` | [`sparseMoment_uniform_constants`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/UniformLowerConstants.lean#L103) |
| Lemma A.1 — Averaging the derivative envelope<br>`appx-lem:envelope` | [`lemma_derivative_envelope`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/DerivativeEnvelopeAllOrders.lean#L131) |
| Lemma B.1 — Interpolation identity with a Gaussian seed<br>`appx-an:lem:identity` | [`hasDerivAt_integral_genericVariableSeededInterpolationLaw_tensor`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/GenericC4CubicTensor.lean#L89) |
| Lemma B.2 — Paired derivatives at translated bases<br>`appx-an:lem:restoration` | [`lemma_paired_restoration`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/Restoration.lean#L129) |
| Lemma B.3 — Gaussian mean relative to a single face<br>`appx-an:lem:mean` | [`RectangleCLT.Companion.gaussian_mean_relative_to_one_face`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/GaussianEntropy.lean#L203) |
| Lemma B.4 — Matrix estimate for logistic weights<br>`appx-an:lem:matrix` | [`exists_logistic_matrix_paper_constant`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LogisticMatrixPaper.lean#L64) |
| Lemma B.5 — Averaged Gaussian threshold derivative<br>`appx-an:lem:threshold` | [`averagedGaussianThresholdDerivative_rectangle_bound`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/AveragedThresholdBound.lean#L425) |
| Lemma C.1 — Rademacher boundary estimate<br>`appx-lem:cube-boundary` | [`intrinsic_cube_boundary`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/IntrinsicCubeBoundary.lean#L373) |
| Lemma E.1 — An expected maximum under an envelope moment<br>`lem:maximum` | [`expected_maximum_under_envelope_moment`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/EnvelopeMaximum.lean#L152) |
| Lemma F.1 — Uniform scalar moderate-tail estimate<br>`opt:moderate-tail` | [`uniformScalarModerateTail`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ModerateTailGeneral.lean#L72) |
| Lemma F.2 — Comparison of independently shifted variables<br>`lower:shift-comparison` | [`independent_shift_comparison`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ShiftComparison.lean#L259) |
| Lemma F.3 — Properties of the common symmetric construction<br>`lower:family-properties` | [`symmetricFamilyProperties`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/SymmetricFamilyCertification.lean#L65) |
| Lemma G.1 — Gaussian comparison with large-increment remainders<br>`ben:comparison` | [`gaussianComparisonWithLargeIncrementRemainders`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/LargeIncrementComparison.lean#L531) |
| Lemma G.2 — Smoothing from the Gaussian endpoint<br>`ben:smoothing` | [`gaussianEndpointSmoothing`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/GaussianEndpointSmoothing.lean#L286) |
| Lemma G.3 — Slepian interpolation with paired increments<br>`ben:paired-interpolation` | [`C4Test.hasDerivAt_arraySlepian_of_coordinate_fourths`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/ArraySlepian.lean#L401) |
| Lemma G.4 — A truncated Bennett maximum<br>`ben:maximum` | [`truncated_bennett_maximum`](https://github.com/VC2015/HDCLTs/blob/69f89747f4b845491b75cb23134c056bfbcd40f7/lean-rectangle-clt-singular/RectangleCLTCompanion/SplitV4/BennettMaximum.lean#L332) |


### Reading the combined statements

- **Theorem 1:** `relativeFourthMomentCLT` has the flat fourth-only assumptions;
  `relativeMomentCLT` supplies the corresponding class formulation.
  `relativeEnvelopeCLT` proves the envelope consequence with the same fixed
  universal constant. Both distinct actual fourth matrices are retained.
- **Corollary 3:** the primary endpoint is the relative branch. The separate
  `boundedPolyhedralEnvelopeCLT`, `orliczPolyhedralCLT` and
  `polynomialPolyhedralCLT` cover the other branches. The checked zero-variance
  deletion and all-zero endpoints complete the degenerate cases. The relative
  substitutions are exactly `J*delta` and `J^2*s4`; the polynomial substitution
  is `J^2*B`.
- **Theorems 5, 7 and 8:** the listed `*_uniform_constants` wrappers choose
  constants before all dimension sequences and, where required, before envelope
  sequences. The underlying `fourthMomentLower`, `denseMomentLower` and
  `sparseMomentLower` contain actual probability constructions and matching
  Gaussian covariances. Their optimality endpoints include the genuine symmetric
  and unrestricted class suprema.
- **Theorems 4, 5 and 6:** the stated bounded/fourth/growing-fourth lower
  constants are respectively $1/(8e)$, $1/(2\sqrt{2}e)$ and $1/(4e)$.
- **Lemma G.3:** `C4Test.ofContDiff` supplies genuine canonical derivatives from
  ordinary C4 hypotheses; symmetry and zero skewness are not upper-bound
  assumptions. **G.4** also has an explicit zero-variance endpoint.

The machine-readable [statement map](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/split-v4-certification/statement-map.json)
contains full names, actual expanded types, printed contract definitions,
source context, supplementary helpers and exact evidence locations. The
[dependency map](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/split-v4-certification/dependency-map.json)
records actual type and proof dependencies, rather than an inferred import list.

## 3. Toolchain, execution and reproduction

### Pinned toolchain

- Lean: `leanprover/lean4:v4.19.0`.
- Recorded executable: `Lean (version 4.19.0, x86_64-unknown-linux-gnu, commit 6caaee842e94, Release)`.
- mathlib: v4.19.0, exact revision `c44e0c8ee63ca166450922a373c7409c5d26b00b`.
- Lake and the sibling `lean-kane`, `lean-rectangle-clt-local` and singular
  packages use the checked-in toolchain and manifests. No `lake update` or
  toolchain migration forms part of this certificate.

The final local run executed **one toolchain check, two builds and 164 fresh
audits**, for 167 successful commands. It ran from an isolated detached
checkout with separate project build directories; only pinned third-party
package caches were shared. All 898 Lean-source fingerprints, manifests,
preserved records and pinned Git dependencies were checked before and after.

### Successful CI evidence

[GitHub Actions run 42407941681](https://github.com/VC2015/HDCLTs/actions/runs/42407941681),
job `128509612732`, succeeded for proof source `69f8974`. Artifact
`13588768741` contains the **8 baseline + 167 checkpoint** command records and
logs. The baseline checkout is exactly the manuscript/handoff commit. The PR
workflow's checkout was synthetic merge
`bfe07f34cae3f4776aec2ac4d01da44a406beeb6`; its mathematical proof/configuration
fingerprints and all 3,751 kernel dependency records were compared with the
frozen local source and agree exactly. A CI checkout hash is therefore recorded
separately from the mathematical proof hash.

Evidence retained with the certificate includes:

- [Local final run ledger](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/split-v4-certification/logs-checkpoint-69f8974/run.json),
  SHA-256 `19619a3040bcbba40faf6a77d4fc75e2ac1226eb116acc25e943044e16dbfee3`.
- [Downloaded CI provenance](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/split-v4-certification/logs-ci-thirty-one-statements/PROVENANCE.json),
  including the two CI ledgers, log hashes and archive SHA-256
  `3340804c1a875acadaa879926ebe48507dd9fd974523fb6d8a14ba75c8a1558f`.
- [Complete verification record](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/SPLIT_V4_VERIFICATION.json),
  tying the reviewed scope, proof source, artifact hashes and CI comparison
  together.

Final checks on the later report-bearing PR head are a separate merge gate.
They are visible in [PR #14's checks](https://github.com/VC2015/HDCLTs/pull/14/checks)
and identified in the annotated tag. They do not change the identities of the
issued proof and certificate commits above.

### Fresh execution

Use a full clone containing the pinned commits, an installed pinned Lean/Lake,
Python 3.9 or newer, and the repository's normal dependency access. Use unused temporary
paths. From the repository root, the following reproduces the pristine baseline
and the frozen checkpoint with independent project builds:

```sh
baseline_repo=/tmp/split-v4-baseline-20261107
proof_repo=/tmp/split-v4-proof-20261107
package_name=lean-rectangle-clt-singular
runner_path="$package_name/split-v4-certification/run.py"
git worktree add --detach "$baseline_repo" \
  2bd43fd98d2a8687ccdda3745f9ac8eac96260dd
git worktree add --detach "$proof_repo" \
  69f89747f4b845491b75cb23134c056bfbcd40f7
mkdir -p "$baseline_repo/$package_name/split-v4-certification"
git show "69f89747f4b845491b75cb23134c056bfbcd40f7:$runner_path" \
  > "$baseline_repo/$runner_path"
cd "$baseline_repo/$package_name"
python3 split-v4-certification/run.py baseline \
  --output /tmp/split-v4-baseline-evidence-20261107
mkdir -p "$proof_repo/$package_name/.lake"
ln -s "$baseline_repo/$package_name/.lake/packages" \
  "$proof_repo/$package_name/.lake/packages"
cd "$proof_repo/$package_name"
python3 split-v4-certification/run.py checkpoint --skip-cache \
  --output /tmp/split-v4-proof-evidence-20261107
```

The baseline includes the optional cache command. A cache/network failure is
recorded separately from a proof failure; populating the pinned cache is not
a theorem proof. Output directories must be new or empty. The workflow also
automates a pristine baseline; its sequential cache-sharing arrangement is
described in the certification README.

To validate the **issued** certificate's stored evidence without rewriting it,
run the following from the tagged repository's `lean-rectangle-clt-singular/`
directory, using the receipt generator included with the certificate:

```sh
cert_dir=split-v4-certification
python3 "$cert_dir/refresh_record.py" \
  --logs "$cert_dir/logs-checkpoint-69f8974" \
  --baseline "$cert_dir/logs-ci-thirty-one-statements/split-v4-baseline/run.json" \
  --baseline-workflow-id 42407941681 \
  --ci-provenance "$cert_dir/logs-ci-thirty-one-statements/PROVENANCE.json" \
  --certify-complete --validate-only
```

The expected summary is 31 checked statements, zero pending, 3,751 selected
declarations, 5,757 imported companion theorems and 167 checkpoint commands.
Fresh `/tmp/` execution logs are a separate reproduction; this command checks
the preserved issued evidence. `build-report.py` beside this report rebuilds
`REPORT.pdf` from `REPORT.md` using Pandoc and XeLaTeX.

## 4. Axiom audit and limits of the certificate

The permitted transitive axiom set is exactly **`propext`, `Classical.choice`
and `Quot.sound`**. Every selected declaration's recorded axiom set is a subset;
no `sorryAx`, new analytic axiom or unchecked native shortcut is admitted.

The fresh complete-import audit checked **5,757 companion theorem declarations**.
The selected dependency record contains **3,751 declarations**: 3,738 theorems
attributed by Lean to SplitV4 modules, 11 explicitly selected historical
endpoints and two explicitly audited C4 constructors. Lean's module attribution
can include generated equations in historical namespaces. These counts overlap
with the complete audit and are **not counts of distinct handwritten lemmas**.

The extractor reads actual types and proof values from the checked kernel
environment, separates direct type/proof edges, computes per-declaration
transitive axioms and checks their union with Lean's official collector. Its
optimized implementation was compared record-for-record with the original
collector on all 1,684 declarations of an earlier frozen checkpoint. The final
build and fresh direct extraction agree, as do local and CI records.

The remaining limits are scope and interpretation, rather than an identified
open mathematical obligation:

- Lean certifies the elaborated formal statements. Matching them with the TeX,
  including ambient assumptions, is a reviewed correspondence judgment.
- Certification is tied to the exact bytes above. It does not automatically
  transfer to a later manuscript or to every explanation in the printed proof.
- The stated axioms, Lean/kernel/toolchain and pinned imported library proofs
  are the trusted formal foundation; the analytic manuscript audit is evidence
  for review, not an extra axiom.
- Historical source comments can use older theorem numbers. The current stable
  labels and mapping table govern this report.
- Execution `run.json` files deliberately retain `paper_certified=false`:
  they record command success only. Likewise the generic disclaimer in
  `06-Audit.log` describes that individual audit. Complete scope comes from the
  separate validated mapping and `SPLIT_V4_VERIFICATION.json`.

## 5. Results, printed proofs and alternative arguments

For each row below, the stated result is certified. The distinction concerns
which argument supplies its formal proof. The revised relative, conditional,
threshold, matrix and large-increment chains have their own checked endpoints;
a historical wrapper is not used as a substitute for those separate targets.

| Statement | What the formal proof establishes | Relation to the printed argument |
| --- | --- | --- |
| Corollary 1 | Exact normalization and covariance scaling, then the historical bounded split-matrix CLT. | The rescaling matches. This wrapper uses `RectangleCLT.Companion.unrestrictedCLT`, rather than replaying the new relative chain. That chain is certified separately. |
| Corollary 2 | Clipping, variance standardization, residual control and joint block-Gaussian covariance restoration; exponential admissibility at `2K`. | The printed proof establishes admissibility at `K` by a closure/monotone-convergence step. Lean uses `2K` and a proved rate-scaling inequality to absorb the fixed factor, together with the historical bounded input. |
| Lemma 2 | Actual smoother supremum and full rectangle-distance bound from deterministic common-threshold telescoping through `ceil(L)` shifts and `F(1-F)` envelopes. | This replaces the printed random-logistic-displacement/radius argument. The result is checked; that printed argument is not literally formalized here. |
| Theorem 3 | Actual two-point laws, attained envelope, independent coordinates and the required Gaussian-maximum/product asymptotics. | The scalar input is a specialized proved Esscher/Cramér bound, rather than invoking current Lemma F.1. The general F.1 is also certified separately. |
| Lemma B.3 | Weighted Jensen, exact one-face Gaussian exponential factorization, tangent-mean geometry and weighted Cauchy–Schwarz. | The substantive expanded entropy/face proof is followed. Supporting tangents implement Jensen and Cameron–Martin translation proves the factorization. Prékopa is not an input to this lemma. |
| Lemma C.1 | The intrinsic edge/ramp bound on the **discrete sign cube**, with active supporting branches handling ties directly. | It follows the edge method but bypasses the printed unique-max perturbation and limiting argument. “Uniform cube” here means independent uniform signs on $\{-1,+1\}^n$, not continuous uniform volume. |
| Lemma G.2 | Exponential mixture, Gaussian-only concentration and global-discrepancy absorption using a clock cutoff with bad-event probability at most `1/4` and radius of order `hL`. | The good-event width is bounded by twice the cutoff radius. The printed expected-width/Markov step is not the argument formalized here. |

These comparisons were checked against actual source and the final fresh
`36-DependencyAudit.log`, not inferred from filenames or a successful build.
Relevant implementations include `ObservationNormalization.lean`,
`SubexponentialOrlicz.lean`, `SubexponentialMain.lean`, `Smoothing.lean`,
`Endpoint.lean`, `LowerCramerBound.lean`, `GaussianEntropy.lean`,
`IntrinsicCubeBoundary.lean`, `ClockCutoff.lean` and
`GaussianEndpointSmoothing.lean`. The detailed
[correspondence review](https://github.com/VC2015/HDCLTs/blob/69363df233f20632d73e953d09981ab495abfb50/lean-rectangle-clt-singular/split-v4-certification/CORRESPONDENCE_REVIEW.md)
and statement map identify the corresponding declarations and evidence.

### Is a manuscript clarification advisable?

**Yes, as a scope and exposition clarification.** A short formalization note
should say that the 31 results and required analytic chains are certified for
this version, with the listed formal route variants. Avoid saying that every
printed proof has been verified line by line. If closer textual alignment is
desired, identify or supply the deterministic endpoint proof, the `2K` Orlicz
bridge, direct supporting branches at tied maxima, and the cutoff proof of G.2.
Clarify the discrete meaning of the sign cube wherever “uniform cube” might
otherwise be read as continuous volume.

**No theorem or rate correction is supported by these route differences.**
They establish the stated results by checked arguments; they do not, on their
own, show that an unformalized printed step is wrong. No such clarification
is inserted into the manuscript in this certified snapshot. It belongs in a
separately reviewed editorial revision.

## 6. Checking correspondence after the editorial revisions

Keep the annotated tag and all November/October records immutable. Incorporate
PR #15 and Denis's work on later branches, with their own reviewed manuscript
identities. Then:

1. Compute the revised TeX SHA-256 and Git blob; record the editorial commit(s)
   and new PDF. Check that the PDF actually corresponds to that source.
2. Regenerate the named-statement inventory and compare stable labels, not
   printed numbers alone. Compare the surrounding definitions, quantifier
   order, allowed constant dependence, hypotheses, moment classes, matrices,
   normalizations, rates and referenced equations as well as the environments.
3. Review proof prose separately. Revisit all seven rows in Section 5; a proof
   rewrite can change correspondence even when the theorem text is unchanged.
   Check signs, law names and thresholds in every changed display. For example,
   the pending PR #15 diff at the head recorded above repeats `S` in both
   probabilities of a newly written final endpoint comparison. That display
   needs checking against the intended `S`/`G` comparison before integration;
   it is not present in the certified source and has not been accepted here.
4. If the formal contracts and all semantic assumptions are unchanged, retain
   the existing proof objects but issue a **new correspondence addendum** tied
   to the revised manuscript bytes. Recheck the mapping, artifact integrity
   and fresh Lean audits; unchanged Lean sources plus a green build alone do
   not certify the editorial correspondence. The existing runner deliberately
   rejects a manuscript hash different from the frozen one. Use a separately
   versioned follow-up runner or target configuration for the revised bytes;
   retain the original pins for reproducing this certificate. Changing a pin
   must accompany the new correspondence review and record.
5. If a statement, assumption or required argument changes substantively,
   update the affected Lean contract/proof and run the complete build and
   transitive axiom audits again. Record new dependency/type evidence, every
   remaining proof-route distinction and a new certificate for the new bytes.
   Publish a new tag; do not move or overwrite the November 7 tag or records.

The tagged report and [merged PR #14](https://github.com/VC2015/HDCLTs/pull/14)
therefore remain a stable reference for the certified pre-editorial snapshot,
while subsequent revisions can receive a precise, separate correspondence
record.
