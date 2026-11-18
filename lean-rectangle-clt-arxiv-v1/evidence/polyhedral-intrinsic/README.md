# Corollary 3: intrinsic polyhedral transfer

The combined endpoint is `RectangleCLTArxivV1.corollary_3_intrinsic` in
`PolyhedralIntrinsicMain.lean`. It proves the complete mathematical
statement of Corollary 3 using the newly checked intrinsic Theorem 1,
Theorem 2 and Corollary 2, with all coefficients chosen before the
probability models and normal vectors.

The exact substitutions are:

| Class | Transferred parameter |
|---|---|
| Bounded relative fourth moments | `δ ↦ J δ`, `s₄ ↦ J² s₄` |
| Bounded envelope alone | `δ ↦ J δ` |
| Polynomial envelope alone | `B ↦ J B` |
| Polynomial with coordinate fourth moments | `B ↦ J² B` |
| Sub-exponential coordinates | `K ↦ J K` |

Every conclusion uses the actual expected maximum of the standardized
Gaussian projections. `polyhedralIntrinsicWidth_le` proves its upper
bound `2 sqrt(log(e k))` from Gaussian geometry alone, with no array,
rank or angle hypothesis. Here `k` is the number of positive-variance
faces; the paper renames the retained count `m` after deleting zero faces.
All rate functions are evaluated at the substituted parameters.

The face variances and their square roots are constructed from the actual
Gaussian covariance factor. Actual zero-variance projections vanish
almost surely under both laws. Nonnegative thresholds delete those
inequalities exactly; a negative threshold excludes both vectors. If no
positive-variance face remains, both the discrepancy and width are exactly
zero. Empty and infeasible polyhedra require no geometric regularity
assumption.

The envelope-only bounded statement does not take a relative fourth
budget: the proof constructs both genuine fourth matrices' bounds from
boundedness. The polynomial envelope-only statement does not take
coordinate fourth moments. Both remain separate in the final contracts.

The fourteen proof units plus complete statement are bound to exact
frozen source excerpts in
`correspondence/polyhedral-intrinsic-passages.json`. They follow Appendix
D.2, frozen main lines 6702–6833, for the Corollary 3 statement at 534–584.
The paper commit is `1803366cc994d9facae8e128ee180f68e319486f`, and the
main source SHA-256 is
`e96aaf12ca782c94d70587f128b58a20d3ace8b31a8c324a3272b2b1d71677a2`.
Independent reading-order review is recorded separately and is required
before passage acceptance is claimed.

Reproduce from the new project with the pinned Lean toolchain on PATH:

```
python3 evidence/polyhedral-intrinsic/run_checkpoint.py checkpoint-2
```

The checkpoint builds the combined import, forces all seven polyhedral
sources, strictly audits all 37 new theorem endpoints, and prints expanded
headline types and the transitive project dependency graph. It checks that
all three new intrinsic supplier families occur and that no archived
terminal polyhedral CLT theorem is used. Only `propext`, `Classical.choice`
and `Quot.sound` are permitted. Source hashes are compared before and
after the checkpoint. The two sub-exponential files also have their own
checkpoint in `evidence/subexponential-intrinsic/checkpoint-2`.

Checkpoint 1 is preserved as failed: a doc-comment/`omit` syntax error was
caught during unused-section warning cleanup. It is not a passing receipt.
This scope does not certify the entire release, the conjectural remarks,
or the remaining H.1 surface estimates. Historical sources and archival
receipts remain unchanged.
