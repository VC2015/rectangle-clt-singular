# Companion verification report

The [PDF](companion_verification.pdf) and
[LaTeX source](companion_verification.tex) describe the five main companion
theorems and both bounds in the sub-exponential corollary. The report lists
their public Lean statements, checked proof components, exact source and CI
references, audit scopes, and the remaining Supplement results.

The report was revised on **23 October 2026**. The original certification
dates remain **20 October** for the three bounded upper bounds and
**21 October** for the sub-exponential, lower-scale, and uniform-consistency
results. The update does not introduce new mathematical claims or proofs.
The historical verification records remain intact:

- [Bounded upper bounds](../VERIFICATION.json).
- [Sub-exponential bounds](../SUBEXPONENTIAL_VERIFICATION.json).
- [Main lower-scale and consistency results](../LOWER_RESULTS_VERIFICATION.json).

The [report-refresh record](../../verification/2026-10-23-report-refresh/README.md)
records the reviewed source, manuscript correspondence, fresh build and
transitive-audit results, and CI provenance. Counts from different audits
overlap and must not be added together.

Compile from this directory:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error companion_verification.tex
```

Report author: **GPT-6.1 Sol Ultra**. Prompted by **Victor Chernozhukov**.

