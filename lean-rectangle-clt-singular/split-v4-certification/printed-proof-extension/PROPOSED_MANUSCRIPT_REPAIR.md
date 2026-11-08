# Proposed positive-order qualification

This proposal concerns the frozen manuscript at
`2bd43fd98d2a8687ccdda3745f9ac8eac96260dd`. It has **not** been applied to
the manuscript or the tagged certificate.

At TeX line 1847, immediately before the local derivative-envelope display,
replace

```latex
=\theta^k\le\theta\) yields
```

with

```latex
=\theta^k\le\theta\) yields, for every integer \(q\ge1\),
```

At TeX line 1872, replace

```latex
Consequently, for fixed \(q\), fixed directions
```

with

```latex
Consequently, for each fixed integer \(q\ge1\), fixed directions
```

The qualification matches every positive-order bound in Lean. A literal
zero-order reading is false, as proved for the actual two-face closed-box
smoother in `Printed.no_uniform_closedBox_zero_order_averaged_bound`.
No theorem rate or positive-order proof needs to change for this repair.

Apply this wording on the editorial branch alongside Yuta’s and Denis’s
revisions. Then record the new manuscript commit and hash, update affected
source anchors and proof correspondence, and rerun the pinned verification
before issuing a certificate for that revised manuscript.
