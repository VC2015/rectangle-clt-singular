# Independent review of the actual Theorems 5 and 7 calibrations

Reviewer: lower_resume. Author: intrinsic_main. The reviewer authored the shared actual-family and generic unmasked detection helpers imported by these files, but did not author the fourth/dense amplitude calibrations or headline instantiations reviewed here.

Frozen source: research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex at 1803366cc994d9facae8e128ee180f68e319486f; statements 2381–2399 and 2456–2474, proofs 8499–8653.

Result: PASS for mathematical correspondence and hypothesis/quantifier review of the two files at the SHA-256 identities below. The rendered frozen main PDF was independently read through pdftotext -layout extraction, pages 29–30 (Theorems 5 and 7) and pages 103–105 (F.5), in addition to the TeX and Lean types. Main PDF SHA-256: 1b43d0fb5fe1ca0e8397ad049f920609df543b35146409db188beb2f4f0f0ed7. This is a mathematical source and exported-statement review; execution/axiom evidence is the author's separate lower-fourth-dense checkpoint.

Theorem 7: the literal amplitude is (B/2)*theta^(-1/q), theta=log(m)/(2n), pi=1. The finite-prefix fallback is the shared actual lowerUnmaskedSequence, and eventual parameter equality is proved from the printed width-small rate, without a log(m)^3/n assumption. The raw scale identity and domination by L=log(e*r*m) justify the vanishing scale. The separate theta-to-zero argument uses the actual raw variance bound and q>2, then proves amplitude at least one. Moment membership is an output for the actual product law: Lq norm bound follows from exact inverse rpow identity and s<=1; for fixed B and q>4 the rare fourth factor tends to zero and actual coordinate fourth moments are eventually <=B^2. The constant precedes varying B,r,m and depends only on fixed q. The exact prescribed width ratio tends to one and both actual signed orthant and rectangle lower bounds retain the actual Gaussian width.

Theorem 5: q=4,B=2 in the literal dense parameters yields exactly theta^(-1/4), not a different fourth-moment example. The code proves theta*a^4=1, pi=1, coordinate fourth <=14/5<4 and actual C4(2) membership (envelope fourth <=16 is carried by PolynomialFourthHypotheses through the established Lq bound). The doubled rate conversion is exact. Positive lower/upper constants precede r,m; width-small rate is w_r*n^(-1/4)*L^(3/4); all positive leading counts, including r=1 and oscillating bounded r, are covered by the shared generic calibration. The two-sided result applies the independently established actual Theorem 2(ii) to the same law and covariance factor. No desired lower-discrepancy estimate or assumed construction is a premise.

The fourth-envelope membership proof takes the already established L4 Minkowski bound and the exact activation identity to obtain 16. This is a valid proof of the headline C4(2) conclusion; the literal auxiliary inequality 8(s^4+theta*a^4) displayed in (F.24) is a separate printed supporting step and is not itself asserted by these two modules.

The explicit constructions imply the paper's existential observations statements. PolynomialEnvelopeHypotheses and PolynomialFourthHypotheses are actual integral/moment fields, while LowerRectangularFamilyProperties supplies iid, centering, central symmetry, unit marginal variance, exact covariance and Gaussian identification. The separate upper comparison after Theorem 7 uses log(en)^(1/2-1/q) and the actual new Theorem 2(i).

Reviewed source SHA-256:
- `RectangleCLTArxivV1/LowerDenseParameters.lean`: `89c50e42299bd6c0e9fc54da1aae04017438c12e20571515d164c778061540fa`
- `RectangleCLTArxivV1/LowerFourthParameters.lean`: `4b9f5b62a928264151897865e178636adca2971136def342a81c9fc8969d4c7a`

## Literal F.24 addon review

PASS: `LowerFourthPrintedMoments.lean` was independently reviewed against rendered PDF page 104, display F.24. Its universal quartic inequality is proved, the actual array law is transferred to the actual seed law using the proved identical distribution, and the activated fourth power has integral theta*a^4 under the actual Bernoulli law. The pointwise actual observation envelope and monotonic fourth power then prove exactly E||X_i||^4<=8(s^4+theta*a^4), followed by <=16 for the literal q4 parameters. The separate variance=sqrt(theta) conclusion follows from pi=1 and theta*a^4=1 with both quantities nonnegative. No assumed moment conclusion or alternative law enters.

Addon source SHA-256: `42090fca20d63d6b44c1e94a63aa9947fe1775c76ce78edf2a23039d6e11852c`. Strict four-target execution/axiom evidence is the author's `evidence/lower-fourth-printed-moments/checkpoint-1/`.
