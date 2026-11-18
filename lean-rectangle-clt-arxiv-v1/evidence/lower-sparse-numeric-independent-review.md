# Independent review of the sparse numerical calibration

Reviewer: lower_resume. Author: intrinsic_main. The reviewer authored shared two-count actual-law and generic masked-detection helpers and the separate actual sparse wrappers, but did not author these two numerical calibration files.

Result: PASS at the source identities below, against the rendered frozen main PDF pages 30–31 (Theorem 8) and 105–107 (F.6), read independently via pdftotext -layout. Main PDF SHA-256: 1b43d0fb5fe1ca0e8397ad049f920609df543b35146409db188beb2f4f0f0ed7. Frozen TeX commit: 1803366cc994d9facae8e128ee180f68e319486f.

The actual headline K uses L=log(e*r*m), while Khat uses ell=log m. The exact factor and uniformly bounded log discrepancy cover either sign of 2/q-1/2. Consequently Kactual tends to infinity implies Khat tends to infinity, and the paper logarithm is eventually between Lambda/3 and Lambda; the log-small headline implies Lambda/ell tends to zero even for bounded or oscillating r. The raw scale is a*k*w_r/sqrt n and is exactly the old scalar scale multiplied by w_r/sqrt ell. The forward bound raw<=headline and reverse actual-width bound headline<=256raw follow from ell<=L<=3ell, gSigma<=2w_r and the eventual logarithm bounds, with q>2 used for the positive exponent beta<=1.

The weak-width step is valid and essential: the old coordinate/scale ratio tends to zero using only Khat divergence. Multiplying that ratio by the NEW weighted raw scale proves the weighted coordinate scale tends to zero. Its exact fourth power is B^2*ell^3*w_r^4/n. The actual uniform positive width lower bound and B>=2 imply ell^3/n tends to zero; theta<=ell/n then tends to zero. The code never infers or assumes that the old worst-dimension sparse scale tends to zero. Variance follows from the exact theta^(2/q)/4 identity. The effective amplitude a*k/ell tends to infinity using the old purely numerical coordinate>=bounded comparison once ell<=n, which was just proved; this supplies the generic masked leading-comparison calibration for every positive leading count.

The old primitives used here are positivity/exact identities, coordinate-to-sparse ratio with only Khat divergence, and a numerical comparison conditional on ell<=n. No old final lower theorem, old sparse actual-family calibration, or old scale-small theta/variance conclusion is used. The combined wrapper audit separately checks these forbidden dependency routes.

Reviewed source SHA-256:
- `RectangleCLTArxivV1/LowerSparseWidthScales.lean`: `d1d9d05f19a352f2652c05bf233444c4ca05069ef11965c9b2f86f530494337a`
- `RectangleCLTArxivV1/LowerSparseWidthLimits.lean`: `41d0e736f5febafce183addb3794eb7349d567555b4c86d068bc77f39dae2006`
