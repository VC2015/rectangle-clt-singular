# Lean verification of arXiv:2611.21474v1

[Browse the interactive Blue Blueprint](https://vc2015.github.io/rectangle-clt-singular/blueprint/) or [download the PDF reader](https://vc2015.github.io/rectangle-clt-singular/blueprint/rectangle-clt-blueprint.pdf).

The verification covers the 16 November 2026 paper and its separate supplement, Appendices G–I. The theorem index pairs each printed result with the Lean declaration that proves it. The proof records link steps in the paper to their Lean declarations. [Paper](https://arxiv.org/abs/2611.21474v1) · [Theorem-to-Lean index](lean-rectangle-clt-arxiv-v1/STATUS.md) · [Proof correspondence](lean-rectangle-clt-arxiv-v1/correspondence/final-coverage.json)

Of the 40 named results, 39 are checked as stated. In Lemma E.1, Lean makes explicit that the envelope scale satisfies $A\ge 0$. The printed proof treats $A=0$ separately and otherwise uses $AL^{-1/q}$ as a truncation level. Its application takes the nonnegative $q$th root of the moment bound. Conjecture 1 remains open. [Lemma E.1 and its proof](https://github.com/VC2015/rectangle-clt-singular/blob/1803366cc994d9facae8e128ee180f68e319486f/research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16.tex#L6882-L6924) · [Lean correspondence for E.1](lean-rectangle-clt-arxiv-v1/correspondence/expected-maximum-passages.json)

All 34 explicit proof environments have source and declaration mappings. For supplemental Lemma H.1, Lean checks the geometric proof in the paper, including the pointwise ridge Gauss–Green identity and the spherical conormal identity. An alternative Lean proof obtains the all-threshold surface bound by continuity and Fatou’s lemma. [H.1 completion record](lean-rectangle-clt-arxiv-v1/correspondence/supplemental-h-nonsimple-printed-completion.json) · [Mathematical note on the continuity argument (PDF)](lean-rectangle-clt-arxiv-v1/writeups/H1_continuity_Fatou.pdf)

| Clean proof commit | Recorded checks |
| --- | --- |
| [443fbc6](https://github.com/VC2015/rectangle-clt-singular/commit/443fbc667ed3c3ee47369e028c2c4280a5eed604) | [Library and axiom checks](lean-rectangle-clt-arxiv-v1/evidence/final-clean-checkpoint/run.json) and [complete manuscript mapping](lean-rectangle-clt-arxiv-v1/evidence/final-clean-mapping/run.json) covering 1,949 declaration types. |
| [63c975b](https://github.com/VC2015/rectangle-clt-singular/commit/63c975b7bd2176ddf559dbed1b2e087e191f7a45) | [H.1 extension](lean-rectangle-clt-arxiv-v1/evidence/supplemental-h-nonsimple-printed/clean-checkpoint/run.json) with a whole-library build, 66 directly checked source modules, 537 new declaration types, and 182 registered axiom targets. |

The audits report only `propext`, `Classical.choice`, and `Quot.sound`. The reproduction guide gives the commands for both proof commits and identifies the public generic-chaining dependency. The earlier V4 certificate has its own manuscript and evidence. [Reproduction guide](lean-rectangle-clt-arxiv-v1/REPRODUCIBILITY.md) · [Manuscript and dependency hashes](lean-rectangle-clt-arxiv-v1/source-pins.json) · [V4 archive](LEAN_VERIFICATION.md)
