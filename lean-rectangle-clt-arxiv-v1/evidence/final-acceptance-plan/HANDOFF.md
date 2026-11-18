# Prepared final acceptance

The live registries, frozen passage ledgers, STATUS, Root and Audit have not been changed by this packet. The final clean build and mapping must both pass before the recorder can produce an acceptance candidate. Applying that candidate additionally requires Root's approval of its exact receipt hash.

The concrete plan is `plan-final.json` (SHA-256 `4a15d38560542485de708bf4ba738c53159c892a068201e3b16f93d944b4a3f2`). It binds proof commit `443fbc667ed3c3ee47369e028c2c4280a5eed604` and the complete 1,949-name mapping plan at `evidence/final-clean-mapping-plan/plan.json`. The recorder is `tools/record_final_acceptance.py` (SHA-256 `78c95521feadb58c7a1b9be8f754c392818a222fa3f61e9c26a5fefd1ffa08b1`). The earlier preparation variants are retained as history.

The plan proposes 39 unqualified named statements, one qualified E.1 statement with A ≥ 0, and one excluded conjecture. It binds all 34 explicit proof environments and 547 passage/support rows. Its 345 distinct canonical units comprise 337 unqualified units and eight qualified E.1 units. Supporting packets can overlap source intervals; their binding counts are separate. The old F4 duplication support row is superseded by its completed paragraph once, without adding a proof environment.

The all-threshold H.1 bound uses actual value continuity and Fatou after generic-threshold geometry. The printed nonsimple ridge Green identity at supplement1081–1100 remains explicitly bypassed and unproved as a separate all-threshold internal claim. Two Gamma rows link explicit checked support packets without claiming their own direct Lean declaration/type atom. Eight empty historical rows are explicitly superseded obligations. Canonical-gap Corollary4 retains an ordinary covariance-factor input; its canonical gap inequality and analytic suppliers are derived. H.3 uses the exact fixed-b bandwidth endpoint.

The 75 authoritative live passage ledgers remain byte-identical. The excluded untracked `lower-width-passages.json` is preserved only as historical snapshot material, and is not an authoritative live-file dependency of the accepted sidecar. Before changing any live registry, the recorder copies all 89 current correspondence JSON/status/README inputs to the candidate's pre-acceptance directory and verifies every hash. The apply phase rechecks the full preservation manifest, every backup file, all fresh evidence, the exact source commit, the current input file set and the approved candidate outputs.

After both clean stages pass, create the reviewable candidate from the project directory:

```sh
python3 tools/record_final_acceptance.py record \
  --plan evidence/final-acceptance-plan/plan-final.json \
  --mapping-plan evidence/final-clean-mapping-plan/plan.json \
  --clean-run evidence/final-clean-checkpoint/run.json \
  --mapping-run evidence/final-clean-mapping/run.json \
  --out evidence/final-acceptance-candidate
```

This command writes candidate outputs under the new evidence directory. It does not mutate the live registries. After Root reviews and approves the candidate's printed receipt SHA-256:

```sh
python3 tools/record_final_acceptance.py apply \
  --candidate evidence/final-acceptance-candidate/receipt.json \
  --approved-receipt-sha256 THE_EXACT_APPROVED_RECEIPT_SHA256
```

Only `correspondence/statements.json`, `correspondence/proof-environments.json`, new `correspondence/final-coverage.json`, new `correspondence/final-acceptance.json`, `correspondence/README.md` and `STATUS.md` are mutation targets. No source or historical passage ledger is rewritten. Seventeen synthetic guard/accounting checks pass in `guard-smoke.json`; these are tests of recorder behavior, not Lean proof evidence.
