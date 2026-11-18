The mapper is `tools/prepare_full_clean_mapping.py`. It reads detailed passage ledgers and the actual Lean declarations of accepted statement records. It retains exact JSON-pointer provenance, explicit checked archived primitives, and qualified theorem scopes. Historical baseline archive_candidate metadata is not a mapped declaration; this never prunes actual kernel dependencies. The excluded early lower-width draft lists its eight otherwise unrequested primitives explicitly.

The exact historical C2 prose item is annotated rather than interpreted as a declaration. Root reviewed the classification and supplied three checked replacement endpoints, all requested explicitly and bound to the existing C2 acceptance bytes. Every other malformed, unresolved or ambiguous target value fails closed.

`final-precommit-plan/` is a provisional current-working-source plan, including the fixed-b H3 and canonical Corollary4 wrappers. It has 1,949 requested declarations and77 hashed correspondence inputs, with no unresolved names/providers/imports. Earlier draft plans are historical infrastructure fixtures. None is a final clean verification.

`smoke-checkpoint-1/` is a focused working-checkout harness check of four public/private/Kane declarations. It checks the exact current renderer, fully explicit type printing, actual imported kernel provider identities and the complete shared kernel axiom union. Independent harvest and runtime/axiom reviews are separate records in this directory.

After the final proof commit, regenerate a plan, then execute it in a separate clean checkout at exactly that commit:

```sh
python3 tools/prepare_full_clean_mapping.py plan --out evidence/full-clean-final-plan
python3 tools/prepare_full_clean_mapping.py run --plan evidence/full-clean-final-plan/plan.json --clean-root /workspace/final-clean/lean-rectangle-clt-arxiv-v1 --out evidence/full-clean-final-mapping
```

The output directory must be outside the clean checkout. Prepare its pinned dependencies/cache first. The runner checks every pinned git package HEAD and tracked-source cleanliness, actual Lean version, exact proof/ledger hashes and clean source status before/after. It builds Root, identifies any explicitly needed provider imports, forces every actual mapped provider plus all ArxivV1 sources in Root/extra import closures, then exports pp.all types and the actual kernel project graph. Final imported-provider identities must match the forced inventory.

The kernel axiom check invokes Lean.CollectAxioms.collect once over all requested names with a shared visited state. It traverses complete kernel type/proof dependencies, including Mathlib; the permitted union is exactly propext, Classical.choice and Quot.sound. A permitted union implies a permitted closure for every target. There is no blanket legacy-CLT exclusion: the lower scalar Berry--Esseen foundation specialization remains explicit, while separate raw headline routes have endpoint-specific independence assertions.

The mapper neither edits Root/Audit nor changes semantic passage or headline acceptance. It preserves failed logs and validates all exact targets instead of dropping missing names.
