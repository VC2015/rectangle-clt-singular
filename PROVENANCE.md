# Public archive provenance

This selected archive was first published on **16 November 2026** from the private HDCLTs repository. It retains 146 commits affecting the allowed manuscripts, Lean sources, and verification records. Every retained commit was checked against the file allowlist, and its author and committer dates were compared with the original. Unrelated research files and their history are excluded. Mixed-project commit messages were replaced with a selected-material description and the original commit ID.

Filtering necessarily changes commit and tree IDs. It does not change the retained file bytes. The [complete map](provenance/commit-map.txt), [date comparison](provenance/commit-dates.json), [path allowlist](provenance/allowed-paths.txt), and [export validation](provenance/export-validation.json) document the transformation. Zero targets in the map identify commits removed because they have no retained changes. Original dates are preserved development metadata; the public release date remains 16 November.

| Snapshot | Original commit | Public counterpart |
| --- | --- | --- |
| manuscript-handoff | `2bd43fd98d2a8687ccdda3745f9ac8eac96260dd` | [`2192ceb37f63`](https://github.com/VC2015/rectangle-clt-singular/commit/2192ceb37f63c56e7bff1356bf7fe6bdbcf88696) |
| result-proof | `69f89747f4b845491b75cb23134c056bfbcd40f7` | [`856146f02b52`](https://github.com/VC2015/rectangle-clt-singular/commit/856146f02b52889d48ecb97c38fd2063f9731087) |
| result-certificate | `69363df233f20632d73e953d09981ab495abfb50` | [`c575a18859d6`](https://github.com/VC2015/rectangle-clt-singular/commit/c575a18859d625a652bf2cdbbc1694ff41e2199d) |
| certified-snapshot | `e692196356de50c00fcdd66ddad0f3706db0241c` | [`74689668a87f`](https://github.com/VC2015/rectangle-clt-singular/commit/74689668a87fc5381477566c9f29579c501b01f5) |
| printed-proof | `92896b8a2a4099357486587d17ca1921a3dba161` | [`7f515de98933`](https://github.com/VC2015/rectangle-clt-singular/commit/7f515de98933646a494cca2438dac23ebf0fc2fa) |
| published-evidence | `0ef13b938895535fe2dcc135b9400688ed97fa61` | [`7ff9414c1b96`](https://github.com/VC2015/rectangle-clt-singular/commit/7ff9414c1b96daadae3d9d4c3e4eb8219c8676b6) |
| manuscript-2026-11-16 | `ca72f5714a74888a587ccb7f060fe895c1bff632` | [`062113621fd0`](https://github.com/VC2015/rectangle-clt-singular/commit/062113621fd025a393554222b5488693f979a88c) |

The original annotated certificate tag, including its **7 November 2026, 22:05:38 UTC** tagger date and annotation, is preserved as [JSON](provenance/original-certificate-tag.json). Its public commit counterpart is the `archive/certified-snapshot` branch. We do not present a newly created public tag as the original tag object.

The archived manuscript, reports, logs, and verification records retain their original bytes, dates and scope. Some historical absolute URLs therefore point to the private source repository. Use the public links in the [Lean guide](LEAN_VERIFICATION.md) or the commit map to locate the corresponding exported file. Original pull-request discussions and unrelated repository contents are not published.

The public-copy checks revalidate the [original result certificate](provenance/public-result-certificate-validation.json), the [printed-proof execution evidence](provenance/public-archive-validation.json), and the [independent CI evidence](provenance/public-ci-evidence-validation.json). They check preserved records and do not perform a new Lean execution. The CI receipt states the one repository-tree adaptation required by filtering. The original validators and records are unchanged.

The [release checksums](provenance/RELEASE_SHA256SUMS) cover the current paper, supplement, source packages and public guides. `provenance/SHA256SUMS` records the original export transport and manifest hashes; the transport bundle itself is represented here by its imported Git objects. The separate [PDF/source checks](research-rectangle-clt-singular/Rectangle_CLT_arXiv_2026-11-16_checks.md) document the arXiv preparation.
