#!/usr/bin/env python3
"""Write author support metadata under evidence only; no global promotion."""
from pathlib import Path
import datetime
import hashlib
import json

P = Path(__file__).resolve().parents[2]
D = Path(__file__).resolve().parent
sha = lambda p: hashlib.sha256(Path(p).read_bytes()).hexdigest()
ref = lambda p: {"path": str(Path(p).relative_to(P)), "sha256": sha(p)}
specs = {
    "geometry": ("supplemental-h-nonsimple-face-geometry", "independent-review.json",
                 ["Geometry", "Independence", "NormalCone"]),
    "incidences": ("supplemental-h-nonsimple-face-incidences", "independent-review.json",
                   ["Cofaces", "Conormal", "Coverage", "Tubes"]),
    "retained": ("supplemental-h-nonsimple-face-retained", "independent-bounded-review.json", ["Retained"]),
    "selected": ("supplemental-h-nonsimple-face-selected", "independent-archive-review.json",
                 ["Spanning", "Selected", "SelectedExistence", "SelectedBijection"])}
owned, groups = {}, {}
for key, (directory, review, modules) in specs.items():
    base = P / "evidence" / directory
    receipt = base / "checkpoint-1/run.json"
    data = json.loads(receipt.read_text())
    assert data["status"] == "passed"
    target_file = base / "checkpoint-1/targets.json"
    targets = json.loads(target_file.read_text()) if target_file.exists() else data["targets"]
    targets = targets["targets"] if isinstance(targets, dict) else targets
    sources = {"RectangleCLTArxivV1/SupplementalHNonsimpleFace" + m + ".lean":
               sha(P / "RectangleCLTArxivV1" / ("SupplementalHNonsimpleFace" + m + ".lean")) for m in modules}
    owned.update(sources)
    groups[key] = {"receipt": ref(receipt), "independent_review": ref(base / review),
                   "checked_declarations": targets, "source_sha256": sources}

source = P.parent / "research-rectangle-clt-singular/Rectangle_CLT_Supplement_2026-11-16.tex"
lines = source.read_bytes().splitlines(keepends=True)
def location(a, b):
    return {"source": "supplement", "path": str(source.relative_to(P.parent)), "lines": [a, b],
            "sha256": hashlib.sha256(b"".join(lines[a-1:b])).hexdigest()}

units = [
    ("ACTUAL_FACE_MODEL", "geometry", 1081, 1100,
     "Complete-active-set actual faces, canonical representatives and actual normal-rank indexing; all original inequalities retained."),
    ("ACTUAL_RIDGE_CLASSIFICATION", "geometry", 1081, 1100,
     "Original strict interior and irredundancy derive active pair/triple independence, exact two-facet ridges and active triple spanning at rank3; no three-active-facet restriction."),
    ("GENUINE_NORMAL_CONE", "geometry", 1101, 1110,
     "Local feasible rays and proved finite-cone bipolarity identify the full outward cone, with exact-presentation and singleton-positive-multiple transport."),
    ("COFACES_AND_CONORMALS", "incidences", 1081, 1110,
     "Supporting-pair polar rays construct actual original ridge cofaces. Canonical projected representative differences derive conormal orientation/unit/strict signs."),
    ("NONZERO_POLAR_COVERAGE", "incidences", 1101, 1110,
     "Every nonzero pair-supported polar ray is a nonnegative multiple of an actual incidence conormal; complete generators are retained."),
    ("DISJOINT_ACTUAL_TUBES", "incidences", 1134, 1206,
     "Complete-active actual face events have disjoint nearest-base tubes and factor1 finite R4 indicator/integral sums. Ordinary frame/level/measurability/moment inputs remain explicit."),
    ("RETAINED_POSITIVE_MULTIPLES", "retained", 1081, 1100,
     "Exact selected/retained physical presentation and genuine strict support points derive positive normal and offset multipliers. No proportionality or Green premise."),
    ("SELECTED_COMPLETE_RANK_THREE", "selected", 1081, 1100,
     "Selected tangent facets construct complete original rank3 faces. Their closedfaces equal originalQ intersected with the three independent supporting planes."),
    ("SELECTOR_COFACE_BIJECTION", "selected", 1081, 1100,
     "An actual retained active inequality forces a selected active constraint; equal spanning three-plane closedfaces give the inverse. Exact finite bijection/sum without triple multiplicity.")]

ledger = {"schema_version": 1, "snapshot": "1803366cc994d9facae8e128ee180f68e319486f",
          "created_at_utc": datetime.datetime.now(datetime.timezone.utc).isoformat(),
          "status": "compiled_and_reviewed_supporting_geometry_pending_final_global_correspondence",
          "release_wide_certification": False,
          "scope": "Supporting actual nonsimple face/incidence/selected-facet geometry. The separately assembled global Je Gauss-Green formula and analytic mass/coarea identity are not conclusions of this metadata packet.",
          "frozen_source": {"path": str(source.relative_to(P.parent)), "sha256": sha(source),
              "pdf_sha256": "34fd0ea571b8005646576b933b90a0555d64fe8c385dc98b462ac965c89d7f94"},
          "source_identity": owned, "verification_groups": groups,
          "passages": [{"id": "H1.NONSIMPLE." + name, "location": location(a, b),
              "status": "checked_supporting_geometry", "verification_group": group, "claim": claim,
              "count_scope": "Support binding only, not a new named result or disjoint atomic passage."}
              for name, group, a, b, claim in units],
          "method_notes": [
              "A rank3 normal space can have more than3 active original facets. A spanning triple supplies coordinates only; the full generated cone retains every active original facet.",
              "Actual residual facets are selected by equality of the physical polyhedra and counted once, with no generic-threshold premise.",
              "The coordinate packet proves exact arbitrary-edge vector/area identities by an equivalent Gaussian-first-moment route. Printed sphere-Laplacian prose1112-1123 is not separately formalized here.",
              "Reviews bind source bytes and fresh kernel exports directly. This later author metadata does not promote global correspondence or modify frozen registries."],
          "prerequisite_packets": [ref(P / "evidence/supplemental-h-nonsimple-face-coordinates/source-freeze.json"),
              ref(P / "evidence/supplemental-h-nonsimple-face-cone/checkpoint-1/run.json"),
              ref(P / "evidence/supplemental-h-nonsimple-face-polar-line/checkpoint-1/run.json")]}
path = D / "support-passages.json"
path.write_text(json.dumps(ledger, indent=2, ensure_ascii=False) + "\n")
freeze = {"status": "frozen_support_metadata_with_source_and_review_bindings",
          "source_sha256": owned, "support_ledger": ref(path),
          "verification_groups": {k: {f: v for f, v in d.items() if f in ["receipt", "independent_review"]}
                                  for k, d in groups.items()},
          "prerequisite_packets": ledger["prerequisite_packets"], "no_global_registry_changes": True}
(D / "source-freeze.json").write_text(json.dumps(freeze, indent=2) + "\n")
print(json.dumps({"ledger": ref(path), "source_freeze": ref(D / "source-freeze.json"),
                  "owned_sources": len(owned), "targets_by_group": {k: len(v["checked_declarations"]) for k, v in groups.items()}}))
