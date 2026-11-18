#!/usr/bin/env python3
"""Check that the final H2 headline actually reaches all native suppliers."""
import hashlib
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
BASE = ROOT / 'evidence/supplement-h-pair-matrix/checkpoint-1'
EXPORT = BASE / 'expanded-types.json'
data = json.loads(EXPORT.read_text())
graph = {row['name']: row['direct_project_dependencies']
         for row in data['project_dependency_graph']}
headline = 'RectangleCLTArxivV1.proposition_H2_pair_matrix_shifted'
seen, todo = set(), [headline]
while todo:
    name = todo.pop()
    if name in seen:
        continue
    seen.add(name)
    todo.extend(graph.get(name, []))
required = [
    'proposition_H2_pair_matrix',
    'intrinsicRectangleConcentration_pairPhysicalMass',
    'intrinsicRectangleConcentration_pairPhysicalProjection',
    'intrinsicRectangleConcentration_pairPhysicalTrace',
    'positiveGammaSoftOrderedPairMass_concentrated_base',
    'positiveGammaSoftOrderedPairProjection_concentrated_base',
    'positiveGammaSoftOrderedPairMass_eq_gamma',
    'positiveGammaSoftOrderedPairProjection_eq_gamma',
    'supplementalH_gamma_positive_edge_mass_budget_small_delta',
    'supplementalH_gamma_positive_edge_normSq_budget_small_delta',
    'supplementalH_gamma_weighted_ridge_budget_small_delta',
    'supplementalH_signedRidge_soft_sum_coarea',
    'intrinsicRectangleConcentration_pairMatrix_of_mass_projection_trace',
    'intrinsicRectangleConcentration_pairFamilyEntropy_of_mass',
    'intrinsicRectangleConcentration_pair_angular_reference_mass',
    'supplementalH_pair_matrix_bracket_le_power',
]
required = ['RectangleCLTArxivV1.' + name for name in required]
assert all(name in seen for name in required), [name for name in required if name not in seen]
receipt = dict(status='passed', headline=headline,
               expanded_types_sha256=hashlib.sha256(EXPORT.read_bytes()).hexdigest(),
               reachable_declaration_count=len(seen),
               required_actual_proof_dependencies=required,
               note='Reachability is computed from the final shifted headline, not from the union of independent audit targets.')
(BASE / 'dependency-check.json').write_text(json.dumps(receipt, indent=2) + '\n')
print('PASS: final shifted H2 reaches all sixteen actual native proof suppliers')
