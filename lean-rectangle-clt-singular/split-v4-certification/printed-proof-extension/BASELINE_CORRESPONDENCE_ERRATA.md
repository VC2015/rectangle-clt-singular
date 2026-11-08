# Baseline correspondence history — owner re-review errata

This note corrects four **initial/baseline** classifications in the central correspondence index. It changes no current classification, Lean source, declaration binding, or evidence hash. The frozen extension proof remains `92896b8a2a4099357486587d17ca1921a3dba161`; the preserved result proof remains `69f89747f4b845491b75cb23134c056bfbcd40f7`.

The final interpolation owner fragment omitted explicit baseline fields. The initial central normalization consequently inferred baseline `SAME_ARGUMENT` from the fragment’s current classification. An explicit re-review by the interpolation owner supplied the corrected history below. The original [hashed interpolation fragment](correspondence/printed-interpolation-map.json) is preserved unchanged.

| Passage / central entry | Original central inference | Corrected baseline | Current coverage | Reason |
| --- | --- | --- | --- | --- |
| TeX 1941–1959 — `interpolation:inputs-conditional-CS` | `SAME_ARGUMENT` | `UNVERIFIED_STEP` | `SAME_ARGUMENT` | The literal conditional square-root-product Cauchy–Schwarz estimate was absent; stronger quadratic budgets sufficed in the preserved proof. |
| TeX 2067–2075 — `interpolation:B1-second-order-taylor` | `SAME_ARGUMENT` | `UNVERIFIED_STEP` | `SAME_ARGUMENT` | The literal centered Hessian-integral identities were not exported in the preserved formal development. |
| TeX 2084–2091 — `interpolation:B1-signed-hessian` | `SAME_ARGUMENT` | `ALTERNATIVE_BYPASS` | `SAME_ARGUMENT` | The preserved endpoint used direct value Taylor4 and gradient Taylor3, bypassing the printed signed-Hessian intermediate. |
| TeX 2103–2110 — `interpolation:B1-hessian-expansion-kernel` | `SAME_ARGUMENT` | `UNVERIFIED_STEP` | `SAME_ARGUMENT` | Separate Hessian Taylor and scalar-kernel results were initially misjudged sufficient. Independent review identified the missing weighted triangular Fubini transition; the extension now proves it. |

In particular, the triangular Fubini gap was found by the [independent core review](correspondence/initial-core-review.md); separate Taylor and kernel identities did not verify that printed transition. The checked `Printed.InterpolationTriangle` additions now supply the actual weighted triangular interchange and its Hessian-to-fourth-remainder application.

The central [coverage record](coverage.json) retains both the original inference and this re-review for each affected entry. Its 811 declaration bindings, 254 current passage records, current classification counts and owner-evidence hashes remain unchanged. The correction is to correspondence history, not to the frozen mathematical development.
