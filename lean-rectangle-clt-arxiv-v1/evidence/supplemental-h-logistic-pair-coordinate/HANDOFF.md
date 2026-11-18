# Actual logistic pair coordinate derivative

Source SupplementalHLogisticPairCoordinateDerivative.lean is FINAL/frozen and cleanly compiled. Build, forced source, strict2, both expanded types and project graph PASS. Only the standard three axioms occur. No earlier frozen source, Root or Audit was edited; no commit was made.

- `supplementalH_hasDerivAt_logistic_power_face_offset u a hh x j l hjl q c`.
- `supplementalH_hasDerivAt_integral_logistic_power_face_offset mu X hX P hP u a hh j l hjl q c`.

The actual derivative of F^(q+1)*pi_j in distinct offset a_l is ((q+2)/h)*F^(q+1)*pi_j*pi_l. Its proof is the frozen power-offset theorem at q+1, multiplied by the actual constant exp(score_j). The generic signed integral theorem keeps P intact, derives primal integrability, and uses global derivative domination by((q+2)/h)*normP. No extra hypothesis occurs beyond probability measure, measurable X, integrable P, h>0 and j!=l.

Receipt: `evidence/supplemental-h-logistic-pair-coordinate/checkpoint-1/run.json`.
Ledger: `correspondence/supplemental-h-logistic-pair-coordinate-passages.json`.
Frozen ledger SHA256: `94cc26dff719b2d536f07d39cc24ad1222126da4262dabeaf0aaf45c95b79fab`.

Mixed Gamma/hard-coarea/trace assembly is separate. Root has the compiled APIs already.
