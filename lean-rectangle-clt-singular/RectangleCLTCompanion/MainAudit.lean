import RectangleCLTCompanion.SharpMain

/-! Inspect the final theorem types and their transitive axiom dependencies.
`CompleteAudit.lean` additionally audits every imported companion theorem. -/

#print RectangleCLT.Companion.UnrestrictedCLT
#print RectangleCLT.Companion.GapSensitiveCLT
#print RectangleCLT.Companion.ZeroSkewCLT
#check RectangleCLT.Companion.unrestrictedCLT
#check RectangleCLT.Companion.gapSensitiveCLT
#check RectangleCLT.Companion.zeroSkewCLT
#check RectangleCLT.Companion.companionCLTExists
#check RectangleCLT.Companion.companionCLTExists_common
#print axioms RectangleCLT.Companion.variationalEstimate
#print axioms RectangleCLT.Companion.zeroSkewVariationalEstimate
#print axioms RectangleCLT.Companion.unrestrictedCLT
#print axioms RectangleCLT.Companion.gapSensitiveCLT
#print axioms RectangleCLT.Companion.zeroSkewCLT
#print axioms RectangleCLT.Companion.companionCLTExists
#print axioms RectangleCLT.Companion.companionCLTExists_common
