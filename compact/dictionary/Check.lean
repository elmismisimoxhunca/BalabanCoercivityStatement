import CompactDictionary

-- Check the exact public equivalence and its axiom dependencies.
example : BalabanCompact.P428Target8 ↔ AdalyFormal.StatementLaneG.P428Target8 :=
  CompactDictionary.p428Target8_iff

#check CompactDictionary.p428Target8_iff
#print axioms CompactDictionary.p428Target8_iff
