module

import Solution

/-!
# Axiom check

`lake env lean scripts/CheckAxioms.lean` (after `lake build`) prints the axioms that each compared
theorem of `Solution.lean` depends on. Palomar permits only `propext`, `Classical.choice` and
`Quot.sound`.
-/

#print axioms GwExact.gwProperty_53
#print axioms GwExact.exists_good_3
#print axioms GwExact.exists_good_4
#print axioms GwExact.exists_good_5
#print axioms GwExact.GW_eq_53
