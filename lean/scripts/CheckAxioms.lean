import Lean
import CoordCriterion

/-!
# Axiom check

Run from `lean/` with `lake env lean scripts/CheckAxioms.lean` (after
`lake build`).  Reports every constant in namespace `CC` that depends on
`sorryAx` or on an axiom other than `propext`, `Quot.sound` and
`Classical.choice`, and prints the number of theorems checked.
-/

open Lean Elab Command

private def allowed : List Name := [``propext, ``Quot.sound, ``Classical.choice]

elab "#check_cc_axioms" : command => do
  let env ← getEnv
  let mut nThms := 0
  let mut bad : Array (Name × List Name) := #[]
  for (n, ci) in env.constants.toList do
    unless (`CC).isPrefixOf n && !n.isInternal do continue
    if ci matches .thmInfo _ then nThms := nThms + 1
    let axs ← liftCoreM <| collectAxioms n
    let extra := axs.toList.filter (fun a => !allowed.contains a)
    unless extra.isEmpty do bad := bad.push (n, extra)
  if bad.isEmpty then
    logInfo m!"OK: {nThms} theorems in namespace CC; axioms used are among propext, Quot.sound, Classical.choice; no sorry."
  else
    for (n, extra) in bad do
      logError m!"{n} uses {extra}"
    logError m!"{bad.size} constants in CC use disallowed axioms ({nThms} theorems checked)."

#check_cc_axioms
