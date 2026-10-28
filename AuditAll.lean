import Decoupling
import Lean.Util.CollectAxioms

/-! Audit every imported project declaration, including private helpers and
generated declarations. Reject any transitive axiom outside Lean's standard
classical foundation. This is a check, not a mathematical assumption. -/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let allowed : Array Name := #[``propext, ``Classical.choice, ``Quot.sound]
  let mut count : Nat := 0
  let mut modules : Array Name := #[]
  for (name, _) in env.constants.toList do
    if let some idx := env.getModuleIdxFor? name then
      let modName := env.header.moduleNames[idx.toNat]!
      if (`Decoupling).isPrefixOf modName then
        count := count + 1
        if !modules.contains modName then modules := modules.push modName
        let axioms ← collectAxioms name
        for ax in axioms do
          unless allowed.contains ax do
            throwError "Forbidden axiom {ax} in {name}, from {modName}"
  if count == 0 then throwError "No project declarations were audited"
  logInfo m!"PASS: {count} project declarations from {modules.size} modules; axiom whitelist: {allowed}"
