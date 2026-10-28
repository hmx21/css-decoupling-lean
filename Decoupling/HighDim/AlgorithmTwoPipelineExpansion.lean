import Lean.Elab.Term
import Lean.Meta.Transform
import Lean.Meta.Tactic.Delta

/-!
# Definition expansion for the finite-data execution entry

`expand_runtime% [f, ...] t` performs only delta expansion of the explicit
whitelist, beta reduction, and structure projection reduction. Proofs and
types are left untouched and runtime let bindings are preserved. It is
elaboration automation for writing out the existing program body, not a
new implementation, solver, axiom, or mathematical lemma. `Work.bind` is
not expanded: its Work argument is evaluated once by the original call,
so beta substitution cannot duplicate a field-operation computation.
The resulting
ordinary Lean term is checked by the kernel; the backend additionally
proves equality of the whole Work value and trace by reflexivity.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineExpansion
open Lean Meta Elab Term

syntax (name := expandRuntime) "expand_runtime%" "[" ident,* "]" term : term

@[term_elab expandRuntime] meta def elaborate : TermElab := fun stx expected => do
  let names ← stx[2].getSepArgs.mapM fun id => resolveGlobalConstNoOverload id
  if names.contains `Decoupling.HighDim.ArithmeticCost.Work.bind then
    throwError "Work.bind must remain a call to preserve evaluation sharing"
  let e ← instantiateMVars (← elabTerm stx[4] expected)
  Meta.transform e (pre := fun e => do
    if ← isProof e then return .done e
    if ← isType e then return .done e
    if let .const name levels := e.getAppFn then
      if names.contains name then
        let info ← getConstInfo name
        if info.hasValue then
          let value ← instantiateValueLevelParams info levels
          return .visit (value.betaRev e.getAppRevArgs (useZeta := false))
    if e.isProj then
      if let some e' ← reduceProj? e then return .visit e'
    return .continue)

end Decoupling.HighDim.AlgorithmTwoPipelineExpansion
