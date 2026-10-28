import Decoupling.HighDim.StableFreeEffectiveCochainInputs

/-! Execute the actual initial program, recursive Schanuel engine and beta absorption once each. -/
namespace Decoupling.HighDim.StableFree.Effective.CochainProgram
open Matrix LaurentArithmetic ArithmeticCost
universe u
variable {K : Type u} [Field K] [DecidableEq K] {D c n p e rel h h₀ length : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- The materialized initial output is shared by all subsequent computations;
its operations occur exactly once in the returned Work trace. -/
def runInitial (i : Initial.Inputs K D c n p e rel h)
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (hh : h₀ ≤ Initial.radius5 h)
    (hs : (initialStage i.runComplete.value.initial).Solvable)
    (hv : StateValid F G (firstUpdate (identityDense K D (Initial.radius5 h) p)
      i.runComplete.value.initial.complementProjector
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.1
      (solvePresentedStage (initialStage i.runComplete.value.initial) hs).value.2.1).value) :=
  let initial := i.runComplete
  Work.bind initial fun _ =>
    stableCheckProgram (initialStage initial.value.initial) initial.value.initial.complementProjector
      initial.value.forward initial.value.initial.beta F G hh hs hv

noncomputable section
variable {M N : ModuleCat.{u} (Laurent K D)}

/-- The native initial data and actual tail resolutions provide all semantic
premises internally; both presentation lifts come from the counted run. -/
theorem runInitial_presents (i : Initial.Inputs K D c n p e rel h)
    (a : Initial.Data M N c n p e rel) (hi : Initial.Realizes i a)
    (F : DenseTower K D h₀ length n) (G : DenseTower K D h₀ length c)
    (hF : F.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piN)) (LinearMap.ker a.piN).subtype)
    (hG : G.Models (ModuleCat.of (Laurent K D) (LinearMap.ker a.piM)) (LinearMap.ker a.piM).subtype)
    (hh : h₀ ≤ Initial.radius5 h) :
    let hs := initialStage_solvable i a hi
    let hv := initialStage_valid i a hi F G hF hG
    ∃ beta : (N × Power (Laurent K D) (p+(c+(F.ranks G).1))) ≃ₗ[Laurent K D]
        (M × Power (Laurent K D) (p+(n+(F.ranks G).2))),
      (∀ x, stabilizedQuotient a.piM _
        (matrixDenote (runInitial i F G hh hs hv).value.forward *ᵥ x) =
          beta (stabilizedQuotient a.piN _ x)) ∧
      (∀ x, stabilizedQuotient a.piN _
        (matrixDenote (runInitial i F G hh hs hv).value.inverse *ᵥ x) =
          beta.symm (stabilizedQuotient a.piM _ x)) := by
  dsimp only
  have ho := Initial.run_correct i a hi
  apply stableCheckProgram_presents a.piN a.piM (complementAt a) (initialEquiv a)
    (initialStage i.runComplete.value.initial) i.runComplete.value.initial.complementProjector
    ho.2.2.2.2.2 i.runComplete.value.forward i.runComplete.value.initial.beta
  · intro x
    change (a.piM.prodMap (complementAt a).project)
      ((powerAdd c (e+p)).symm (matrixDenote i.makeForward.value *ᵥ x)) = _
    rw [Initial.makeForward_correct i a hi,a.matrixForward_apply]
    exact a.forwardLift_projects x
  · intro x
    change stabilizedQuotient a.piN p (matrixDenote i.run.value.beta *ᵥ x) = _
    rw [ho.2.1]
    exact a.betaArrow.equation x

end
end Decoupling.HighDim.StableFree.Effective.CochainProgram
