import Decoupling.HighDim.SchreyerCSS

/-!
# HD014 choosing the third prescribed term from the actual check kernel

Noetherianity supplies a finite generating matrix for `ker H_X†`. This
choice only constructs the prescribed third term; it makes no claim that
repeating arbitrary kernel generation yields the short Schreyer tail.
-/
namespace Decoupling.HighDim.SchreyerCSS
open CategoryTheory Matrix
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {D q s r : ℕ}

theorem exists_gamma (c : CSS.Checks K D q s r) :
    ∃ t : ℕ, ∃ gamma : Matrix (Fin t) (Fin s) (Laurent K D),
      LinearMap.range (dagger gamma).mulVecLin =
        LinearMap.ker (dagger c.H_X).mulVecLin := by
  let N := LinearMap.ker (dagger c.H_X).mulVecLin
  let : Module.Finite (Laurent K D) (Fin s → Laurent K D) :=
    Module.Finite.of_basis (Pi.basisFun (Laurent K D) _)
  let : Module.Finite (Laurent K D) N := inferInstance
  obtain ⟨t,g,hg⟩ := Module.Finite.exists_fin' (Laurent K D) N
  let f : (Fin t → Laurent K D) →ₗ[Laurent K D] (Fin s → Laurent K D) :=
    N.subtype.comp g
  refine ⟨t,dagger (LinearMap.toMatrix' f),?_⟩
  rw [dagger_dagger]
  have hf : (LinearMap.toMatrix' f).mulVecLin = f := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec f x
  rw [hf]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (g y).property
  · intro hx
    obtain ⟨y,hy⟩ := hg ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩

end
end Decoupling.HighDim.SchreyerCSS
