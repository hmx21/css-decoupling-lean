import Decoupling.HighDim.SchreyerLocalizationTransport
import Decoupling.HighDim.SchreyerResolutionExistence

/-!
# HD014 finite free Laurent submodule resolutions without a terminal basis

Finite Laurent generators are shifted into the genuine D-variable
polynomial ring. The proved Schreyer matrix resolution is localized with
its actual differentials and augmentation. Its image is identified with
the original Laurent submodule, and its length remains D-1.
-/
namespace Decoupling.HighDim.SchreyerLocalization
open CategoryTheory Matrix PolynomialLaurent
noncomputable section
universe u
variable {K : Type u} [Field K] {D m n : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

theorem exists_range_data (B : Matrix (Fin m) (Fin n) (Laurent K D)) :
    Nonempty (FreeData (ModuleCat.of (Laurent K D) (LinearMap.range B.mulVecLin)) (D-1)) := by
  obtain ⟨C⟩ := clearedMatrix_exists B
  let N := LinearMap.range C.matrix.mulVecLin
  obtain ⟨A⟩ := SchreyerResolution.exists_data N
  have he : localizedImage A = LinearMap.range B.mulVecLin :=
    augmentation_range_original B C A.augmentation A.range_augmentation
  exact ⟨(native A).transport (LinearEquiv.ofEq _ _ he).toModuleIso⟩

/-- A finite generator matrix is derived from actual Noetherianity. This
chooses generators of the submodule, not a basis of a projective module. -/
theorem exists_generating_matrix (N : Submodule (Laurent K D) (Fin m → Laurent K D)) :
    ∃ n : ℕ, ∃ B : Matrix (Fin m) (Fin n) (Laurent K D), LinearMap.range B.mulVecLin=N := by
  let : Module.Finite (Laurent K D) (Fin m → Laurent K D) :=
    Module.Finite.of_basis (Pi.basisFun (Laurent K D) _)
  let : Module.Finite (Laurent K D) N := inferInstance
  obtain ⟨n,f,hf⟩ := Module.Finite.exists_fin' (Laurent K D) N
  let g := N.subtype.comp f
  refine ⟨n,LinearMap.toMatrix' g,?_⟩
  have hg : (LinearMap.toMatrix' g).mulVecLin=g := by
    apply LinearMap.ext
    intro x
    exact LinearMap.toMatrix'_mulVec g x
  rw [hg]
  ext x
  constructor
  · rintro ⟨y,rfl⟩
    exact (f y).property
  · intro hx
    obtain ⟨y,hy⟩ := hf ⟨x,hx⟩
    exact ⟨y,congrArg Subtype.val hy⟩

/-- Every actual Laurent submodule has the claimed short finite free
resolution, with all intermediate data supplied by the construction. -/
theorem exists_submodule_data (N : Submodule (Laurent K D) (Fin m → Laurent K D)) :
    Nonempty (FreeData (ModuleCat.of (Laurent K D) N) (D-1)) := by
  obtain ⟨n,B,hB⟩ := exists_generating_matrix N
  obtain ⟨A⟩ := exists_range_data B
  exact ⟨A.transport (LinearEquiv.ofEq _ _ hB).toModuleIso⟩

def submoduleData (N : Submodule (Laurent K D) (Fin m → Laurent K D)) :
    FreeData (ModuleCat.of (Laurent K D) N) (D-1) :=
  Classical.choice (exists_submodule_data N)

end
end Decoupling.HighDim.SchreyerLocalization
