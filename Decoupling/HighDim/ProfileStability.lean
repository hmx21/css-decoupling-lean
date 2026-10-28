import Decoupling.HighDim.ResolutionComparison
import Decoupling.HighDim.PhysicalIsomorphism

/-!
# Lemma 5: module-isomorphism invariance of the full profile

Source: `drafts/appendix.tex:202–228`. The actual quotient by the X-stabilizer
submodule is used, with the antipode twist and genuine positive derived Hom.
No topological condition is needed for this invariance statement.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}

/-- The full positive RHom profile of an actual reduced module. -/
def moduleProfile (M : ModuleCat (Laurent K D)) : DerivedCategory (ModuleCat (Laurent K D)) :=
  Profile.ofResolution (projectiveResolution (Layers.conjugate M))
    (ModuleCat.of (Laurent K D) (Laurent K D))

/-- This acts on the entire derived object, including its attachment data. -/
def moduleProfileIso {M N : ModuleCat (Laurent K D)} (e : M ≅ N) :
    moduleProfile M ≅ moduleProfile N :=
  ResolutionComparison.profileIsoOfModuleIso (ModuleCat.of (Laurent K D) (Laurent K D))
    (projectiveResolution (Layers.conjugate M))
    ((ModuleCat.restrictScalars bar.toRingHom).mapIso e) _

variable {Q C : Type} [Fintype C]

/-- The literal quotient of physical representatives by X stabilizers. -/
def matrixReduced (H : Matrix C Q (Laurent K D)) : ModuleCat (Laurent K D) :=
  ModuleCat.of (Laurent K D) ((Q → Laurent K D) ⧸ LinearMap.range (dagger H).mulVecLin)

/-- The same profile for arbitrary finite species/check labels, including block sums. -/
def matrixProfile (H : Matrix C Q (Laurent K D)) := moduleProfile (matrixReduced H)

variable {q s r : ℕ}

/-- The matrix definition agrees with the manuscript's actual CSS profile. -/
def cssProfileIso (c : CSS.Checks K D q s r) : matrixProfile c.H_X ≅ Profile.S_X c :=
  Iso.refl _

/-- A genuine isomorphism of reduced modules induces profile invariance. -/
def cssProfileIsoOfReducedIso {q' s' r' : ℕ}
    (c : CSS.Checks K D q s r) (d : CSS.Checks K D q' s' r')
    (e : Layers.reduced c ≅ Layers.reduced d) : Profile.S_X c ≅ Profile.S_X d :=
  moduleProfileIso e

end
end Decoupling.HighDim.ProfileStability
