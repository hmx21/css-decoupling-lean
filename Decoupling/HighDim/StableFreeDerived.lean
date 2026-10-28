import Decoupling.HighDim.StableFreeRanks
import Decoupling.HighDim.CochainCokernelDerived

/-!
# Derived equivalence of supplied free models, using the new C4 construction

This interface lifts an actual native derived isomorphism to homotopies and
then invokes generalized Schanuel. The input consists of the actual bounded
finite free models and their given coordinates, as in Algorithm 2. There is
no freeness theorem for the intermediate projective complement. Existence
of a derived isomorphism and solving its lifting equations are not assigned
a computational cost in this module.
-/

namespace Decoupling.HighDim.StableFree

open CategoryTheory HomologicalComplex
universe u
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {R : Type u} [CommRing R]
variable {C T : CochainComplex (ModuleCat.{u} R) ℤ}

/-- The new stable-cokernel construction from genuine derived-equivalent
input models. The ranks remain the explicit parity totals of their terms. -/
def derivedStableEquiv (cC : Coordinates C) (cT : Coordinates T)
    (l : ℕ) (uC uT : ℤ)
    [C.IsStrictlyGE (-(l : ℤ))] [T.IsStrictlyGE (-(l : ℤ))]
    [C.IsStrictlyLE uC] [T.IsStrictlyLE uT] [C.IsGE 1] [T.IsGE 1]
    (e : DerivedCategory.Q.obj C ≅ DerivedCategory.Q.obj T) :
    (CochainCokernel.CheckCokernel T ×
      Power R (cC.rank 2 + (cochainRanks cC cT l).2)) ≃ₗ[R]
    (CochainCokernel.CheckCokernel C ×
      Power R (cC.rank 2 + (cochainRanks cC cT l).1)) := by
  letI (i : ℤ) : Module.Free R (C.X i) := Module.Free.of_equiv (cC.equiv i).symm
  letI (i : ℤ) : Module.Free R (T.X i) := Module.Free.of_equiv (cT.equiv i).symm
  letI (i : ℤ) : Projective (C.X i) := inferInstance
  letI (i : ℤ) : Projective (T.X i) := inferInstance
  exact homotopyStableEquiv
    (CochainCokernel.homotopyEquivOfDerivedIso_boundedAbove uC uT e) cC cT l

end
end Decoupling.HighDim.StableFree
