import Decoupling.HighDim.StableCokernelHomotopy
import Decoupling.HighDim.RingDimension
import Decoupling.HighDim.Laurent
import Mathlib.Algebra.Homology.Homotopy

/-!
# Stable check cokernels of actual homotopy equivalent cochain complexes

Source: `drafts/appendix.tex`, C2, lines 490–577. We extract the two degree-one
homotopy identities from mathlib's genuine `HomotopyEquiv` for `ℤ`-indexed
cochain complexes of modules. The check cokernel is the actual quotient of
degree one by the range of the degree-zero differential. For the Laurent
ring the finite-projective-freeness input is discharged by `RingDimension`.
No homotopy data or stable isomorphism is hidden in a profile definition.
-/

namespace Decoupling.HighDim.CochainCokernel

open CategoryTheory HomologicalComplex

universe u

variable {R : Type u} [CommRing R]

/-- The actual cokernel of the differential from degree zero to degree one. -/
abbrev CheckCokernel (C : CochainComplex (ModuleCat.{u} R) ℤ) :=
  (C.X 1) ⧸ LinearMap.range (C.d 0 1).hom

/-- Consecutive actual cochain differentials compose to zero as linear maps. -/
theorem differential_comp (C : CochainComplex (ModuleCat.{u} R) ℤ) :
    (C.d 1 2).hom.comp (C.d 0 1).hom = 0 :=
  congrArg ModuleCat.Hom.hom (C.d_comp_d 0 1 2)

/-- The linear commuting square is extracted from a genuine cochain map. -/
theorem map_comm {C T : CochainComplex (ModuleCat.{u} R) ℤ} (f : C ⟶ T) :
    (f.f 1).hom.comp (C.d 0 1).hom = (T.d 0 1).hom.comp (f.f 0).hom :=
  congrArg ModuleCat.Hom.hom (f.comm 0 1).symm

/-- Read the degree-one homotopy relation with the paper's sign and order.
The homotopy here runs from the identity to the composite; for a homotopy
equivalence this is the symmetric homotopy of mathlib's stored field. -/
theorem homotopy_error {C T : CochainComplex (ModuleCat.{u} R) ℤ}
    (f : C ⟶ T) (g : T ⟶ C) (h : Homotopy (𝟙 C) (f ≫ g)) :
    LinearMap.id - (g.f 1).hom.comp (f.f 1).hom =
      (C.d 0 1).hom.comp (h.hom 1 0).hom +
        (h.hom 2 1).hom.comp (C.d 1 2).hom := by
  have hc := h.comm 1
  rw [dNext_eq h.hom (show (ComplexShape.up ℤ).Rel 1 2 by decide),
    prevD_eq h.hom (show (ComplexShape.up ℤ).Rel 0 1 by decide)] at hc
  have hl := congrArg ModuleCat.Hom.hom hc
  change LinearMap.id = (h.hom 2 1).hom.comp (C.d 1 2).hom +
      (C.d 0 1).hom.comp (h.hom 1 0).hom + (g.f 1).hom.comp (f.f 1).hom at hl
  rw [hl]
  abel

/-- Genuine homotopy equivalence gives stable isomorphism of check cokernels
over the actual Laurent ring. Only the degree-two modules need to be finite
free for this step; freeness of finite projectives is not an input. -/
theorem exists_stableEquiv_of_homotopyEquiv
    {K : Type u} [Field K] {D : ℕ}
    {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}
    (e : HomotopyEquiv C T)
    [Module.Finite (Laurent K D) (C.X 2)] [Module.Free (Laurent K D) (C.X 2)]
    [Module.Finite (Laurent K D) (T.X 2)] [Module.Free (Laurent K D) (T.X 2)] :
    ∃ a b : ℕ, Nonempty
      ((CheckCokernel T × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (CheckCokernel C × (Fin a → Laurent K D))) :=
  StableCokernel.exists_stableFreeEquiv_of_homotopy
    (C.d 0 1).hom (C.d 1 2).hom (T.d 0 1).hom (T.d 1 2).hom
    (differential_comp C) (differential_comp T)
    (e.inv.f 0).hom (e.inv.f 1).hom (e.hom.f 0).hom (e.hom.f 1).hom
    (map_comm e.inv) (map_comm e.hom)
    (e.homotopyHomInvId.symm.hom 1 0).hom (e.homotopyHomInvId.symm.hom 2 1).hom
    (e.homotopyInvHomId.symm.hom 1 0).hom (e.homotopyInvHomId.symm.hom 2 1).hom
    (homotopy_error e.hom e.inv e.homotopyHomInvId.symm)
    (homotopy_error e.inv e.hom e.homotopyInvHomId.symm)
    (RingDimension.finite_projective_free K D)

end Decoupling.HighDim.CochainCokernel
