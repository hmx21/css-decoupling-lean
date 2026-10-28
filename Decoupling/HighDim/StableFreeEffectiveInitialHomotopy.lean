import Decoupling.HighDim.StableFreeEffectiveInitialAlgebra
import Decoupling.HighDim.StableFreeHomotopy

/-!
# HD012 obtaining the initial presented data from the actual computed homotopy

All quotient maps, error factorizations and free-coordinate lifts in
`Initial.Data` are derived here. They are not additional assumptions on
the original code or a stable-cokernel isomorphism supplied by the caller.
The supplied term coordinates are the original finite-free input coordinates.
-/
namespace Decoupling.HighDim.StableFree.Effective.Initial
open CategoryTheory HomologicalComplex Matrix
universe u
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {R : Type u} [CommRing R]
  {C T : CochainComplex (ModuleCat.{u} R) ℤ}

def homotopyData (e : HomotopyEquiv C T) (cC : Coordinates C) (cT : Coordinates T) :
    Data (ModuleCat.of R (CochainCokernel.CheckCokernel C))
      (ModuleCat.of R (CochainCokernel.CheckCokernel T))
      (cC.rank 1) (cT.rank 1) (cC.rank 2) (cT.rank 2) (cT.rank 0) := by
  let πC := (LinearMap.range (C.d 0 1).hom).mkQ
  let πT := (LinearMap.range (T.d 0 1).hom).mkQ
  let f := StableCokernel.cokernelMap (C.d 0 1).hom (T.d 0 1).hom
    (e.hom.f 0).hom (e.hom.f 1).hom (CochainCokernel.map_comm e.hom)
  let g := StableCokernel.cokernelMap (T.d 0 1).hom (C.d 0 1).hom
    (e.inv.f 0).hom (e.inv.f 1).hom (CochainCokernel.map_comm e.inv)
  let ξC := StableCokernel.cokernelDifferential (C.d 0 1).hom (C.d 1 2).hom
    (CochainCokernel.differential_comp C)
  let ξT := StableCokernel.cokernelDifferential (T.d 0 1).hom (T.d 1 2).hom
    (CochainCokernel.differential_comp T)
  let hC := (e.homotopyHomInvId.symm.hom 2 1).hom
  let hT := (e.homotopyInvHomId.symm.hom 2 1).hom
  let ζC := πC.comp hC
  let ζT := πT.comp hT
  have errC : LinearMap.id - g.comp f = ζC.comp ξC :=
    StableCokernel.cokernel_error_factorization (C.d 0 1).hom (C.d 1 2).hom (T.d 0 1).hom
      (CochainCokernel.differential_comp C)
      (e.inv.f 0).hom (e.inv.f 1).hom (e.hom.f 0).hom (e.hom.f 1).hom
      (CochainCokernel.map_comm e.inv) (CochainCokernel.map_comm e.hom)
      (e.homotopyHomInvId.symm.hom 1 0).hom hC
      (CochainCokernel.homotopy_error e.hom e.inv e.homotopyHomInvId.symm)
  have errT : LinearMap.id - f.comp g = ζT.comp ξT :=
    StableCokernel.cokernel_error_factorization (T.d 0 1).hom (T.d 1 2).hom (C.d 0 1).hom
      (CochainCokernel.differential_comp T)
      (e.hom.f 0).hom (e.hom.f 1).hom (e.inv.f 0).hom (e.inv.f 1).hom
      (CochainCokernel.map_comm e.hom) (CochainCokernel.map_comm e.inv)
      (e.homotopyInvHomId.symm.hom 1 0).hom hT
      (CochainCokernel.homotopy_error e.inv e.hom e.homotopyInvHomId.symm)
  let relMap := (cT.equiv 1).toLinearMap.comp ((T.d 0 1).hom.comp (cT.equiv 0).symm.toLinearMap)
  refine {
    piM := πC.comp (cC.equiv 1).symm.toLinearMap
    piN := πT.comp (cT.equiv 1).symm.toLinearMap
    surjM := (LinearMap.range (C.d 0 1).hom).mkQ_surjective.comp (cC.equiv 1).symm.surjective
    surjN := (LinearMap.range (T.d 0 1).hom).mkQ_surjective.comp (cT.equiv 1).symm.surjective
    relations := LinearMap.toMatrix' relMap
    kerN := ?_
    f := f
    g := g
    xiM := (cC.equiv 2).toLinearMap.comp ξC
    zetaM := ζC.comp (cC.equiv 2).symm.toLinearMap
    xiN := (cT.equiv 2).toLinearMap.comp ξT
    zetaN := ζT.comp (cT.equiv 2).symm.toLinearMap
    errorM := ?_
    errorN := ?_
    F := (cT.equiv 1).toLinearMap.comp ((e.hom.f 1).hom.comp (cC.equiv 1).symm.toLinearMap)
    G := (cC.equiv 1).toLinearMap.comp ((e.inv.f 1).hom.comp (cT.equiv 1).symm.toLinearMap)
    X := (cC.equiv 2).toLinearMap.comp ((C.d 1 2).hom.comp (cC.equiv 1).symm.toLinearMap)
    Y := (cT.equiv 2).toLinearMap.comp ((T.d 1 2).hom.comp (cT.equiv 1).symm.toLinearMap)
    Z := (cC.equiv 1).toLinearMap.comp (hC.comp (cC.equiv 2).symm.toLinearMap)
    T := (cT.equiv 1).toLinearMap.comp (hT.comp (cT.equiv 2).symm.toLinearMap)
    F_lifts := ?_
    G_lifts := ?_
    X_lifts := ?_
    Y_lifts := ?_
    Z_lifts := ?_
    T_lifts := ?_ }
  · ext x
    change πT ((cT.equiv 1).symm x) = 0 ↔ ∃ y, LinearMap.toMatrix' relMap *ᵥ y = x
    change (Submodule.Quotient.mk ((cT.equiv 1).symm x) :
      CochainCokernel.CheckCokernel T) = 0 ↔ _
    rw [Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨y,hy⟩
      refine ⟨cT.equiv 0 y, ?_⟩
      rw [LinearMap.toMatrix'_mulVec]
      change cT.equiv 1 ((T.d 0 1).hom ((cT.equiv 0).symm (cT.equiv 0 y))) = x
      rw [LinearEquiv.symm_apply_apply, hy, LinearEquiv.apply_symm_apply]
    · rintro ⟨y,hy⟩
      rw [LinearMap.toMatrix'_mulVec] at hy
      refine ⟨(cT.equiv 0).symm y, ?_⟩
      exact (cT.equiv 1).injective (hy.trans ((cT.equiv 1).apply_symm_apply x).symm)
  · rw [errC]
    apply LinearMap.ext
    intro x
    change ζC (ξC x) = ζC ((cC.equiv 2).symm (cC.equiv 2 (ξC x)))
    rw [LinearEquiv.symm_apply_apply]
  · rw [errT]
    apply LinearMap.ext
    intro x
    change ζT (ξT x) = ζT ((cT.equiv 2).symm (cT.equiv 2 (ξT x)))
    rw [LinearEquiv.symm_apply_apply]
  · apply LinearMap.ext
    intro x
    change πT ((cT.equiv 1).symm (cT.equiv 1 ((e.hom.f 1).hom ((cC.equiv 1).symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · apply LinearMap.ext
    intro x
    change πC ((cC.equiv 1).symm (cC.equiv 1 ((e.inv.f 1).hom ((cT.equiv 1).symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    rfl
  · apply LinearMap.ext
    intro x
    change πC ((cC.equiv 1).symm (cC.equiv 1 (hC ((cC.equiv 2).symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl
  · apply LinearMap.ext
    intro x
    change πT ((cT.equiv 1).symm (cT.equiv 1 (hT ((cT.equiv 2).symm x)))) = _
    rw [LinearEquiv.symm_apply_apply]
    rfl

end
end Decoupling.HighDim.StableFree.Effective.Initial
