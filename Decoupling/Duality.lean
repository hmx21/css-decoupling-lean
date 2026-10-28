import Decoupling.ExtLayers
import Decoupling.ToricWindows
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Concrete dual and conjugated quotient coordinates

This file connects the actual module operations to the matrix conventions
of `notes/main.pdf`: finite-free duals use the dual standard bases, and
dualizing a conjugated matrix produces precisely its Laurent adjoint.
Conjugation changes the scalar action; it is never treated as an R-linear
endomorphism of an unchanged module.
-/

namespace Decoupling.Duality

open Matrix ExtLayers CategoryTheory CategoryTheory.Abelian

noncomputable section

/-- Coordinates in the dual standard basis. The ith coordinate is evaluation
of the functional on the ith standard basis vector. -/
def dualCoordinates (ι : Type) [Fintype ι] [DecidableEq ι] :
    ((ι → R) →ₗ[R] R) ≃ₗ[R] (ι → R) :=
  ((Pi.basisFun R ι).constr R).symm

@[simp] theorem dualCoordinates_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → R) →ₗ[R] R) (i : ι) :
    dualCoordinates ι f i = f (Pi.single i 1) := by
  simp [dualCoordinates, Pi.basisFun_apply]

theorem functional_eq_sum {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : (ι → R) →ₗ[R] R) (a : ι → R) :
    f a = ∑ i, a i * dualCoordinates ι f i := by
  calc
    f a = ((Pi.basisFun R ι).constr R (dualCoordinates ι f)) a := by
      rw [dualCoordinates, LinearEquiv.apply_symm_apply]
    _ = ∑ i, a i * dualCoordinates ι f i := by
      rw [Module.Basis.constr_apply_fintype]
      rfl

/-- Dualizing a matrix is transposition in the prescribed standard bases. -/
theorem dualCoordinates_precomp {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (f : (m → R) →ₗ[R] R) :
    dualCoordinates n (f.comp D.mulVecLin) = D.transpose *ᵥ dualCoordinates m f := by
  funext i
  rw [dualCoordinates_apply, LinearMap.comp_apply]
  change f (D *ᵥ Pi.single i 1) = _
  rw [Matrix.mulVec_single_one]
  exact functional_eq_sum f _

/-- The dual of the conjugated matrix is the manuscript's dagger. -/
theorem dualCoordinates_conjugate_precomp {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (f : (m → R) →ₗ[R] R) :
    dualCoordinates n (f.comp (D.map bar).mulVecLin) = dagger D *ᵥ dualCoordinates m f :=
  dualCoordinates_precomp (D.map bar) f

/-- The same dual coordinate equivalence for categorical module morphisms,
as used by the genuine Ext long exact sequence. -/
def homCoordinates (ι : Type) [Fintype ι] [DecidableEq ι] :
    (ModuleCat.of R (ι → R) ⟶ ModuleCat.of R R) ≃ₗ[R] (ι → R) :=
  ModuleCat.homLinearEquiv.trans (dualCoordinates ι)

@[simp] theorem homCoordinates_apply {ι : Type} [Fintype ι] [DecidableEq ι]
    (f : ModuleCat.of R (ι → R) ⟶ ModuleCat.of R R) (i : ι) :
    homCoordinates ι f i = f (Pi.single i 1) :=
  dualCoordinates_apply f.hom i

theorem homCoordinates_precomp {m n : Type}
    [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]
    (D : Matrix m n R) (f : ModuleCat.of R (m → R) ⟶ ModuleCat.of R R) :
    homCoordinates n (ModuleCat.ofHom D.mulVecLin ≫ f) =
      D.transpose *ᵥ homCoordinates m f :=
  dualCoordinates_precomp D f.hom

/-- The scalar involution is its own inverse. -/
instance barInvPair : RingHomInvPair bar.toRingHom bar.toRingHom where
  comp_eq := RingHom.ext bar_bar
  comp_eq₂ := RingHom.ext bar_bar

/-- Coefficientwise conjugation as a genuinely semilinear equivalence of
the original free modules. -/
def barFreeEquiv (ι : Type) : (ι → R) ≃ₛₗ[bar.toRingHom] (ι → R) where
  toFun := ToricWindows.barVec
  invFun := ToricWindows.barVec
  left_inv := ToricWindows.barVec_barVec
  right_inv := ToricWindows.barVec_barVec
  map_add' a b := by
    funext i
    exact bar_add _ _
  map_smul' r a := by
    funext i
    exact bar_mul _ _

/-- Conjugation sends the actual column image to the column image of the
entrywise conjugated matrix. -/
theorem conjugate_range {m n : Type} [Fintype n] (D : Matrix m n R) :
    (LinearMap.range D.mulVecLin).map (barFreeEquiv m).toLinearMap =
      LinearMap.range (D.map bar).mulVecLin := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨b, ⟨x, rfl⟩, hba⟩
    refine ⟨ToricWindows.barVec x, ?_⟩
    calc
      D.map bar *ᵥ ToricWindows.barVec x = ToricWindows.barVec (D *ᵥ x) :=
        (ToricWindows.barVec_mulVec D x).symm
      _ = a := hba
  · rintro ⟨x, rfl⟩
    refine ⟨D *ᵥ ToricWindows.barVec x, ⟨ToricWindows.barVec x, rfl⟩, ?_⟩
    change ToricWindows.barVec (D *ᵥ ToricWindows.barVec x) = D.map bar *ᵥ x
    rw [ToricWindows.barVec_mulVec, ToricWindows.barVec_barVec]

/-- The concrete cokernel of an arbitrary finite-source matrix. -/
abbrev Cokernel {m n : Type} [Fintype n] (D : Matrix m n R) :=
  (m → R) ⧸ LinearMap.range D.mulVecLin

/-- The semilinear map on actual quotient classes, prior to changing the
domain scalar action. -/
def barCokernelEquiv {m n : Type} [Fintype n] (D : Matrix m n R) :
    Cokernel D ≃ₛₗ[bar.toRingHom] Cokernel (D.map bar) :=
  Submodule.Quotient.equiv _ _ (barFreeEquiv m) (conjugate_range D)

/-- The conjugate of the actual cokernel is linearly isomorphic to the
cokernel of the entrywise conjugated matrix. This is an R-linear map because
the source is `ExtLayers.conjugate`, with its changed scalar action. -/
def conjugateCokernelEquiv {m n : Type} [Fintype n] (D : Matrix m n R) :
    conjugate (ModuleCat.of R (Cokernel D)) ≃ₗ[R] Cokernel (D.map bar) where
  toEquiv := (barCokernelEquiv D).toEquiv
  map_add' := (barCokernelEquiv D).map_add
  map_smul' r a := by
    change barCokernelEquiv D (bar r • (show Cokernel D from a)) =
      r • barCokernelEquiv D a
    rw [map_smulₛₗ]
    simp

@[simp] theorem conjugateCokernelEquiv_mk {m n : Type} [Fintype n]
    (D : Matrix m n R) (a : m → R) :
    conjugateCokernelEquiv D
      (show conjugate (ModuleCat.of R (Cokernel D)) from Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (ToricWindows.barVec a) := rfl

/-- Conjugating the dagger leaves only the ordinary transpose. -/
theorem bar_dagger {m n : Type} (D : Matrix m n R) :
    (dagger D).map bar = D.transpose := by
  funext i j
  exact bar_bar _

/-- The actual conjugated reduced Pauli module is the cokernel of `H_Xᵀ`.
This bridges the paper's module convention to a concrete presentation. -/
def conjugateReducedEquiv {q s r : ℕ} (c : CSS.Checks q s r) :
    conjugate (reduced c) ≃ₗ[R] Cokernel c.H_X.transpose :=
  (conjugateCokernelEquiv (dagger c.H_X)).trans
    (Submodule.quotEquivOfEq _ _ (by rw [bar_dagger]))

/-- Transport genuine Ext groups along an isomorphism of their first input.
The direction is contravariant and the transport is R-linear. -/
def extSourceEquiv {M N : ModuleCat R} (e : M ≅ N) (T : ModuleCat R) (n : ℕ) :
    Ext M T n ≃ₗ[R] Ext N T n where
  toLinearMap := (Ext.mk₀ e.inv).precompOfLinear R T (zero_add n)
  invFun a := (Ext.mk₀ e.hom).comp a (zero_add n)
  left_inv a := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add n)) (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv a := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add n)) (zero_add n) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

end

end Decoupling.Duality
