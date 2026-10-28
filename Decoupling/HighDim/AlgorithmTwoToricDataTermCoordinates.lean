import Decoupling.HighDim.AlgorithmTwoToricDataCells
import Decoupling.HighDim.ToricModel

/-!
# Native toric terms in the explicit mask coordinates

These are semantic coordinate equivalences for the actual extended
Koszul complex. The operational mask enumeration is independently
computable. No enumerated basis is selected with `Fintype.equivFin`.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory Koszul
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section

def maskTermCoordinates (A : Type) [CommRing A] (D k : ℕ) :
    Term A D k ≃ₗ[A] ({a : Fin (2 ^ D) // (subsetAt D a).card = k} → A) :=
  (Finsupp.domLCongr (R := A) (M := A) (cellMaskEquiv D k)).trans
    (Finsupp.linearEquivFunOnFinite A A _)

@[simp] theorem maskTermCoordinates_apply (A : Type) [CommRing A] (D k : ℕ)
    (v : Term A D k) (a : {a : Fin (2 ^ D) // (subsetAt D a).card = k}) :
    maskTermCoordinates A D k v a = v (cellOfSet (subsetAt D a.val) a.property) := by
  simp [maskTermCoordinates, cellMaskEquiv]

theorem maskTermCoordinates_symm_single (A : Type) [CommRing A] (D k : ℕ)
    (a : {a : Fin (2 ^ D) // (subsetAt D a).card = k}) :
    (maskTermCoordinates A D k).symm (Pi.single a 1) =
      Finsupp.single (cellOfSet (subsetAt D a.val) a.property) 1 := by
  classical
  apply (maskTermCoordinates A D k).injective
  rw [LinearEquiv.apply_symm_apply]
  funext b
  rw [maskTermCoordinates_apply]
  change (Pi.single a (1 : A) : _ → A) b =
    (Finsupp.single ((cellMaskEquiv D k).symm a) (1 : A)) ((cellMaskEquiv D k).symm b)
  simp [Finsupp.single_apply, Pi.single_apply, eq_comm]

def GradeMask (D : ℕ) (j n : ℤ) := {a : Fin (2 ^ D) // j - ((subsetAt D a).card : ℤ) = n}

def gradeMaskEquiv (D : ℕ) (j n : ℤ) (k : ℕ) (hk : j - (k : ℤ) = n) :
    {a : Fin (2 ^ D) // (subsetAt D a).card = k} ≃ GradeMask D j n where
  toFun a := ⟨a.val, by rw [a.property]; exact hk⟩
  invFun a := ⟨a.val, by have := a.property; omega⟩
  left_inv _ := rfl
  right_inv _ := rfl

variable (K : Type) [CommRing K] (D : ℕ)

def individualCoordinatesAt (j n : ℤ) (k : ℕ) (hk : j - (k : ℤ) = n) :
    (Toric.model K D j).X n ≃ₗ[Laurent K D] (GradeMask D j n → Laurent K D) :=
  ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) hk).toLinearEquiv.trans
    ((maskTermCoordinates (Laurent K D) D k).trans
      (LinearEquiv.piCongrLeft' (Laurent K D) (fun _ => Laurent K D) (gradeMaskEquiv D j n k hk)))

def individualCoordinates (j n : ℤ) :
    (Toric.model K D j).X n ≃ₗ[Laurent K D] (GradeMask D j n → Laurent K D) := by
  classical
  by_cases hn : n ≤ j
  · exact individualCoordinatesAt K D j n (j - n).toNat (by omega)
  · let : Subsingleton ((Toric.model K D j).X n) :=
      ModuleCat.subsingleton_of_isZero ((Toric.model K D j).isZero_of_isStrictlyLE j n (by omega))
    let : IsEmpty (GradeMask D j n) := ⟨fun a => by have := a.property; omega⟩
    exact LinearEquiv.ofSubsingleton _ _

theorem individualCoordinates_eq_at (j n : ℤ) (k : ℕ) (hk : j - (k : ℤ) = n) :
    individualCoordinates K D j n = individualCoordinatesAt K D j n k hk := by
  unfold individualCoordinates
  rw [dite_eq_left (by omega : n ≤ j)]
  have he : k = (j - n).toNat := by omega
  subst k
  rfl

theorem individualCoordinatesAt_apply (j n : ℤ) (k : ℕ) (hk : j - (k : ℤ) = n)
    (x : (Toric.model K D j).X n) (a : GradeMask D j n) :
    individualCoordinatesAt K D j n k hk x a =
      (show Term (Laurent K D) D k from
        ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) hk).hom x)
        (cellOfSet (subsetAt D a.val) (by have := a.property; omega)) := by
  change maskTermCoordinates (Laurent K D) D k
    (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) hk).hom x)
    ⟨a.val, by have := a.property; omega⟩ = _
  exact maskTermCoordinates_apply _ _ _ _ _

end
end Decoupling.HighDim.AlgorithmTwoToricData
