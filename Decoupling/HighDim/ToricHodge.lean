import Decoupling.HighDim.ToricHodgeCells
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Signed perfect pairing on complementary toric cells

The pairing is an explicit signed permutation of the actual cell basis,
followed by the genuine finite-free dual-basis equivalence.
-/

namespace Decoupling.HighDim.Toric.Hodge

open Koszul

noncomputable section
attribute [local instance] Classical.propDecidable
variable (A : Type*) [CommRing A] {D k l : ℕ}

def orientationUnit (I : Cell D k) : Aˣ :=
  ⟨orientation A I, orientation A I, orientation_sq A I, orientation_sq A I⟩

def signedCoordinates : Term A D k ≃ₗ[A] (Cell D k → A) :=
  (Finsupp.linearEquivFunOnFinite A A (Cell D k)).trans
    (LinearEquiv.piCongrRight (fun I => LinearEquiv.smulOfUnit (orientationUnit A I)))

@[simp] theorem signedCoordinates_apply (x : Term A D k) (I : Cell D k) :
    signedCoordinates A x I = orientation A I * x I := rfl

def duality (h : k + l = D) : Term A D k ≃ₗ[A] Module.Dual A (Term A D l) :=
  (signedCoordinates A).trans
    ((LinearEquiv.piCongrLeft' A (fun _ : Cell D k => A) (complementEquiv h)).trans
      (Finsupp.basisSingleOne.constr A))

theorem duality_apply_complement_single (h : k + l = D) (x : Term A D k)
    (I : Cell D k) (a : A) :
    duality A h x (Finsupp.single (complement h I) a) =
      a * orientation A I * x I := by
  simp [duality, LinearEquiv.piCongrLeft', signedCoordinates, orientationUnit,
    complementEquiv, complement_involutive, mul_assoc, Finsupp.single_apply, LinearEquiv.smulOfUnit]

theorem duality_single_single (h : k + l = D) (I : Cell D k) (J : Cell D l) :
    duality A h (Finsupp.single I 1) (Finsupp.single J 1) =
      if complement h I = J then orientation A I else 0 := by
  classical
  obtain ⟨I', rfl⟩ := (complementEquiv h).surjective J
  change duality A h (Finsupp.single I 1) (Finsupp.single (complement h I') 1) = _
  rw [duality_apply_complement_single]
  by_cases hI : I = I'
  · subst I'
    simp [complementEquiv]
  · have hc : complement h I ≠ complement h I' := (complementEquiv h).injective.ne hI
    simp [hI, hc, complementEquiv]

end
end Decoupling.HighDim.Toric.Hodge
