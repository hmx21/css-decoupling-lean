import Decoupling.HighDim.ToricWindow
import Decoupling.HighDim.CochainCokernel

/-!
# Coordinates of the actual toric model's three physical terms

The following equivalences connect the integer cochain model to the
actual CSS matrices, and therefore identify its actual check cokernel.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory Matrix

noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [CommRing K] (D k : ℕ)

def zeroCoordinates : (model K D (k + 1)).X 0 ≃ₗ[Laurent K D]
    CSS.Free K D (cellCount D (k + 1)) :=
  ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (k + 1))
    (i := k + 1) (i' := 0) (by simp)).toLinearEquiv.trans (cellCoordinates K D (k + 1))

def oneCoordinates : (model K D (k + 1)).X 1 ≃ₗ[Laurent K D]
    CSS.Free K D (cellCount D k) :=
  ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (k + 1))
    (i := k) (i' := 1) (by simp)).toLinearEquiv.trans (cellCoordinates K D k)

def minusOneCoordinates : (model K D (k + 1)).X (-1) ≃ₗ[Laurent K D]
    CSS.Free K D (cellCount D (k + 2)) :=
  ((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (k + 1))
    (i := k + 2) (i' := -1) (by simp)).toLinearEquiv.trans (cellCoordinates K D (k + 2))

theorem d_zero_one_coordinates (x : (model K D (k + 1)).X 0) :
    oneCoordinates K D k ((model K D (k + 1)).d 0 1 x) =
      (checks K D k).H_X *ᵥ zeroCoordinates K D k x := by
  rw [checks_H_X, boundaryMatrix_apply]
  change cellCoordinates K D k
      (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (k + 1))
        (i := k) (i' := 1) (by simp)).hom ((model K D (k + 1)).d 0 1 x)) = _
  dsimp only [model]
  rw [(Koszul.laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE (k + 1))
    (i := k + 1) (j := k) (i' := 0) (j' := 1) (by simp) (by simp)]
  simp [zeroCoordinates, Koszul.laurentComplex]
  rfl

theorem d_minus_one_zero_coordinates (x : (model K D (k + 1)).X (-1)) :
    zeroCoordinates K D k ((model K D (k + 1)).d (-1) 0 x) =
      dagger (checks K D k).H_Z *ᵥ minusOneCoordinates K D k x := by
  rw [checks_dagger_H_Z, boundaryMatrix_apply]
  change cellCoordinates K D (k + 1)
      (((Koszul.laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE (k + 1))
        (i := k + 1) (i' := 0) (by simp)).hom ((model K D (k + 1)).d (-1) 0 x)) = _
  dsimp only [model]
  rw [(Koszul.laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE (k + 1))
    (i := k + 2) (j := k + 1) (i' := -1) (j' := 0) (by simp) (by simp)]
  simp [minusOneCoordinates, Koszul.laurentComplex]
  rfl

theorem range_coordinates :
    (LinearMap.range ((model K D (k + 1)).d 0 1).hom).map
        (oneCoordinates K D k).toLinearMap = LinearMap.range (checks K D k).H_X.mulVecLin := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨zeroCoordinates K D k y, (d_zero_one_coordinates K D k y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(model K D (k + 1)).d 0 1 ((zeroCoordinates K D k).symm y),
      ⟨(zeroCoordinates K D k).symm y, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, d_zero_one_coordinates, LinearEquiv.apply_symm_apply]
    rfl

def checkCokernelEquiv : CochainCokernel.CheckCokernel (model K D (k + 1)) ≃ₗ[Laurent K D]
    (checks K D k).CheckCokernel :=
  Submodule.Quotient.equiv _ _ (oneCoordinates K D k) (range_coordinates K D k)

end
end Decoupling.HighDim.Toric
