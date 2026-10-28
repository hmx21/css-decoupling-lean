import Decoupling.HighDim.TorusComplexDual

/-!
# Duality on genuine homotopy-category morphisms

The maps here descend the actual transpose of cochain maps through actual
chain homotopies. In particular, this is not a replacement of the derived
or homotopy categories by a matrix-counting model.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits HomologicalComplex
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

variable (R : Type) [CommRing R]

abbrev homotopyQuotient := HomotopyCategory.quotient (ModuleCat R) (.up ℤ)

/-- Transposition descended to actual homotopy classes. -/
def homotopyDualMap {C E : CochainComplex (ModuleCat R) ℤ}
    (f : (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) :
    (homotopyQuotient R).obj (complexDual R E) ⟶
      (homotopyQuotient R).obj (complexDual R C) :=
  Quot.lift (fun g => (homotopyQuotient R).map (complexDualMap R g))
    (fun f g h => HomotopyCategory.eq_of_homotopy _ _
      (complexDualHomotopy R (HomotopyCategory.homotopyOfEq f g (Quot.sound h)))) f

@[simp] theorem homotopyDualMap_quotient {C E : CochainComplex (ModuleCat R) ℤ}
    (f : C ⟶ E) :
    homotopyDualMap R ((homotopyQuotient R).map f) =
      (homotopyQuotient R).map (complexDualMap R f) := rfl

@[simp] theorem homotopyDualMap_add {C E : CochainComplex (ModuleCat R) ℤ}
    (f g : (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) :
    homotopyDualMap R (f + g) = homotopyDualMap R f + homotopyDualMap R g := by
  obtain ⟨f, rfl⟩ := (homotopyQuotient R).map_surjective f
  obtain ⟨g, rfl⟩ := (homotopyQuotient R).map_surjective g
  rw [← Functor.map_add, homotopyDualMap_quotient, complexDualMap_add, Functor.map_add]
  rfl

@[simp] theorem homotopyDualMap_smul {C E : CochainComplex (ModuleCat R) ℤ}
    (r : R) (f : (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) :
    homotopyDualMap R (r • f) = r • homotopyDualMap R f := by
  obtain ⟨f, rfl⟩ := (homotopyQuotient R).map_surjective f
  rw [← Functor.map_smul, homotopyDualMap_quotient, complexDualMap_smul, Functor.map_smul]
  rfl

variable {R}

/-- Inverse transposition on homotopy classes. -/
def homotopyUndualMap {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.IsReflexive R (E.X n)]
    (g : (homotopyQuotient R).obj (complexDual R E) ⟶
      (homotopyQuotient R).obj (complexDual R C)) :
    (homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E :=
  (homotopyQuotient R).map (complexEvaluation C) ≫ homotopyDualMap R g ≫
    (homotopyQuotient R).map (complexDoubleDualIso E).inv

@[simp] theorem homotopyUndualMap_quotient {C E : CochainComplex (ModuleCat R) ℤ}
    [∀ n, Module.IsReflexive R (E.X n)]
    (g : complexDual R E ⟶ complexDual R C) :
    homotopyUndualMap ((homotopyQuotient R).map g) =
      (homotopyQuotient R).map (complexUndualMap g) := by
  simp [homotopyUndualMap, complexUndualMap]

/-- Reflexive targets give a natural linear equivalence on genuine
homotopy-category morphisms. -/
def homotopyDualHomEquiv (C E : CochainComplex (ModuleCat R) ℤ)
    [∀ n, Module.IsReflexive R (E.X n)] :
    ((homotopyQuotient R).obj C ⟶ (homotopyQuotient R).obj E) ≃ₗ[R]
      ((homotopyQuotient R).obj (complexDual R E) ⟶
        (homotopyQuotient R).obj (complexDual R C)) where
  toFun := homotopyDualMap R
  invFun := homotopyUndualMap
  left_inv f := by
    obtain ⟨f, rfl⟩ := (homotopyQuotient R).map_surjective f
    simp
  right_inv g := by
    obtain ⟨g, rfl⟩ := (homotopyQuotient R).map_surjective g
    simp
  map_add' := homotopyDualMap_add R
  map_smul' := homotopyDualMap_smul R

end
end Decoupling.HighDim.Torus
