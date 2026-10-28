import Decoupling.HighDim.GluedNativeCone

/-!
# Explicit comparison to the native gluing cone

All maps below are maps of the actual cochain complexes; the map from
checks augments the first vertex component and keeps the second Koszul
component with the signs required by the native cone differential.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
noncomputable section
set_option backward.isDefEq.respectTransparency false

section Extend
variable {R : Type} [CommRing R]
variable (C : CochainComplex (ModuleCat R) ℕ) (Q : CochainComplex (ModuleCat R) ℤ)
  (φ : ∀ n : ℕ, C.X n ⟶ Q.X (n : ℤ))

open scoped Classical in
def extendNatComponent (i : ℤ) : (C.extend ComplexShape.embeddingUpNat).X i ⟶ Q.X i :=
  if hi : 0 ≤ i then
    (C.extendXIso ComplexShape.embeddingUpNat (Int.toNat_of_nonneg hi)).hom ≫
      φ i.toNat ≫ (Q.XIsoOfEq (Int.toNat_of_nonneg hi)).hom
  else 0

theorem extendNatComponent_eq (n : ℕ) :
    extendNatComponent C Q φ (n : ℤ) =
      (C.extendXIso ComplexShape.embeddingUpNat rfl).hom ≫ φ n := by
  simp [extendNatComponent]

/-- Extension by zero of an actual natural-number cochain map into an
integer complex. There is no outgoing boundary from the omitted part. -/
def extendNatMap
    (hφ : ∀ n : ℕ, φ n ≫ Q.d (n : ℤ) ((n + 1 : ℕ) : ℤ) =
      C.d n (n + 1) ≫ φ (n + 1)) : C.extend ComplexShape.embeddingUpNat ⟶ Q where
  f i := extendNatComponent C Q φ i
  comm' i j hij := by
    by_cases hi : ∃ n : ℕ, (n : ℤ) = i
    · obtain ⟨n, rfl⟩ := hi
      have hj : j = ((n + 1 : ℕ) : ℤ) := by change (n : ℤ) + 1 = j at hij; omega
      clear hij
      subst j
      rw [extendNatComponent_eq, extendNatComponent_eq]
      rw [C.extend_d_eq ComplexShape.embeddingUpNat (i := n) (j := n + 1)
        (i' := (n : ℤ)) (j' := ((n + 1 : ℕ) : ℤ)) rfl rfl]
      simp only [Category.assoc, Iso.inv_hom_id_assoc, hφ]
    · exact (C.isZero_extend_X ComplexShape.embeddingUpNat i
        (by simpa using hi)).eq_of_src _ _

end Extend

end
end Decoupling.HighDim.Glued
