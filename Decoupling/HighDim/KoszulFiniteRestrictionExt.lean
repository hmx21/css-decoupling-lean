import Decoupling.HighDim.KoszulRestrictionExt

/-!
# Finite coefficient sums and native Ext restriction

The argument decomposes the actual identity map using the finite coordinate
inclusions and projections. Only the source has to be a finite coefficient
sum; the target may be any augmentation-annihilated module.
-/

namespace Decoupling.HighDim.Koszul

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Preadditive
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [CommRing K] [IsDomain K] (D p : ℕ)
  [Fact p.Prime] [CharP K p]

/-- Native Ext restriction vanishes on a finite sum of coefficient sources,
expressed by its actual coordinate inclusions and projections. -/
theorem finite_source_ext_restriction_eq_zero
    {ι : Type} [Fintype ι] (A B : ModuleCat (Laurent K D))
    (inc : ι → (coefficientModule K D ⟶ A))
    (pr : ι → (A ⟶ coefficientModule K D))
    (htotal : ∑ i, pr i ≫ inc i = 𝟙 A)
    (hB : ∀ i : Fin D, ∀ b : B, difference K i • b = 0)
    (n : ℕ) (e : Ext A B (n + 1)) :
    e.mapExactFunctor (ModuleCat.restrictScalars (scaling K D p)) = 0 := by
  let F := ModuleCat.restrictScalars (scaling K D p)
  have hi (i : ι) :
      ((Ext.mk₀ (inc i)).comp e (zero_add (n + 1))).mapExactFunctor F = 0 :=
    coefficient_ext_restriction_eq_zero K D p B hB n _
  have hrep : e = ∑ i, (Ext.mk₀ (pr i)).comp
      ((Ext.mk₀ (inc i)).comp e (zero_add (n + 1))) (zero_add (n + 1)) := by
    simp only [Ext.mk₀_comp_mk₀_assoc, ← Ext.sum_comp, ← Ext.mk₀_sum, htotal,
      Ext.mk₀_id_comp]
  rw [hrep]
  change F.mapExtAddHom A B (n + 1) _ = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change ((Ext.mk₀ (pr i)).comp ((Ext.mk₀ (inc i)).comp e
    (zero_add (n + 1))) (zero_add (n + 1))).mapExactFunctor F = 0
  rw [Ext.mapExactFunctor_comp, hi, Ext.comp_zero]

end
end Decoupling.HighDim.Koszul
