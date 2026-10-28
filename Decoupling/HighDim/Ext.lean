import Decoupling.HighDim.CSS
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The genuine conjugated reduced modules and Ext layers

Source: `drafts/main.tex` 452–506, Theorem 1 and Corollary 1.
Finite-dimensionality is over the coefficient field, not over the Laurent
ring. Only one whole sector must have finite layers. The high-degree vanishing
and the identification with a resolution's cohomology remain separate theorems.
-/

namespace Decoupling.HighDim.Layers

attribute [local instance] Classical.propDecidable

open CategoryTheory CategoryTheory.Abelian
noncomputable section

variable {K : Type} [CommRing K] {D q s r : ℕ}

def conjugate (M : ModuleCat (Laurent K D)) : ModuleCat (Laurent K D) :=
  (ModuleCat.restrictScalars bar.toRingHom).obj M

theorem conjugate_smul (M : ModuleCat (Laurent K D)) (a : Laurent K D) (m : conjugate M) :
    a • m = bar a • (show M from m) := rfl

def conjugationEquivalence : ModuleCat (Laurent K D) ≌ ModuleCat (Laurent K D) :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv bar

def reduced (c : CSS.Checks K D q s r) : ModuleCat (Laurent K D) :=
  ModuleCat.of (Laurent K D) c.M_X

abbrev E_X (c : CSS.Checks K D q s r) (j : ℕ) :=
  Ext (conjugate (reduced c)) (ModuleCat.of (Laurent K D) (Laurent K D)) j

abbrev E_Z (c : CSS.Checks K D q s r) (j : ℕ) := E_X c.swap j

def layer (c : CSS.Checks K D q s r) (j : ℕ) : ModuleCat (Laurent K D) :=
  ModuleCat.of (Laurent K D) (E_X c j)

def coefficients (M : ModuleCat (Laurent K D)) : ModuleCat K :=
  (ModuleCat.restrictScalars constant).obj M

def conjugateFreeEquiv (ι : Type) :
    conjugate (ModuleCat.of (Laurent K D) (ι → Laurent K D)) ≃ₗ[Laurent K D]
      (ι → Laurent K D) where
  toFun m i := bar (m i)
  invFun m i := bar (m i)
  left_inv m := by funext i; exact bar_bar _
  right_inv m := by funext i; exact bar_bar _
  map_add' m n := by funext i; exact bar_add _ _
  map_smul' a m := by
    funext i
    change bar (bar a * m i) = a * bar (m i)
    simp

end

noncomputable section
variable {p D q s r : ℕ} [Fact p.Prime]

/-- Precisely the positive layer hypothesis. The degree upper bound is proved
from topology elsewhere and is not built into the definition of Ext. -/
def FiniteXLayers (c : CSS.Checks (ZMod p) D q s r) : Prop :=
  ∀ j : ℕ, 1 ≤ j → j < D → FiniteDimensional (ZMod p) (coefficients (layer c j))

def FiniteZLayers (c : CSS.Checks (ZMod p) D q s r) : Prop := FiniteXLayers c.swap

def FiniteOneSector (c : CSS.Checks (ZMod p) D q s r) : Prop :=
  FiniteXLayers c ∨ FiniteZLayers c

def multiplicity (c : CSS.Checks (ZMod p) D q s r) (j : ℕ) : ℕ :=
  Module.finrank (ZMod p) (coefficients (layer c j))

/-- Counts nonzero layers, including the case where the set is empty. -/
def nonzeroLayerCount (c : CSS.Checks (ZMod p) D q s r) : ℕ :=
  ((Finset.range D).filter (fun j => 1 ≤ j ∧ Nontrivial (E_X c j))).card

omit [Fact p.Prime] in
theorem nonzeroLayerCount_le (c : CSS.Checks (ZMod p) D q s r) :
    nonzeroLayerCount c ≤ D :=
  (Finset.card_filter_le _ _).trans_eq (Finset.card_range D)

end
end Decoupling.HighDim.Layers
