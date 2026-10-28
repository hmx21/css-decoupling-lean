import Decoupling.CSS
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic

/-!
# Actual reduced module and Ext layers

The input objects are the actual quotients from `CSS`, and the layers below
are mathlib's derived-category Ext groups. Conjugation is restriction of scalars
along the involution bar, so r acts on the conjugate module as bar(r).
This implements (3), (6), and (10); the cohomology formulas (8) are separate
proof obligations and are not used as definitions of the Ext layers.
-/

namespace Decoupling.ExtLayers

open CategoryTheory CategoryTheory.Abelian Matrix

noncomputable section

/-- The conjugate R-module, with scalar action r • m := bar(r) • m. -/
def conjugate (M : ModuleCat R) : ModuleCat R :=
  (ModuleCat.restrictScalars bar.toRingHom).obj M

theorem conjugate_smul (M : ModuleCat R) (r : R) (m : conjugate M) :
    r • m = bar r • (show M from m) := rfl

/-- Conjugation is an equivalence of module categories, not an identification of actions. -/
def conjugationEquivalence : ModuleCat R ≌ ModuleCat R :=
  ModuleCat.restrictScalarsEquivalenceOfRingEquiv bar

variable {q s r : ℕ}

/-- M_X = coker H_X†, bundled as an actual R-module. -/
def reduced (c : CSS.Checks q s r) : ModuleCat R :=
  ModuleCat.of R ((Fin q → R) ⧸ LinearMap.range (Matrix.mulVecLin (dagger c.H_X)))

/-- N = coker H_X, separately bundled to prevent confusing the two quotients. -/
def syndrome (c : CSS.Checks q s r) : ModuleCat R :=
  ModuleCat.of R ((Fin s → R) ⧸ LinearMap.range (Matrix.mulVecLin c.H_X))

/-- The manuscript's E_X^i = Ext_R^i(overline M_X,R). -/
abbrev E_X (c : CSS.Checks q s r) (i : ℕ) :=
  Ext (conjugate (reduced c)) (ModuleCat.of R R) i

/-- The canonical conjugated coordinate identification on a finite free module. -/
def conjugateFreeEquiv (ι : Type) :
    conjugate (ModuleCat.of R (ι → R)) ≃ₗ[R] (ι → R) where
  toFun m i := bar (m i)
  invFun m i := bar (m i)
  left_inv m := by funext i; exact bar_bar _
  right_inv m := by funext i; exact bar_bar _
  map_add' m n := by funext i; exact bar_add _ _
  map_smul' a m := by
    funext i
    change bar (bar a * m i) = a * bar (m i)
    simp

/-- Conjugating a matrix map conjugates every Laurent entry in the chosen bases. -/
theorem conjugate_matrix_apply {m n : Type} [Fintype n]
    (D : Matrix m n R) (v : conjugate (ModuleCat.of R (n → R))) :
    conjugateFreeEquiv m (D *ᵥ v) =
      D.map (bar : R → R) *ᵥ conjugateFreeEquiv n v := by
  funext i
  change bar (∑ j, D i j * v j) = ∑ j, bar (D i j) * bar (v j)
  simp only [map_sum, bar_mul]

/-- Transpose after conjugation is exactly the manuscript's dagger. -/
theorem conjugate_transpose {m n : Type} (D : Matrix m n R) :
    (D.map (bar : R → R)).transpose = dagger D := rfl

end
end Decoupling.ExtLayers
