import Decoupling.HighDim.TorusHomology
import Decoupling.HighDim.Ext
import Mathlib.CategoryTheory.Triangulated.Pretriangulated
import Mathlib.Algebra.Homology.DerivedCategory.Linear
import Mathlib.RingTheory.Finiteness.Finsupp

/-!
# Actual representable long exact sequences and their dimension losses

Source: Appendix B.3. These are native derived-category morphism spaces,
with the coefficient-field action obtained by scalar restriction. Exactness
is a theorem of distinguished triangles; it is not supplied as an input.
The torus comparison will use the augmentation module in degree `D` as
`P`, invoking Laurent Koszul self-duality.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Preadditive CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}
abbrev Derived (K : Type) [Field K] (D : ℕ) := DerivedCategory (ModuleCat (Laurent K D))

/-- Genuine representable morphism space, retaining the coefficient-field
linear structure. -/
def homCoefficients (P X : Derived K D) : ModuleCat K :=
  Layers.coefficients (ModuleCat.of (Laurent K D) (P ⟶ X))

/-- Postcomposition, over the coefficient field. -/
def postcompose (P : Derived K D) {X Y : Derived K D} (f : X ⟶ Y) :
    homCoefficients P X ⟶ homCoefficients P Y :=
  ModuleCat.ofHom (X := homCoefficients P X) (Y := homCoefficients P Y) {
  toFun g := (show P ⟶ X from g) ≫ f
  map_add' _ _ := Preadditive.add_comp _ _ _ _ _ _
  map_smul' a g := by
    change ((constant (D := D) a) • (show P ⟶ X from g)) ≫ f =
      (constant (D := D) a) • ((show P ⟶ X from g) ≫ f)
    simp }

/-- The first exactness statement of the actual representable long exact
sequence associated to a distinguished triangle. -/
theorem postcompose_exact (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _) :
    Function.Exact (postcompose P T.mor₁) (postcompose P T.mor₂) := by
  intro g
  change (show P ⟶ T.obj₂ from g) ≫ T.mor₂ = 0 ↔
    ∃ f : P ⟶ T.obj₁, f ≫ T.mor₁ = g
  constructor
  · intro hg
    obtain ⟨f, hf⟩ := T.coyoneda_exact₂ hT g hg
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, rfl⟩
    rw [Category.assoc, comp_distTriang_mor_zero₁₂ T hT, comp_zero]

/-- The next exactness statement includes the actual connecting map. -/
theorem postcompose_connecting_exact (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _) :
    Function.Exact (postcompose P T.mor₂) (postcompose P T.mor₃) := by
  intro g
  change (show P ⟶ T.obj₃ from g) ≫ T.mor₃ = 0 ↔
    ∃ f : P ⟶ T.obj₂, f ≫ T.mor₂ = g
  constructor
  · intro hg
    obtain ⟨f, hf⟩ := T.coyoneda_exact₃ hT g hg
    exact ⟨f, hf.symm⟩
  · rintro ⟨f, rfl⟩
    rw [Category.assoc, comp_distTriang_mor_zero₂₃ T hT, comp_zero]

/-- Finite-dimensional ends imply a finite-dimensional middle, so no
finite-dimensionality of the derived morphism space is assumed silently. -/
theorem homCoefficients_finite_middle (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _)
    [Module.Finite K (homCoefficients P T.obj₁)]
    [Module.Finite K (homCoefficients P T.obj₃)] :
    Module.Finite K (homCoefficients P T.obj₂) := by
  let f := (postcompose P T.mor₁).hom
  let g := (postcompose P T.mor₂).hom
  apply Module.Finite.of_exact (f := f) (g := g.rangeRestrict) ?_
    (LinearMap.surjective_rangeRestrict g)
  intro x
  change g.rangeRestrict x = 0 ↔ ∃ y, f y = x
  rw [Subtype.ext_iff]
  exact postcompose_exact P T hT x

/-- Distinguished triangles give the bound used at every Postnikov stage. -/
theorem triangle_finrank_le (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _)
    [Module.Finite K (homCoefficients P T.obj₁)]
    [Module.Finite K (homCoefficients P T.obj₃)] :
    Module.finrank K (homCoefficients P T.obj₂) ≤
      Module.finrank K (homCoefficients P T.obj₁) +
        Module.finrank K (homCoefficients P T.obj₃) := by
  let := homCoefficients_finite_middle P T hT
  exact finrank_exact_middle_le _ _ (postcompose_exact P T hT)

/-- A detected nonzero gluing map gives strict loss in that same native
long exact sequence. Detection itself is a separate Koszul theorem. -/
theorem triangle_finrank_lt (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _)
    [Module.Finite K (homCoefficients P T.obj₁)]
    [Module.Finite K (homCoefficients P T.obj₃)]
    (hδ : postcompose P T.mor₃ ≠ 0) :
    Module.finrank K (homCoefficients P T.obj₂) <
      Module.finrank K (homCoefficients P T.obj₁) +
        Module.finrank K (homCoefficients P T.obj₃) := by
  let := homCoefficients_finite_middle P T hT
  exact finrank_exact_middle_lt _ _ _
    (postcompose_exact P T hT) (postcompose_connecting_exact P T hT) hδ

/-- An actual derived isomorphism gives a coefficient-linear isomorphism
of represented morphisms. -/
def homCoefficientsIso (P : Derived K D) {X Y : Derived K D} (e : X ≅ Y) :
    homCoefficients P X ≅ homCoefficients P Y where
  hom := postcompose P e.hom
  inv := postcompose P e.inv
  hom_inv_id := by
    ext f
    change ((show P ⟶ X from f) ≫ e.hom) ≫ e.inv = f
    simp
  inv_hom_id := by
    ext f
    change ((show P ⟶ Y from f) ≫ e.inv) ≫ e.hom = f
    simp

end
end Decoupling.HighDim.Torus
