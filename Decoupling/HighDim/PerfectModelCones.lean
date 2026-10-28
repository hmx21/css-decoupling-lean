import Decoupling.HighDim.PerfectModelBasic

/-!
# Actual cone models and closure under distinguished extensions

The middle model is constructed by lifting the actual inverse-rotated
connecting map to cochains and taking its actual mapping cone. The
resulting derived identification comes from the distinguished triangles.
-/
namespace Decoupling.HighDim.PerfectModel
open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open HomologicalComplex Torus
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D : ℕ} {X Y : Derived K D}

/-- Literal degreewise coordinates of the mapping cone. -/
def coneTermIso (M : TensorModel X) (N : TensorModel Y) (f : M.complex ⟶ N.complex) (n : ℤ) :
    (CochainComplex.mappingCone f).X n ≅
      ModuleCat.of (Laurent K D) (M.complex.X (n + 1) × N.complex.X n) :=
  homotopyCofiber.XIsoBiprod f n (n + 1) rfl ≪≫ ModuleCat.biprodIsoProd _ _

def cone (M : TensorModel X) (N : TensorModel Y) (f : M.complex ⟶ N.complex) :
    TensorModel (DerivedCategory.Q.obj (CochainComplex.mappingCone f)) where
  complex := CochainComplex.mappingCone f
  lower := min (M.lower - 1) N.lower
  upper := max (M.upper - 1) N.upper
  finite n := Module.Finite.equiv (coneTermIso M N f n).symm.toLinearEquiv
  free n := Module.Free.of_equiv (coneTermIso M N f n).symm.toLinearEquiv
  boundedBelow := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro n hn
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨M.complex.isZero_of_isStrictlyGE M.lower (n + 1) (by omega),
      N.complex.isZero_of_isStrictlyGE N.lower n (by omega)⟩
  boundedAbove := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    rw [CochainComplex.mappingCone.isZero_X_iff]
    exact ⟨M.complex.isZero_of_isStrictlyLE M.upper (n + 1) (by omega),
      N.complex.isZero_of_isStrictlyLE N.upper n (by omega)⟩
  iso := Iso.refl _

/-- A distinguished extension of objects with actual bounded free models
has such a model, without a supplied cone presentation or cochain lift. -/
def middle (T : Triangle (Derived K D)) (hT : T ∈ distTriang _)
    (M : TensorModel T.obj₁) (N : TensorModel T.obj₃) : TensorModel T.obj₂ := by
  let Ns := shift N (-1)
  let f := Ns.lift M T.invRotate.mor₁
  let CT := DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle f)
  let e : CT ≅ T.invRotate := isoTriangleOfIso₁₂ CT T.invRotate
    (DerivedCategory.mappingCone_triangle_distinguished f) (inv_rot_of_distTriang T hT)
    Ns.iso M.iso (by
      change DerivedCategory.Q.map f ≫ M.iso.hom = Ns.iso.hom ≫ T.invRotate.mor₁
      rw [TensorModel.lift_spec]
      simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id])
  exact ofIso (cone Ns M f) (Triangle.π₃.mapIso e)

end
end Decoupling.HighDim.PerfectModel
