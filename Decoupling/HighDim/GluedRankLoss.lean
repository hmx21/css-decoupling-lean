import Decoupling.HighDim.TorusTriangle

/-!
# Both actual rank losses in the example's long exact sequence

This is ordinary finite-dimensional linear algebra applied to a genuine
distinguished triangle. It retains the incoming as well as the outgoing
connecting morphism, which is needed for the exact six-versus-four count.
-/

namespace Decoupling.HighDim.GluedRankLoss

open CategoryTheory CategoryTheory.Pretriangulated Torus
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K]

theorem fiveTerm_dimension {A B C E F : ModuleCat K}
    [Module.Finite K B] [Module.Finite K C] [Module.Finite K E]
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ E) (d : E ⟶ F)
    (hab : Function.Exact a b) (hbc : Function.Exact b c) (hcd : Function.Exact c d) :
    Module.finrank K C + Module.finrank K a.hom.range + Module.finrank K d.hom.range =
      Module.finrank K B + Module.finrank K E := by
  have hB := finrank_of_exact a b hab
  have hC := finrank_of_exact b c hbc
  have hE := finrank_of_exact c d hcd
  omega

theorem rank_eq_one_of_domain {A B : ModuleCat K} [Module.Finite K A]
    (f : A ⟶ B) (hf : f ≠ 0) (hA : Module.finrank K A = 1) :
    Module.finrank K f.hom.range = 1 := by
  have hle := LinearMap.finrank_range_le f.hom
  have hne : Module.finrank K f.hom.range ≠ 0 := by
    intro h
    exact hf (ModuleCat.hom_ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)))
  omega

theorem rank_eq_one_of_codomain {A B : ModuleCat K} [Module.Finite K B]
    (f : A ⟶ B) (hf : f ≠ 0) (hB : Module.finrank K B = 1) :
    Module.finrank K f.hom.range = 1 := by
  have hle := f.hom.range.finrank_le
  have hne : Module.finrank K f.hom.range ≠ 0 := by
    intro h
    exact hf (ModuleCat.hom_ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)))
  omega

variable {K : Type} [Field K] {D : ℕ}

@[simp] theorem postcompose_zero (P X Y : Derived K D) :
    postcompose P (0 : X ⟶ Y) = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro f
  change (show P ⟶ X from f) ≫ 0 = 0
  simp

theorem triangle_dimension (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _)
    [Module.Finite K (homCoefficients P T.obj₁)]
    [Module.Finite K (homCoefficients P T.obj₃)] :
    Module.finrank K (homCoefficients P T.obj₂) +
      Module.finrank K (postcompose P T.invRotate.mor₁).hom.range +
      Module.finrank K (postcompose P T.mor₃).hom.range =
        Module.finrank K (homCoefficients P T.obj₁) +
          Module.finrank K (homCoefficients P T.obj₃) := by
  let := homCoefficients_finite_middle P T hT
  exact fiveTerm_dimension (B := homCoefficients P T.obj₁)
    (C := homCoefficients P T.obj₂) (E := homCoefficients P T.obj₃)
    (postcompose P T.invRotate.mor₁) (postcompose P T.mor₁)
    (postcompose P T.mor₂) (postcompose P T.mor₃)
    (postcompose_exact P T.invRotate (inv_rot_of_distTriang T hT))
    (postcompose_exact P T hT) (postcompose_connecting_exact P T hT)

/-- If the source object is the probe itself up to a proved isomorphism,
no nonzero map can disappear under this representable functor. -/
theorem postcompose_nonzero_of_sourceIso (P : Derived K D) {X Y : Derived K D}
    (e : P ≅ X) (f : X ⟶ Y) (hf : f ≠ 0) : postcompose P f ≠ 0 := by
  intro h
  have he := congrArg (fun g : homCoefficients P X ⟶ homCoefficients P Y =>
    g (show homCoefficients P X from e.hom)) h
  change e.hom ≫ f = 0 at he
  exact hf ((cancel_epi e.hom).mp (by simpa using he))

/-- The two rank-one boundary maps remove exactly two of the six modes. -/
theorem triangle_count_four (P : Derived K D) (T : Triangle (Derived K D))
    (hT : T ∈ distTriang _)
    [Module.Finite K (homCoefficients P T.obj₁)]
    [Module.Finite K (homCoefficients P T.obj₃)]
    (hleft : Module.finrank K (homCoefficients P T.obj₁) = 3)
    (hright : Module.finrank K (homCoefficients P T.obj₃) = 3)
    (hin : Module.finrank K (postcompose P T.invRotate.mor₁).hom.range = 1)
    (hout : Module.finrank K (postcompose P T.mor₃).hom.range = 1) :
    Module.finrank K (homCoefficients P T.obj₂) = 4 := by
  have h := triangle_dimension P T hT
  omega

end
end Decoupling.HighDim.GluedRankLoss
