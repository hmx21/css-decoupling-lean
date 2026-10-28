import Decoupling.HighDim.FiniteResolutionProfile
import Decoupling.HighDim.CochainCokernelDerived

/-!
# Native profile isomorphisms imply stable CSS check-cokernel isomorphisms

This is the algebraic C1--C2 bridge. The finite free models, comparison
homotopies, and finite-projective-freeness are all constructed or proved;
the sole additional premise of the comparison theorem is the actual
derived profile isomorphism that Theorem 1 will supply.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory Matrix

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D q s r : ℕ}

theorem cssComplex_range_coordinates (c : CSS.Checks K D q s r) (hc : c.Topological) :
    (LinearMap.range ((cssComplex c hc).d 0 1).hom).map
        (cssDualOneCoordinates c).toLinearMap = LinearMap.range c.H_X.mulVecLin := by
  ext x
  constructor
  · rintro ⟨_, ⟨y, rfl⟩, rfl⟩
    exact ⟨cssDualZeroCoordinates c y, (cssDual_d_zero_one c y).symm⟩
  · rintro ⟨y, rfl⟩
    refine ⟨(cssDual c).d 0 1 ((cssDualZeroCoordinates c).symm y),
      ⟨(cssDualZeroCoordinates c).symm y, rfl⟩, ?_⟩
    simp only [LinearEquiv.coe_coe, cssDual_d_zero_one, LinearEquiv.apply_symm_apply]
    rfl

/-- The constructed model has the actual original CSS check cokernel. -/
def cssComplex_checkCokernelEquiv (c : CSS.Checks K D q s r) (hc : c.Topological) :
    CochainCokernel.CheckCokernel (cssComplex c hc) ≃ₗ[Laurent K D] c.CheckCokernel :=
  Submodule.Quotient.equiv _ _ (cssDualOneCoordinates c) (cssComplex_range_coordinates c hc)

/-- The full algebraic comparison for two topological CSS codes. Neither
resolution data nor homotopies nor stable-isomorphism certificates are inputs. -/
theorem exists_stableCheckEquiv_of_profileIso
    (c : CSS.Checks K D q s r) (hc : c.Topological)
    {q' s' r' : ℕ} (d : CSS.Checks K D q' s' r') (hd : d.Topological)
    (e : Profile.S_X c ≅ Profile.S_X d) :
    ∃ a b : ℕ, Nonempty
      ((d.CheckCokernel × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (c.CheckCokernel × (Fin a → Laurent K D))) := by
  obtain ⟨a, b, ⟨f⟩⟩ := CochainCokernel.exists_stableEquiv_of_derivedIso
    (D + 2) (D + 2) (cssComplex_profileIso c hc ≪≫ e ≪≫ (cssComplex_profileIso d hd).symm)
  exact ⟨a, b, ⟨((cssComplex_checkCokernelEquiv d hd).symm.prodCongr
    (LinearEquiv.refl _ _)).trans (f.trans
      ((cssComplex_checkCokernelEquiv c hc).prodCongr (LinearEquiv.refl _ _)))⟩⟩

end
end Decoupling.HighDim.FiniteResolution
