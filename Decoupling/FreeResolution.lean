import Decoupling.ResolutionExt
import Mathlib.RingTheory.FiniteType
import Mathlib.GroupTheory.Finiteness
import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Concrete algebra for the free-resolution lemma

This file proves the actual reduced-module embedding and Noetherianity of
the Laurent ring. It keeps the separate global homological-dimension bound
and Laurent-projective freeness theorem explicit as inputs; neither is an
axiom or a replacement definition of projectivity or freeness.
-/

namespace Decoupling.FreeResolution

open Matrix CategoryTheory CategoryTheory.Abelian

noncomputable section

/-- The actual three-variable Laurent ring is Noetherian: its translation
monoid is finitely generated, hence its group algebra is finite type over
the Noetherian coefficient field. -/
instance laurentIsNoetherian : IsNoetherianRing R :=
  Algebra.FiniteType.isNoetherianRing (ZMod 2) R

variable {q s t : ℕ} (c : CSS.Checks q s t)

/-- The actual relation module in the supplied presentation. -/
abbrev RelationKernel := LinearMap.ker (dagger c.H_X).mulVecLin

/-- Finite generation of the relation kernel follows from the proved
Noetherianity, independently of any projective or free conclusion. -/
instance relationKernelFinite : Module.Finite R (RelationKernel c) := inferInstance

/-- Under the second topological condition, `[v] ↦ H_Z v` identifies the
actual reduced Pauli quotient with the column image of `H_Z`. -/
def reducedEquivRange (hc : c.Topological) :
    c.M_X ≃ₗ[R] LinearMap.range c.H_Z.mulVecLin :=
  (Submodule.quotEquivOfEq _ _ hc.2.symm).trans c.H_Z.mulVecLin.quotKerEquivRange

/-- The reduced Pauli module embeds into the actual Z-label free module. -/
def reducedEmbedding (hc : c.Topological) : c.M_X →ₗ[R] (Fin t → R) :=
  (LinearMap.range c.H_Z.mulVecLin).subtype.comp (reducedEquivRange c hc).toLinearMap

theorem reducedEmbedding_injective (hc : c.Topological) :
    Function.Injective (reducedEmbedding c hc) :=
  (LinearMap.range c.H_Z.mulVecLin).injective_subtype.comp (reducedEquivRange c hc).injective

@[simp] theorem reducedEmbedding_mk (hc : c.Topological) (a : Fin q → R) :
    reducedEmbedding c hc (Submodule.Quotient.mk a) = c.H_Z *ᵥ a := rfl

def embeddedSequence (hc : c.Topological) : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (reducedEmbedding c hc) (LinearMap.range c.H_Z.mulVecLin).mkQ (by
    apply LinearMap.ext
    intro a
    exact (Submodule.Quotient.mk_eq_zero _).mpr ((reducedEquivRange c hc) a).property)

theorem embeddedSequence_shortExact (hc : c.Topological) :
    (embeddedSequence c hc).ShortExact where
  exact := by
    apply ((embeddedSequence c hc).moduleCat_exact_iff).mpr
    intro a ha
    let a' : LinearMap.range c.H_Z.mulVecLin :=
      ⟨a, (Submodule.Quotient.mk_eq_zero _).mp ha⟩
    refine ⟨(reducedEquivRange c hc).symm a', ?_⟩
    exact congrArg Subtype.val ((reducedEquivRange c hc).apply_symm_apply a')
  mono_f := (ModuleCat.mono_iff_injective _).mpr (reducedEmbedding_injective c hc)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range c.H_Z.mulVecLin).mkQ_surjective

instance embeddedSequence_projective_middle (hc : c.Topological) :
    Projective (embeddedSequence c hc).X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R (Fin t))

/-- The reduced module has projective dimension at most two if the actual
cokernel of `H_Z` has projective dimension at most three. This is the first
dimension shift in Appendix A, with native projective-dimension classes. -/
theorem reduced_projectiveDimensionLE_two (hc : c.Topological)
    (hQ : HasProjectiveDimensionLE
      (ModuleCat.of R ((Fin t → R) ⧸ LinearMap.range c.H_Z.mulVecLin)) 3) :
    HasProjectiveDimensionLE (ModuleCat.of R c.M_X) 2 :=
  ((embeddedSequence_shortExact c hc).hasProjectiveDimensionLT_X₃_iff 2 inferInstance).mp hQ

/-- The canonical image-cover sequence in the supplied Pauli presentation. -/
def imageSequence : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk
    (LinearMap.range (dagger c.H_X).mulVecLin).subtype
    (LinearMap.range (dagger c.H_X).mulVecLin).mkQ (by
      apply LinearMap.ext
      intro a
      exact (Submodule.Quotient.mk_eq_zero _).mpr a.property)

theorem imageSequence_shortExact : (imageSequence c).ShortExact where
  exact := by
    apply ((imageSequence c).moduleCat_exact_iff).mpr
    intro a ha
    exact ⟨⟨a, (Submodule.Quotient.mk_eq_zero _).mp ha⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (LinearMap.range (dagger c.H_X).mulVecLin).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (LinearMap.range (dagger c.H_X).mulVecLin).mkQ_surjective

instance imageSequence_projective_middle : Projective (imageSequence c).X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R (Fin q))

/-- The kernel-cover sequence, retaining the actual kernel of `H_X†`. -/
def kernelSequence : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk (RelationKernel c).subtype
    (dagger c.H_X).mulVecLin.rangeRestrict (by
      apply LinearMap.ext
      intro a
      exact Subtype.ext a.property)

theorem kernelSequence_shortExact : (kernelSequence c).ShortExact where
  exact := by
    apply ((kernelSequence c).moduleCat_exact_iff).mpr
    intro a ha
    exact ⟨⟨a, congrArg Subtype.val ha⟩, rfl⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr (RelationKernel c).injective_subtype
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (dagger c.H_X).mulVecLin.surjective_rangeRestrict

instance kernelSequence_projective_middle : Projective (kernelSequence c).X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R (Fin s))

/-- Two further genuine dimension shifts make the actual relation kernel
projective. This conclusion is weaker than freeness and is not identified
with freeness by definition. -/
theorem relationKernel_projective
    (hM : HasProjectiveDimensionLE (ModuleCat.of R c.M_X) 2) :
    Module.Projective R (RelationKernel c) := by
  have hI : HasProjectiveDimensionLT (imageSequence c).X₁ 2 :=
    ((imageSequence_shortExact c).hasProjectiveDimensionLT_X₃_iff 1 inferInstance).mp hM
  have hK : HasProjectiveDimensionLT (kernelSequence c).X₁ 1 :=
    ((kernelSequence_shortExact c).hasProjectiveDimensionLT_X₃_iff 0 inferInstance).mp hI
  apply (IsProjective.iff_projective (RelationKernel c)).mpr
  exact projective_iff_hasProjectiveDimensionLT_one.mpr hK

/-- With an actual finite-free relation kernel, a basis produces the actual
matrix `Γ` and the supplied-resolution interface used by `ResolutionExt`.
No desired resolution identities are assumed: they follow from the kernel
subtype and its basis. -/
def resolutionOfFreeKernel [Module.Free R (RelationKernel c)] :
    ResolutionExt.CSSResolution c (Module.finrank R (RelationKernel c)) := by
  let b := Module.finBasis R (RelationKernel c)
  let g : (Fin (Module.finrank R (RelationKernel c)) → R) →ₗ[R] (Fin s → R) :=
    (RelationKernel c).subtype.comp b.equivFun.symm.toLinearMap
  let Γ := LinearMap.toMatrix' g
  have hΓ (a : Fin (Module.finrank R (RelationKernel c)) → R) :
      Γ *ᵥ a = (b.equivFun.symm a : Fin s → R) :=
    LinearMap.toMatrix'_mulVec g a
  refine { Γ := Γ, zero := ?_, exact₁ := ?_, injectiveΓ := ?_ }
  · apply Matrix.mulVec_injective
    funext a
    rw [← mulVec_mulVec, zero_mulVec, hΓ]
    exact (b.equivFun.symm a).property
  · intro a
    constructor
    · intro ha
      refine ⟨b.equivFun ⟨a, ha⟩, ?_⟩
      rw [hΓ]
      exact congrArg Subtype.val (b.equivFun.symm_apply_apply ⟨a, ha⟩)
    · rintro ⟨v, rfl⟩
      rw [hΓ]
      exact (b.equivFun.symm v).property
  · intro a a' haa'
    apply b.equivFun.symm.injective
    apply Subtype.ext
    simpa only [hΓ] using haa'

/-- Modular closure of Lemma I.1 from native global dimension and native
Laurent-projective freeness. `LaurentGlobalDimension` and `SwanInduction`
prove those inputs; `MainTheorem.exists_free_resolution` assembles them. -/
theorem exists_free_resolution_of_global_bound_and_freeness (hc : c.Topological)
    (hglobal : ∀ M : ModuleCat.{0} R, HasProjectiveDimensionLE M 3)
    (hfreeness : ∀ M : ModuleCat.{0} R, Module.Finite R M → Module.Projective R M →
      Module.Free R M) :
    ∃ cX : ℕ, Nonempty (ResolutionExt.CSSResolution c cX) := by
  have hM := reduced_projectiveDimensionLE_two c hc (hglobal _)
  let : Module.Projective R (RelationKernel c) := relationKernel_projective c hM
  let : Module.Free R (RelationKernel c) :=
    hfreeness (ModuleCat.of R (RelationKernel c)) inferInstance inferInstance
  exact ⟨Module.finrank R (RelationKernel c), ⟨resolutionOfFreeKernel c⟩⟩

end

end Decoupling.FreeResolution
