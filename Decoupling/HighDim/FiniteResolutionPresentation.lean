import Decoupling.HighDim.FiniteResolutionLaurent

/-!
# Extending a prescribed finite presentation

For an actual map `f : P₁ → P₀` of finite projective Laurent modules we
construct a finite free resolution of its actual cokernel whose first two
terms and first differential are the supplied presentation. The extra
tail resolves the actual kernel. A conservative length bound `D + 2` is
used; the existence statement does not claim this is the shortest bound.
-/

namespace Decoupling.HighDim.FiniteResolution

open CategoryTheory CategoryTheory.Limits

universe u
noncomputable section

variable {R : Type u} [CommRing R] {P₁ P₀ : ModuleCat.{u} R} (f : P₁ ⟶ P₀)

/-- The presented module is the actual quotient by the range. -/
abbrev Cokernel := ModuleCat.of R (P₀ ⧸ LinearMap.range f.hom)

def quotient : P₀ ⟶ Cokernel f := ModuleCat.ofHom (LinearMap.range f.hom).mkQ

theorem quotient_surjective : Function.Surjective (quotient f).hom :=
  (LinearMap.range f.hom).mkQ_surjective

/-- The given relation map with codomain restricted to the actual kernel
of the quotient map. -/
def relations : P₁ ⟶ Syzygy (quotient f) :=
  ModuleCat.ofHom (f.hom.codRestrict (LinearMap.ker (quotient f).hom) (by
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x, rfl⟩))

theorem relations_surjective : Function.Surjective (relations f).hom := by
  intro x
  have hx : x.val ∈ LinearMap.range f.hom :=
    (Submodule.Quotient.mk_eq_zero _).mp x.property
  obtain ⟨y, hy⟩ := hx
  exact ⟨y, Subtype.ext hy⟩

section Laurent

variable {K : Type u} [Field K] {D : ℕ}
  {P₁ P₀ : ModuleCat.{u} (Laurent K D)} (f : P₁ ⟶ P₀)
  [Module.Finite (Laurent K D) P₀] [Projective P₀]
  [Module.Finite (Laurent K D) P₁] [Projective P₁]

/-- A finite free resolution extending exactly the supplied presentation. -/
def presentationData : Data (Cokernel f) (D + 2) :=
  prepend (quotient f) (quotient_surjective f)
    (prepend (relations f) (relations_surjective f) (laurent (Syzygy (relations f))))

@[simp] theorem presentation_X_zero : (presentationData f).X 0 = P₀ := rfl
@[simp] theorem presentation_X_one : (presentationData f).X 1 = P₁ := rfl

@[simp] theorem presentation_d_zero : (presentationData f).d 0 = f := by
  apply ModuleCat.hom_ext
  rfl

@[simp] theorem presentation_augmentation : (presentationData f).ε = quotient f := rfl

/-- This native projective resolution retains the original first matrix. -/
def presentationResolution : ProjectiveResolution (Cokernel f) :=
  (presentationData f).toProjectiveResolution

instance presentationResolution_finite (k : ℕ) :
    Module.Finite (Laurent K D) ((presentationResolution f).complex.X k) :=
  (presentationData f).finite k

instance presentationResolution_free (k : ℕ) :
    Module.Free (Laurent K D) ((presentationResolution f).complex.X k) :=
  (presentationData f).free k

theorem presentationResolution_zero_above (k : ℕ) (hk : D + 2 < k) :
    IsZero ((presentationResolution f).complex.X k) :=
  (presentationData f).zero_above k hk

@[simp] theorem presentationResolution_d_one_zero :
    (presentationResolution f).complex.d 1 0 = f := by
  exact (presentationData f).complex_d 0 |>.trans (presentation_d_zero f)

end Laurent

end

end Decoupling.HighDim.FiniteResolution
