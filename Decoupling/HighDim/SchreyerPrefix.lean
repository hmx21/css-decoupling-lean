import Decoupling.HighDim.SchreyerLocalizationData
import Decoupling.HighDim.FiniteResolutionPresentation

/-!
# HD014: retaining three prescribed finite free terms

This consumer takes a resolution of the actual kernel of `g : P₂ → P₁`
and retains `P₀`, `P₁`, `P₂`, `f`, and `g` literally. Its tail input is an
intermediate interface, to be discharged by Laurent Schreyer resolution.
Every term has supplied finite-power coordinates; no projective-freeness
or terminal-basis theorem occurs in the construction.
-/
namespace Decoupling.HighDim.SchreyerPrefix
open CategoryTheory CategoryTheory.Limits FiniteResolution SchreyerLocalization
noncomputable section
universe u
variable {R : Type u} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Prepending an actual cover preserves explicit finite-power coordinates. -/
def prepend {M P : ModuleCat.{u} R} {length rank : ℕ}
    (p : P ⟶ M) (hp : Function.Surjective p.hom)
    (e : P ≃ₗ[R] (Fin rank → R)) (A : FreeData (Syzygy p) length) :
    FreeData M (length + 1) := by
  letI : Module.Free R P := Module.Free.of_equiv e.symm
  letI : Module.Finite R P := Module.Finite.equiv e.symm
  exact {
    data := FiniteResolution.prepend p hp A.data
    rank := fun k => match k with | 0 => rank | k+1 => A.rank k
    coordinates := fun k => by cases k with | zero => exact e | succ k => exact A.coordinates k }

variable {P₀ P₁ P₂ : ModuleCat.{u} R}
    (f : P₁ ⟶ P₀) (g : P₂ ⟶ P₁)
    (hexact : LinearMap.range g.hom = LinearMap.ker f.hom)
    {length : ℕ} (A : FreeData (Syzygy g) length)

include hexact in
lemma comp_eq_zero : g ≫ f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  have hx : g.hom x ∈ LinearMap.ker f.hom := by
    rw [← hexact]
    exact ⟨x,rfl⟩
  exact hx

/-- The native augmented resolution with exactly the prescribed three terms. -/
def data [Projective P₀] [Module.Finite R P₀]
    [Projective P₁] [Module.Finite R P₁]
    [Projective P₂] [Module.Finite R P₂] : Data (Cokernel f) (length + 3) where
  X k := match k with | 0 => P₀ | 1 => P₁ | 2 => P₂ | k+3 => A.data.X k
  d k := match k with
    | 0 => f
    | 1 => g
    | 2 => A.data.ε ≫ ModuleCat.ofHom (LinearMap.ker g.hom).subtype
    | k+3 => A.data.d k
  sq k := by
    cases k with
    | zero => exact comp_eq_zero f g hexact
    | succ k => cases k with
      | zero =>
        apply ModuleCat.hom_ext
        apply LinearMap.ext
        intro x
        exact (A.data.ε x).property
      | succ k => cases k with
        | zero => simp only [← Category.assoc,A.data.d_ε,zero_comp]
        | succ k => exact A.data.sq k
  ε := quotient f
  d_ε := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨x,rfl⟩
  surjective := quotient_surjective f
  exact_zero := by
    change LinearMap.range f.hom = LinearMap.ker (LinearMap.range f.hom).mkQ
    exact (Submodule.ker_mkQ _).symm
  exact_succ k := by
    cases k with
    | zero => exact hexact
    | succ k => cases k with
      | zero =>
        ext x
        constructor
        · rintro ⟨y,rfl⟩
          exact (A.data.ε y).property
        · intro hx
          obtain ⟨y,hy⟩ := A.data.surjective ⟨x,hx⟩
          exact ⟨y,congrArg Subtype.val hy⟩
      | succ k => cases k with
        | zero =>
          rw [A.data.exact_zero]
          ext x
          change A.data.ε x=0 ↔ (A.data.ε x : P₂)=0
          exact ⟨fun h => congrArg Subtype.val h,fun h => Subtype.ext h⟩
        | succ k => exact A.data.exact_succ k
  projective k := by
    cases k with
    | zero => infer_instance
    | succ k => cases k with
      | zero => infer_instance
      | succ k => cases k with
        | zero => infer_instance
        | succ k => exact A.data.projective k
  finite k := by
    cases k with
    | zero => infer_instance
    | succ k => cases k with
      | zero => infer_instance
      | succ k => cases k with
        | zero => infer_instance
        | succ k => exact A.data.finite k
  zero_above k hk := by
    cases k with
    | zero => omega
    | succ k => cases k with
      | zero => omega
      | succ k => cases k with
        | zero => omega
        | succ k => exact A.data.zero_above k (by omega)

/-- Explicit finite-power coordinates throughout the prescribed prefix and tail. -/
def freeData {r₀ r₁ r₂ : ℕ}
    (e₀ : P₀ ≃ₗ[R] (Fin r₀ → R)) (e₁ : P₁ ≃ₗ[R] (Fin r₁ → R))
    (e₂ : P₂ ≃ₗ[R] (Fin r₂ → R)) : FreeData (Cokernel f) (length + 3) := by
  letI : Module.Free R P₀ := Module.Free.of_equiv e₀.symm
  letI : Module.Free R P₁ := Module.Free.of_equiv e₁.symm
  letI : Module.Free R P₂ := Module.Free.of_equiv e₂.symm
  letI : Module.Finite R P₀ := Module.Finite.equiv e₀.symm
  letI : Module.Finite R P₁ := Module.Finite.equiv e₁.symm
  letI : Module.Finite R P₂ := Module.Finite.equiv e₂.symm
  exact {
    data := data f g hexact A
    rank := fun k => match k with | 0 => r₀ | 1 => r₁ | 2 => r₂ | k+3 => A.rank k
    coordinates := fun k => by
      cases k with
      | zero => exact e₀
      | succ k => cases k with
        | zero => exact e₁
        | succ k => cases k with
          | zero => exact e₂
          | succ k => exact A.coordinates k }

end
end Decoupling.HighDim.SchreyerPrefix
