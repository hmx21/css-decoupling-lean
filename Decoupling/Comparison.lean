import Decoupling.Stabilization
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Comparison maps from an augmentation isomorphism

This file proves the comparison-existence step in Proposition III.3 of
`notes/main.pdf`. Given exact augmented finite-free presentations and an
isomorphism `β : Nstd ≃ₗ[A] N`, it constructs comparison maps in the manuscript's
orientation `φ : G → F`, reverse maps `ρ : F → G`, and the two degree-zero
homotopies. The result is actual `Stabilization.ComparisonData`, so equation
(48) is a conclusion rather than an additional assumption.

The construction uses lifts through surjective linear maps. It is an existence
proof using classical choice; it does not provide a terminating Laurent-system
solver. Construction of the augmentation isomorphism `β` from the topological
and finite-Ext-layer assumptions is a separate obligation.
-/

namespace Decoupling.Comparison

open Matrix

section Lifting

variable {A : Type*} [CommRing A]
  {P M N : Type*}
  [AddCommGroup P] [Module A P] [Module.Projective A P]
  [AddCommGroup M] [Module A M]
  [AddCommGroup N] [Module A N]

/-- A map from a projective module lifts through another map if its image is
contained in that map's image. Finite-free source modules satisfy projectivity. -/
theorem exists_lift_of_range_le (f : M →ₗ[A] N) (g : P →ₗ[A] N)
    (h : LinearMap.range g ≤ LinearMap.range f) :
    ∃ l : P →ₗ[A] M, f.comp l = g := by
  let g' := g.codRestrict (LinearMap.range f) fun p => h ⟨p, rfl⟩
  obtain ⟨l, hl⟩ :=
    Module.projective_lifting_property f.rangeRestrict g' f.surjective_rangeRestrict
  refine ⟨l, ?_⟩
  ext p
  exact congrArg Subtype.val (DFunLike.congr_fun hl p)

/-- Exactness turns a cycle-valued map from a projective module into a lift. -/
theorem exists_lift_of_comp_eq_zero
    {Q : Type*} [AddCommGroup Q] [Module A Q]
    (d : M →ₗ[A] N) (ε : N →ₗ[A] Q) (g : P →ₗ[A] N)
    (hexact : LinearMap.range d = LinearMap.ker ε) (hzero : ε.comp g = 0) :
    ∃ l : P →ₗ[A] M, d.comp l = g := by
  apply exists_lift_of_range_le d g
  rw [hexact]
  rintro _ ⟨p, rfl⟩
  exact DFunLike.congr_fun hzero p

end Lifting

section Comparison

variable {A : Type*} [CommRing A] [CharP A 2]

/-- Every module over a ring of characteristic two has exponent two additively. -/
theorem module_add_self (M : Type*) [AddCommGroup M] [Module A M] (v : M) :
    v + v = 0 := by
  calc
    v + v = (1 : A) • v + (1 : A) • v := by simp
    _ = ((1 : A) + 1) • v := (add_smul _ _ _).symm
    _ = 0 := by rw [CharTwo.add_self_eq_zero, zero_smul]

variable {F₀ F₁ G₀ G₁ : Type*}
  [Fintype F₀] [Fintype F₁] [Fintype G₀] [Fintype G₁]
  [DecidableEq F₀] [DecidableEq F₁] [DecidableEq G₀] [DecidableEq G₁]
  {N Nstd : Type*}
  [AddCommGroup N] [Module A N]
  [AddCommGroup Nstd] [Module A Nstd]

/-- Proposition III.3 with a specified degree-zero lift, in a form directly
usable by the stable construction. In the manuscript this lift is `(T V')`.

The two hypotheses `exactF`, `exactG` give exactness at degree zero. Surjectivity
of `εG` is supplied; surjectivity of `εF` follows from the specified lift of `β`.
The four comparison equations are the fields of the resulting witness `c`.
The chosen `φ₀` is retained, and `ρ₀` lifts `β⁻¹`.
All finite index types may be empty.
-/
theorem exists_comparisonData_of_lift
    (d₁ : Matrix F₀ F₁ A) (td₁ : Matrix G₀ G₁ A)
    (εF : (F₀ → A) →ₗ[A] N) (εG : (G₀ → A) →ₗ[A] Nstd)
    (surjectiveG : Function.Surjective εG)
    (exactF : LinearMap.range d₁.mulVecLin = LinearMap.ker εF)
    (exactG : LinearMap.range td₁.mulVecLin = LinearMap.ker εG)
    (β : Nstd ≃ₗ[A] N)
    (φ₀ : (G₀ → A) →ₗ[A] (F₀ → A))
    (hφ₀ : εF.comp φ₀ = β.toLinearMap.comp εG) :
    ∃ c : Stabilization.ComparisonData A F₀ F₁ G₀ G₁,
      c.d₁ = d₁ ∧ c.td₁ = td₁ ∧
      c.φ₀ = LinearMap.toMatrix' φ₀ ∧
      εF.comp c.φ₀.mulVecLin = β.toLinearMap.comp εG ∧
      εG.comp c.ρ₀.mulVecLin = β.symm.toLinearMap.comp εF := by
  obtain ⟨ρ₀, hρ₀⟩ :=
    Module.projective_lifting_property εG (β.symm.toLinearMap.comp εF) surjectiveG
  have hφ (v : G₀ → A) : εF (φ₀ v) = β (εG v) := DFunLike.congr_fun hφ₀ v
  have hρ (v : F₀ → A) : εG (ρ₀ v) = β.symm (εF v) := DFunLike.congr_fun hρ₀ v
  have hdF (v : F₁ → A) : εF (d₁.mulVecLin v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactF]
    exact ⟨v, rfl⟩
  have hdG (v : G₁ → A) : εG (td₁.mulVecLin v) = 0 := by
    apply LinearMap.mem_ker.mp
    rw [← exactG]
    exact ⟨v, rfl⟩
  obtain ⟨φ₁, hφ₁⟩ :=
    exists_lift_of_comp_eq_zero d₁.mulVecLin εF (φ₀.comp td₁.mulVecLin) exactF
      (by ext v; simp only [LinearMap.comp_apply, hφ, hdG, map_zero,
        LinearMap.zero_apply])
  obtain ⟨ρ₁, hρ₁⟩ :=
    exists_lift_of_comp_eq_zero td₁.mulVecLin εG (ρ₀.comp d₁.mulVecLin) exactG
      (by ext v; simp only [LinearMap.comp_apply, hρ, hdF, map_zero,
        LinearMap.zero_apply])
  obtain ⟨η₀, hη₀⟩ :=
    exists_lift_of_comp_eq_zero d₁.mulVecLin εF (LinearMap.id + φ₀.comp ρ₀) exactF
      (by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
          map_add, hφ, hρ, β.apply_symm_apply, LinearMap.zero_apply]
        exact module_add_self (A := A) N _)
  obtain ⟨tη₀, htη₀⟩ :=
    exists_lift_of_comp_eq_zero td₁.mulVecLin εG (LinearMap.id + ρ₀.comp φ₀) exactG
      (by
        ext v
        simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.id_apply,
          map_add, hρ, hφ, β.symm_apply_apply, LinearMap.zero_apply]
        exact module_add_self (A := A) Nstd _)
  refine ⟨{
    d₁ := d₁
    td₁ := td₁
    φ₀ := LinearMap.toMatrix' φ₀
    ρ₀ := LinearMap.toMatrix' ρ₀
    φ₁ := LinearMap.toMatrix' φ₁
    ρ₁ := LinearMap.toMatrix' ρ₁
    η₀ := LinearMap.toMatrix' η₀
    tη₀ := LinearMap.toMatrix' tη₀
    forward := ?_
    backward := ?_
    homotopyF := ?_
    homotopyG := ?_
  }, rfl, rfl, rfl, ?_, ?_⟩
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply' d₁, Matrix.toLin'_apply' td₁]
      using hφ₁
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix',
      Matrix.toLin'_apply' d₁, Matrix.toLin'_apply' td₁]
      using hρ₁
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_add,
      Matrix.toLin'_one, Matrix.toLin'_apply' d₁] using hη₀
  · apply Matrix.toLin'.injective
    simpa only [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', map_add,
      Matrix.toLin'_one, Matrix.toLin'_apply' td₁] using htη₀
  · change εF.comp (Matrix.toLin' (LinearMap.toMatrix' φ₀)) = _
    simpa only [Matrix.toLin'_toMatrix'] using hφ₀
  · change εG.comp (Matrix.toLin' (LinearMap.toMatrix' ρ₀)) = _
    simpa only [Matrix.toLin'_toMatrix'] using hρ₀

/-- Every augmentation isomorphism between the two exact finite-free
presentations admits comparison maps and both degree-zero homotopies.
This version also constructs the initial degree-zero lift `φ₀`. -/
theorem exists_comparisonData
    (d₁ : Matrix F₀ F₁ A) (td₁ : Matrix G₀ G₁ A)
    (εF : (F₀ → A) →ₗ[A] N) (εG : (G₀ → A) →ₗ[A] Nstd)
    (surjectiveF : Function.Surjective εF) (surjectiveG : Function.Surjective εG)
    (exactF : LinearMap.range d₁.mulVecLin = LinearMap.ker εF)
    (exactG : LinearMap.range td₁.mulVecLin = LinearMap.ker εG)
    (β : Nstd ≃ₗ[A] N) :
    ∃ c : Stabilization.ComparisonData A F₀ F₁ G₀ G₁,
      c.d₁ = d₁ ∧ c.td₁ = td₁ ∧
      εF.comp c.φ₀.mulVecLin = β.toLinearMap.comp εG ∧
      εG.comp c.ρ₀.mulVecLin = β.symm.toLinearMap.comp εF := by
  obtain ⟨φ₀, hφ₀⟩ :=
    Module.projective_lifting_property εF (β.toLinearMap.comp εG) surjectiveF
  obtain ⟨c, hd, htd, _, hφ, hρ⟩ :=
    exists_comparisonData_of_lift d₁ td₁ εF εG surjectiveG
      exactF exactG β φ₀ hφ₀
  exact ⟨c, hd, htd, hφ, hρ⟩

omit [DecidableEq F₁] [DecidableEq G₁] in
/-- Equation (47b), the reverse-seed equation, follows from the constructed
homotopy with the manuscript's characteristic-two signs. -/
theorem reverse_seed (c : Stabilization.ComparisonData A F₀ F₁ G₀ G₁) :
    c.φ₀ * c.ρ₀ + c.d₁ * c.η₀ = 1 := by
  rw [c.homotopyF, ← add_assoc, add_comm (c.φ₀ * c.ρ₀) 1, add_assoc,
    Stabilization.matrix_add_self, add_zero]

end Comparison

end Decoupling.Comparison
