import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-!
# Finite-dimensional homology and strict dimension losses

Source: `drafts/appendix.tex`, Appendix B.3. These are linear-algebra
lemmas for the actual native homology of a short complex, not a replacement
for the profile or its derived tensor product. The bridge to the CSS torus
and the canonical truncation triangles is constructed in subsequent files.
-/

namespace Decoupling.HighDim.Torus

open CategoryTheory CategoryTheory.Limits

noncomputable section

variable {K : Type*} [Field K]

theorem finrank_homology (S : ShortComplex (ModuleCat K)) :
    Module.finrank K S.homology =
      Module.finrank K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) :=
  S.moduleCatHomologyIso.toLinearEquiv.finrank_eq

instance finite_homology (S : ShortComplex (ModuleCat K)) [Module.Finite K S.X₂] :
    Module.Finite K S.homology :=
  by
    let : Module.Finite K S.moduleCatLeftHomologyData.H := by
      change Module.Finite K (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles)
      infer_instance
    exact Module.Finite.equiv S.moduleCatHomologyIso.symm.toLinearEquiv

/-- Rank-nullity for homology, retaining both adjacent losses. -/
theorem finrank_homology_add_ranks (S : ShortComplex (ModuleCat K))
    [Module.Finite K S.X₂] :
    Module.finrank K S.homology + Module.finrank K S.moduleCatToCycles.range +
      Module.finrank K S.g.hom.range = Module.finrank K S.X₂ := by
  rw [finrank_homology, Submodule.finrank_quotient_add_finrank]
  exact (Nat.add_comm _ _).trans S.g.hom.finrank_range_add_finrank_ker

theorem finrank_homology_le (S : ShortComplex (ModuleCat K))
    [Module.Finite K S.X₂] :
    Module.finrank K S.homology ≤ Module.finrank K S.X₂ := by
  have h := finrank_homology_add_ranks S
  omega

/-- A nonzero outgoing differential forces strict loss. -/
theorem finrank_homology_lt_of_g_ne_zero (S : ShortComplex (ModuleCat K))
    [Module.Finite K S.X₂] (hg : S.g ≠ 0) :
    Module.finrank K S.homology < Module.finrank K S.X₂ := by
  have hg' : S.g.hom.range ≠ ⊥ := by
    intro h
    exact hg (ModuleCat.hom_ext (LinearMap.range_eq_bot.mp h))
  have hp : 0 < Module.finrank K S.g.hom.range := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hg' (Submodule.finrank_eq_zero.mp h)
  have h := finrank_homology_add_ranks S
  omega

/-- Full dimension is equivalent to vanishing of both adjacent maps. -/
theorem finrank_homology_eq_iff (S : ShortComplex (ModuleCat K))
    [Module.Finite K S.X₂] :
    Module.finrank K S.homology = Module.finrank K S.X₂ ↔ S.f = 0 ∧ S.g = 0 := by
  constructor
  · intro h
    have hr := finrank_homology_add_ranks S
    have hf : Module.finrank K S.moduleCatToCycles.range = 0 := by omega
    have hg : Module.finrank K S.g.hom.range = 0 := by omega
    have hf' : S.moduleCatToCycles = 0 :=
      LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hf)
    constructor
    · ext x
      have hx := congrArg (fun f => (f x : LinearMap.ker S.g.hom).val) hf'
      exact hx
    · exact ModuleCat.hom_ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp hg))
  · rintro ⟨hf, hg⟩
    have hf' : S.moduleCatToCycles = 0 := by
      ext x
      simp [ShortComplex.moduleCatToCycles, hf]
    have hr := finrank_homology_add_ranks S
    have hf0 : Module.finrank K S.moduleCatToCycles.range = 0 := by
      rw [hf', LinearMap.range_zero]; simp
    have hg0 : Module.finrank K S.g.hom.range = 0 := by
      have hg' : S.g.hom = 0 := congrArg ModuleCat.Hom.hom hg
      rw [hg', LinearMap.range_zero]; simp
    omega

/-- Exactness at the middle term gives its dimension decomposition. -/
theorem finrank_of_exact {A B C : ModuleCat K}
    [Module.Finite K B] (f : A ⟶ B) (g : B ⟶ C)
    (he : Function.Exact f g) :
    Module.finrank K B = Module.finrank K f.hom.range + Module.finrank K g.hom.range := by
  have hker : LinearMap.range f.hom = LinearMap.ker g.hom := (LinearMap.exact_iff.mp he).symm
  rw [hker, Nat.add_comm]
  exact g.hom.finrank_range_add_finrank_ker |>.symm

/-- The central three terms of an exact sequence satisfy the triangle
inequality used at every Postnikov step. -/
theorem finrank_exact_middle_le {A B C : ModuleCat K}
    [Module.Finite K A] [Module.Finite K B] [Module.Finite K C]
    (f : A ⟶ B) (g : B ⟶ C) (he : Function.Exact f g) :
    Module.finrank K B ≤ Module.finrank K A + Module.finrank K C := by
  rw [finrank_of_exact f g he]
  exact Nat.add_le_add (LinearMap.finrank_range_le f.hom) g.hom.range.finrank_le

/-- A nonzero connecting map makes the triangle inequality strict. -/
theorem finrank_exact_middle_lt {A B C E : ModuleCat K}
    [Module.Finite K A] [Module.Finite K B] [Module.Finite K C]
    (f : A ⟶ B) (g : B ⟶ C) (δ : C ⟶ E)
    (he : Function.Exact f g) (he' : Function.Exact g δ) (hδ : δ ≠ 0) :
    Module.finrank K B < Module.finrank K A + Module.finrank K C := by
  have hker : LinearMap.range g.hom = LinearMap.ker δ.hom := (LinearMap.exact_iff.mp he').symm
  have hr := δ.hom.finrank_range_add_finrank_ker
  have hp : 0 < Module.finrank K δ.hom.range := by
    apply Nat.pos_of_ne_zero
    intro h
    exact hδ (ModuleCat.hom_ext (LinearMap.range_eq_bot.mp (Submodule.finrank_eq_zero.mp h)))
  have hg : Module.finrank K g.hom.range < Module.finrank K C := by rw [hker]; omega
  rw [finrank_of_exact f g he]
  exact Nat.add_lt_add_of_le_of_lt (LinearMap.finrank_range_le f.hom) hg

end
end Decoupling.HighDim.Torus
