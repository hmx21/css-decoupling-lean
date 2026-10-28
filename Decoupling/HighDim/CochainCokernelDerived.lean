import Decoupling.HighDim.CochainCokernel
import Mathlib.Algebra.Homology.DerivedCategory.KProjective

/-!
# Derived isomorphisms of projective models give stable check cokernels

Source: `drafts/appendix.tex`, C1–C2. An actual isomorphism in mathlib's
derived category is lifted to a homotopy equivalence when the two complexes
are bounded above and degreewise projective. We use the bijection on maps
from K-projective objects, not an assumed comparison-map certificate.
Combined with `CochainCokernel`, this proves stable cokernel isomorphism
for such models over the actual Laurent ring. The construction of the
finite free models of a CSS profile remains an upstream task.
-/

namespace Decoupling.HighDim.CochainCokernel

open CategoryTheory DerivedCategory

universe v u

noncomputable section

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory A]

/-- A genuine derived isomorphism between K-projective complexes lifts to
a homotopy equivalence of the original cochain complexes. -/
def homotopyEquivOfDerivedIso {C T : CochainComplex A ℤ}
    [C.IsKProjective] [T.IsKProjective]
    (e : Q.obj C ≅ Q.obj T) : HomotopyEquiv C T := by
  let F := HomotopyCategory.quotient A (ComplexShape.up ℤ)
  let e' : Qh.obj (F.obj C) ≅ Qh.obj (F.obj T) :=
    (quotientCompQhIso A).app C ≪≫ e ≪≫ ((quotientCompQhIso A).app T).symm
  let f := ((CochainComplex.IsKProjective.Qh_map_bijective C (F.obj T)).surjective e'.hom).choose
  have hf : Qh.map f = e'.hom :=
    ((CochainComplex.IsKProjective.Qh_map_bijective C (F.obj T)).surjective e'.hom).choose_spec
  let g := ((CochainComplex.IsKProjective.Qh_map_bijective T (F.obj C)).surjective e'.inv).choose
  have hg : Qh.map g = e'.inv :=
    ((CochainComplex.IsKProjective.Qh_map_bijective T (F.obj C)).surjective e'.inv).choose_spec
  apply HomotopyCategory.homotopyEquivOfIso
  refine { hom := f, inv := g, hom_inv_id := ?_, inv_hom_id := ?_ }
  · apply (CochainComplex.IsKProjective.Qh_map_bijective C (F.obj C)).injective
    simp only [Functor.map_comp, hf, hg, e'.hom_inv_id]
    exact (Qh.map_id _).symm
  · apply (CochainComplex.IsKProjective.Qh_map_bijective T (F.obj T)).injective
    simp only [Functor.map_comp, hf, hg, e'.inv_hom_id]
    exact (Qh.map_id _).symm

/-- Bounded-above degreewise projective complexes are K-projective, so the
previous lifting theorem needs no additional K-projectivity assumption. -/
def homotopyEquivOfDerivedIso_boundedAbove {C T : CochainComplex A ℤ}
    (c t : ℤ) [C.IsStrictlyLE c] [T.IsStrictlyLE t]
    [∀ n : ℤ, Projective (C.X n)] [∀ n : ℤ, Projective (T.X n)]
    (e : Q.obj C ≅ Q.obj T) : HomotopyEquiv C T := by
  letI : C.IsKProjective := CochainComplex.isKProjective_of_projective C c
  letI : T.IsKProjective := CochainComplex.isKProjective_of_projective T t
  exact homotopyEquivOfDerivedIso e

attribute [local instance] HasDerivedCategory.standard in
/-- Actual derived-equivalent bounded-above projective models over the
Laurent ring have stably isomorphic check cokernels. In applications the
finite free models supply the displayed projectivity and degree-two
finiteness/freeness; no ring-freeness hypothesis or comparison data is input. -/
theorem exists_stableEquiv_of_derivedIso
    {K : Type u} [Field K] {D : ℕ}
    {C T : CochainComplex (ModuleCat.{u} (Laurent K D)) ℤ}
    (c t : ℤ) [C.IsStrictlyLE c] [T.IsStrictlyLE t]
    [∀ n : ℤ, Projective (C.X n)] [∀ n : ℤ, Projective (T.X n)]
    [Module.Finite (Laurent K D) (C.X 2)] [Module.Free (Laurent K D) (C.X 2)]
    [Module.Finite (Laurent K D) (T.X 2)] [Module.Free (Laurent K D) (T.X 2)]
    (e : Q.obj C ≅ Q.obj T) :
    ∃ a b : ℕ, Nonempty
      ((CheckCokernel T × (Fin b → Laurent K D)) ≃ₗ[Laurent K D]
        (CheckCokernel C × (Fin a → Laurent K D))) :=
  exists_stableEquiv_of_homotopyEquiv (homotopyEquivOfDerivedIso_boundedAbove c t e)

end

end Decoupling.HighDim.CochainCokernel
