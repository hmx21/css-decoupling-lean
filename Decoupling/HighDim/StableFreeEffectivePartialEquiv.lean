import Decoupling.HighDim.StableFreeEffectiveReindex

/-!
# Actual inverse maps on the represented projective summands

The free ambient matrices need only be inverse on the actual projector
images. This predicate is invariant under the fixed coordinate reordering
and directly constructs an ordinary linear equivalence of the represented
modules; it does not postulate a basis or a free ambient inverse.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {R : Type u} [CommRing R] {p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

structure PartialEquiv (E : Matrix (Fin p) (Fin p) R) (F : Matrix (Fin q) (Fin q) R)
    (A : Matrix (Fin q) (Fin p) R) (B : Matrix (Fin p) (Fin q) R) : Prop where
  forward : ∀ x, E *ᵥ x = x → F *ᵥ (A *ᵥ x) = A *ᵥ x ∧ B *ᵥ (A *ᵥ x) = x
  inverse : ∀ y, F *ᵥ y = y → E *ᵥ (B *ᵥ y) = B *ᵥ y ∧ A *ᵥ (B *ᵥ y) = y

namespace PartialEquiv

theorem symm {E : Matrix (Fin p) (Fin p) R} {F : Matrix (Fin q) (Fin q) R}
    {A : Matrix (Fin q) (Fin p) R} {B : Matrix (Fin p) (Fin q) R}
    (h : PartialEquiv E F A B) : PartialEquiv F E B A := ⟨h.inverse,h.forward⟩

/-- An actual equivalence with coordinate formulas gives both inverse
identities on the exact projector images. -/
theorem of_representation {P Q : ModuleCat.{u} R} (p : FiniteRetract P) (q : FiniteRetract Q)
    (e : P ≃ₗ[R] Q) (A : Matrix (Fin q.size) (Fin p.size) R)
    (B : Matrix (Fin p.size) (Fin q.size) R)
    (hA : ∀ x, A *ᵥ p.embed x = q.embed (e x))
    (hB : ∀ y, B *ᵥ q.embed y = p.embed (e.symm y)) :
    PartialEquiv p.projector q.projector A B := by
  constructor
  · intro x hx
    have he : p.embed (p.project x) = x := (p.projector_mulVec x).symm.trans hx
    rw [←he,hA]
    constructor
    · rw [q.projector_mulVec,q.project_embed]
    · rw [hB,e.symm_apply_apply]
  · intro y hy
    have he : q.embed (q.project y) = y := (q.projector_mulVec y).symm.trans hy
    rw [←he,hB]
    constructor
    · rw [p.projector_mulVec,p.project_embed]
    · rw [hA,e.apply_symm_apply]

noncomputable section

/-- Construct the actual module equivalence from the two computed matrices. -/
def toEquiv {P Q : ModuleCat.{u} R} (p : FiniteRetract P) (q : FiniteRetract Q)
    (A : Matrix (Fin q.size) (Fin p.size) R) (B : Matrix (Fin p.size) (Fin q.size) R)
    (h : PartialEquiv p.projector q.projector A B) : P ≃ₗ[R] Q :=
  LinearEquiv.ofLinearMap (p.mapOfMatrix q A) (q.mapOfMatrix p B)
    (by
      ext y
      apply q.embed_injective
      have hy : q.projector *ᵥ q.embed y = q.embed y := by rw [q.projector_mulVec,q.project_embed]
      have hb := h.inverse (q.embed y) hy
      change q.embed (q.project (A *ᵥ p.embed (p.project (B *ᵥ q.embed y)))) = q.embed y
      rw [←p.projector_mulVec,hb.1,hb.2,q.project_embed])
    (by
      ext x
      apply p.embed_injective
      have hx : p.projector *ᵥ p.embed x = p.embed x := by rw [p.projector_mulVec,p.project_embed]
      have ha := h.forward (p.embed x) hx
      change p.embed (p.project (B *ᵥ q.embed (q.project (A *ᵥ p.embed x)))) = p.embed x
      rw [←q.projector_mulVec,ha.1,ha.2,p.project_embed])

theorem toEquiv_coordinates {P Q : ModuleCat.{u} R} (p : FiniteRetract P) (q : FiniteRetract Q)
    (A : Matrix (Fin q.size) (Fin p.size) R) (B : Matrix (Fin p.size) (Fin q.size) R)
    (h : PartialEquiv p.projector q.projector A B) (x : P) :
    q.embed (toEquiv p q A B h x) = A *ᵥ p.embed x := by
  change q.embed (q.project (A *ᵥ p.embed x)) = _
  rw [←q.projector_mulVec]
  exact (h.forward _ (by rw [p.projector_mulVec,p.project_embed])).1

end
end PartialEquiv
end Decoupling.HighDim.StableFree.Effective
