import Decoupling.HighDim.StableFreeEffectiveAbsorbBlocks

/-!
# Actual stable-cokernel equivalence and its two presentation lift matrices

The computed stable complement map is absorbed into the known initial
isomorphism. The matrices use only known products and fixed permutations.
Projection of the initial lift's complement coordinates makes the formula
valid even when a presentation lift is not normalized on the free ambient.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix
universe u
noncomputable section
variable {R : Type u} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {M N Q : ModuleCat.{u} R} {n m p q A B : ℕ}

def stabilizedQuotient (π : Power R n →ₗ[R] N) (k : ℕ) : Power R (n+k) →ₗ[R] (N × Power R k) :=
  (π.prodMap LinearMap.id).comp (powerAdd n k).symm.toLinearMap

@[simp] theorem stabilizedQuotient_apply (π : Power R n →ₗ[R] N) (k : ℕ)
    (x : Power R n) (y : Power R k) :
    stabilizedQuotient π k (powerAdd n k (x,y)) = (π x,y) := by
  change (π ((powerAdd n k).symm (powerAdd n k (x,y))).1,
    ((powerAdd n k).symm (powerAdd n k (x,y))).2) = _
  rw [LinearEquiv.symm_apply_apply]

/-- Absorb the actual constructed stable complement equivalence. -/
def absorbComputed (e : (N × Power R p) ≃ₗ[R] (M × Q))
    (s : Power R (p+A) ≃ₗ[R] (Q × Power R B)) :
    (N × Power R (p+B)) ≃ₗ[R] (M × Power R (p+A)) :=
  ((LinearEquiv.refl R N).prodCongr (powerAdd p B).symm).trans
    ((LinearEquiv.prodAssoc R N (Power R p) (Power R B)).symm.trans
      ((e.prodCongr (LinearEquiv.refl _ _)).trans
        ((LinearEquiv.prodAssoc R M Q (Power R B)).trans
          ((LinearEquiv.refl R M).prodCongr s.symm))))

@[simp] theorem absorbComputed_apply (e : (N × Power R p) ≃ₗ[R] (M × Q))
    (s : Power R (p+A) ≃ₗ[R] (Q × Power R B)) (x : N) (y : Power R p) (z : Power R B) :
    absorbComputed e s (x,powerAdd p B (y,z)) = ((e (x,y)).1,s.symm ((e (x,y)).2,z)) := by
  change ((e (x,((powerAdd p B).symm (powerAdd p B (y,z))).1)).1,
    s.symm ((e (x,((powerAdd p B).symm (powerAdd p B (y,z))).1)).2,
      ((powerAdd p B).symm (powerAdd p B (y,z))).2)) = _
  rw [LinearEquiv.symm_apply_apply]

@[simp] theorem absorbComputed_symm_apply (e : (N × Power R p) ≃ₗ[R] (M × Q))
    (s : Power R (p+A) ≃ₗ[R] (Q × Power R B)) (x : M) (y : Power R (p+A)) :
    (absorbComputed e s).symm (x,y) =
      ((e.symm (x,(s y).1)).1,powerAdd p B ((e.symm (x,(s y).1)).2,(s y).2)) := rfl

def absorbForwardMatrix (L : Matrix (Fin (m+q)) (Fin (n+p)) R)
    (T : Matrix (Fin (p+A)) (Fin (q+B)) R) (E : Matrix (Fin q) (Fin q) R) :
    Matrix (Fin (m+(p+A))) (Fin (n+(p+B))) R :=
  diagonalBlocks (1 : Matrix (Fin m) (Fin m) R) T *
    (diagonalBlocks (1 : Matrix (Fin m) (Fin m) R)
      (diagonalBlocks E (1 : Matrix (Fin B) (Fin B) R)) * extendAssociation L B)

def absorbInverseMatrix (L : Matrix (Fin (n+p)) (Fin (m+q)) R)
    (S : Matrix (Fin (q+B)) (Fin (p+A)) R) :
    Matrix (Fin (n+(p+B))) (Fin (m+(p+A))) R :=
  extendAssociation L B * diagonalBlocks (1 : Matrix (Fin m) (Fin m) R) S

/-- Actual quotient action of the forward matrix; no new lift is selected. -/
theorem absorbForwardMatrix_projects
    (πN : Power R n →ₗ[R] N) (πM : Power R m →ₗ[R] M)
    (rq : RetractAt Q q) (e : (N × Power R p) ≃ₗ[R] (M × Q))
    (s : Power R (p+A) ≃ₗ[R] (Q × Power R B))
    (L : Matrix (Fin (m+q)) (Fin (n+p)) R)
    (T : Matrix (Fin (p+A)) (Fin (q+B)) R)
    (hL : ∀ x, (πM.prodMap rq.project) ((powerAdd m q).symm (L *ᵥ x)) =
      e (stabilizedQuotient πN p x))
    (hT : ∀ y z, T *ᵥ powerAdd q B (rq.embed y,z) = s.symm (y,z))
    (x : Power R (n+(p+B))) :
    stabilizedQuotient πM (p+A) (absorbForwardMatrix L T rq.model.projector *ᵥ x) =
      absorbComputed e s (stabilizedQuotient πN (p+B) x) := by
  obtain ⟨⟨x,w⟩,rfl⟩ := (powerAdd (R := R) n (p+B)).surjective x
  obtain ⟨⟨y,z⟩,rfl⟩ := (powerAdd (R := R) p B).surjective w
  simp only [absorbForwardMatrix,←Matrix.mulVec_mulVec,extendAssociation_mulVec,
    diagonalBlocks_mulVec,Matrix.one_mulVec,
    stabilizedQuotient_apply,absorbComputed_apply]
  have hproj (v : Power R q) : rq.model.projector *ᵥ v = rq.embed (rq.project v) :=
    rq.model.projector_mulVec v
  rw [hproj,hT]
  have hl := hL (powerAdd n p (x,y))
  rw [stabilizedQuotient_apply] at hl
  change (πM ((powerAdd m q).symm (L *ᵥ powerAdd n p (x,y))).1,
    rq.project ((powerAdd m q).symm (L *ᵥ powerAdd n p (x,y))).2) = e (πN x,y) at hl
  exact congrArg (fun w : M × Q => (w.1,s.symm (w.2,z))) hl

/-- Actual quotient action of the inverse matrix, preserving its signs. -/
theorem absorbInverseMatrix_projects
    (πN : Power R n →ₗ[R] N) (πM : Power R m →ₗ[R] M)
    (rq : RetractAt Q q) (e : (N × Power R p) ≃ₗ[R] (M × Q))
    (s : Power R (p+A) ≃ₗ[R] (Q × Power R B))
    (L : Matrix (Fin (n+p)) (Fin (m+q)) R)
    (S : Matrix (Fin (q+B)) (Fin (p+A)) R)
    (hL : ∀ x, stabilizedQuotient πN p (L *ᵥ x) =
      e.symm ((πM.prodMap rq.project) ((powerAdd m q).symm x)))
    (hS : ∀ x, S *ᵥ x = powerAdd q B (rq.embed (s x).1,(s x).2))
    (x : Power R (m+(p+A))) :
    stabilizedQuotient πN (p+B) (absorbInverseMatrix L S *ᵥ x) =
      (absorbComputed e s).symm (stabilizedQuotient πM (p+A) x) := by
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) m (p+A)).surjective x
  rw [absorbInverseMatrix,←Matrix.mulVec_mulVec,diagonalBlocks_mulVec,Matrix.one_mulVec,hS,
    extendAssociation_mulVec,stabilizedQuotient_apply,stabilizedQuotient_apply,absorbComputed_symm_apply]
  have hl := hL (powerAdd m q (x,rq.embed (s y).1))
  change (πN ((powerAdd n p).symm (L *ᵥ powerAdd m q (x,rq.embed (s y).1))).1,
    ((powerAdd n p).symm (L *ᵥ powerAdd m q (x,rq.embed (s y).1))).2) =
    e.symm ((πM.prodMap rq.project) ((powerAdd m q).symm (powerAdd m q (x,rq.embed (s y).1)))) at hl
  rw [LinearEquiv.symm_apply_apply] at hl
  change (_,_) = e.symm (πM x,rq.project (rq.embed (s y).1)) at hl
  rw [rq.model.project_embed] at hl
  exact congrArg (fun w : N × Power R p => (w.1,powerAdd p B (w.2,(s y).2))) hl

end
end Decoupling.HighDim.StableFree.Effective
