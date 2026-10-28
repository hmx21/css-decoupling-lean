import Decoupling.HighDim.StableFreeEffectiveFullProgram
import Decoupling.HighDim.StableFreeEffectiveAbsorb

/-! The computed stable matrices construct the real complement isomorphism. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix
universe u
noncomputable section
variable {R : Type u} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

@[simp] theorem diagonalBlocks_one_one (a b : ℕ) :
    diagonalBlocks (1 : Matrix (Fin a) (Fin a) R) (1 : Matrix (Fin b) (Fin b) R) = 1 := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) a b).surjective x
  rw [diagonalBlocks_mulVec,Matrix.one_mulVec,Matrix.one_mulVec,Matrix.one_mulVec]

theorem free_projector {F : ModuleCat.{u} R} (n : ℕ) (c : F ≃ₗ[R] Power R n) :
    (FiniteRetract.ofCoordinates n c).projector = 1 := by
  apply Matrix.mulVec_injective
  funext x
  rw [FiniteRetract.projector_mulVec,Matrix.one_mulVec]
  exact c.apply_symm_apply x

theorem prod_free_projector {Q F : ModuleCat.{u} R} (q : FiniteRetract Q)
    (n : ℕ) (c : F ≃ₗ[R] Power R n) :
    (q.prod (FiniteRetract.ofCoordinates n c)).projector =
      diagonalBlocks q.projector (1 : Matrix (Fin n) (Fin n) R) := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) q.size n).surjective x
  rw [FiniteRetract.projector_mulVec]
  change powerAdd q.size n
    (q.embed (q.project ((powerAdd q.size n).symm (powerAdd q.size n (x,y))).1),
      c (c.symm ((powerAdd q.size n).symm (powerAdd q.size n (x,y))).2)) = _
  rw [LinearEquiv.symm_apply_apply,c.apply_symm_apply]
  have hd := diagonalBlocks_mulVec q.projector (1 : Matrix (Fin n) (Fin n) R) x y
  simpa only [FiniteRetract.projector_mulVec,Matrix.one_mulVec] using hd.symm

variable {Q : ModuleCat.{u} R} {q r B : ℕ}

/-- Actual isomorphism from the known free power to the stabilized projective
complement. It is constructed from the real matrix outputs, with no basis of Q. -/
def complementFromMatrices (rq : RetractAt Q q)
    (S : Matrix (Fin (q+B)) (Fin r) R) (T : Matrix (Fin r) (Fin (q+B)) R)
    (hs : PartialEquiv (1 : Matrix (Fin r) (Fin r) R)
      (diagonalBlocks rq.model.projector 1) S T) :
    Power R r ≃ₗ[R] (Q × Power R B) :=
  PartialEquiv.toEquiv (FiniteRetract.ofCoordinates (P := ModuleCat.of R (Power R r)) r (LinearEquiv.refl R _))
    (rq.model.prod (FiniteRetract.ofCoordinates (P := ModuleCat.of R (Power R B)) B (LinearEquiv.refl R _))) S T
    (by simpa only [free_projector,prod_free_projector] using hs)

theorem complementFromMatrices_forward (rq : RetractAt Q q)
    (S : Matrix (Fin (q+B)) (Fin r) R) (T : Matrix (Fin r) (Fin (q+B)) R)
    (hs : PartialEquiv (1 : Matrix (Fin r) (Fin r) R)
      (diagonalBlocks rq.model.projector 1) S T) (x : Power R r) :
    S *ᵥ x = powerAdd q B
      (rq.embed (complementFromMatrices rq S T hs x).1,(complementFromMatrices rq S T hs x).2) := by
  unfold complementFromMatrices
  exact (PartialEquiv.toEquiv_coordinates
    (FiniteRetract.ofCoordinates (P := ModuleCat.of R (Power R r)) r (LinearEquiv.refl R _))
    (rq.model.prod (FiniteRetract.ofCoordinates (P := ModuleCat.of R (Power R B)) B (LinearEquiv.refl R _)))
    S T (by simpa only [free_projector,prod_free_projector] using hs) x).symm

theorem complementFromMatrices_inverse (rq : RetractAt Q q)
    (S : Matrix (Fin (q+B)) (Fin r) R) (T : Matrix (Fin r) (Fin (q+B)) R)
    (hs : PartialEquiv (1 : Matrix (Fin r) (Fin r) R)
      (diagonalBlocks rq.model.projector 1) S T) (y : Q) (z : Power R B) :
    T *ᵥ powerAdd q B (rq.embed y,z) = (complementFromMatrices rq S T hs).symm (y,z) := rfl

end
end Decoupling.HighDim.StableFree.Effective
