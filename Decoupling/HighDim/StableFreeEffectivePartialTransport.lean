import Decoupling.HighDim.StableFreeEffectivePartialEquiv

/-! Pure reindexing preserves the exact inverse relations on projector images. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

namespace PartialEquiv

theorem reindex {p q r s : ℕ} {E : Matrix (Fin p) (Fin p) R} {F : Matrix (Fin q) (Fin q) R}
    {A : Matrix (Fin q) (Fin p) R} {B : Matrix (Fin p) (Fin q) R}
    (h : PartialEquiv E F A B) (e : Fin r ≃ Fin p) (f : Fin s ≃ Fin q) :
    PartialEquiv (E.submatrix e e) (F.submatrix f f) (A.submatrix f e) (B.submatrix e f) := by
  constructor
  · intro x hx
    rw [Matrix.submatrix_mulVec_equiv] at hx
    have hx' : E *ᵥ (x ∘ e.symm) = x ∘ e.symm := by
      funext i
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun hx (e.symm i)
    have ha := h.forward _ hx'
    rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv,
      Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def,Equiv.apply_symm_apply,ha.1,ha.2,Equiv.symm_apply_apply] using
      And.intro (congrArg (fun v => v ∘ f) ha.1) (congrArg (fun v => v ∘ e) ha.2)
  · intro y hy
    rw [Matrix.submatrix_mulVec_equiv] at hy
    have hy' : F *ᵥ (y ∘ f.symm) = y ∘ f.symm := by
      funext i
      simpa only [Function.comp_apply,Equiv.apply_symm_apply] using congrFun hy (f.symm i)
    have hb := h.inverse _ hy'
    rw [Matrix.submatrix_mulVec_equiv,Matrix.submatrix_mulVec_equiv,
      Matrix.submatrix_mulVec_equiv]
    simpa only [Function.comp_def,Equiv.apply_symm_apply,hb.1,hb.2,Equiv.symm_apply_apply] using
      And.intro (congrArg (fun v => v ∘ e) hb.1) (congrArg (fun v => v ∘ f) hb.2)

end PartialEquiv

theorem collectOrder_coordinates_back (p a b : ℕ)
    (x : Power R p) (y : Power R a) (z : Power R b) :
    (powerAdd (a+p) b (powerAdd a p (y,x),z)) ∘ collectOrder p a b =
      powerAdd p (a+b) (x,powerAdd a b (y,z)) := by
  rw [←collectOrder_coordinates]
  funext i
  simp only [Function.comp_apply,Equiv.symm_apply_apply]

/-- The copied permutation sends the exact enlarged projector to the
projector of the original factor plus the alternating free rank. -/
theorem collectOrder_projector (p a b : ℕ) (E : Matrix (Fin p) (Fin p) R) :
    (diagonalBlocks (diagonalBlocks (1 : Matrix (Fin a) (Fin a) R) E)
      (1 : Matrix (Fin b) (Fin b) R)).submatrix (collectOrder p a b) (collectOrder p a b) =
      diagonalBlocks E (1 : Matrix (Fin (a+b)) (Fin (a+b)) R) := by
  apply Matrix.mulVec_injective
  funext x
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) p (a+b)).surjective x
  obtain ⟨⟨y,z⟩,rfl⟩ := (powerAdd (R := R) a b).surjective y
  rw [Matrix.submatrix_mulVec_equiv,collectOrder_coordinates,
    diagonalBlocks_mulVec,diagonalBlocks_mulVec,Matrix.one_mulVec,Matrix.one_mulVec,
    collectOrder_coordinates_back,diagonalBlocks_mulVec,Matrix.one_mulVec]

end Decoupling.HighDim.StableFree.Effective
