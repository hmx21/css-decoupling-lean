import Decoupling.HighDim.StableFreeEffectivePartialTransport

/-! Fixed association permutations for actual stable-cokernel lift matrices. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
variable {R : Type*} [CommRing R]
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

def assocOrder (a b c : ℕ) : Fin (a+(b+c)) ≃ Fin ((a+b)+c) :=
  (finSumFinEquiv : Fin a ⊕ Fin (b+c) ≃ _).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv : Fin b ⊕ Fin c ≃ _).symm).trans
      ((Equiv.sumAssoc (Fin a) (Fin b) (Fin c)).symm.trans
        ((Equiv.sumCongr (finSumFinEquiv : Fin a ⊕ Fin b ≃ _) (Equiv.refl _)).trans finSumFinEquiv)))

theorem assocOrder_coordinates (a b c : ℕ) (x : Power R a) (y : Power R b) (z : Power R c) :
    (powerAdd a (b+c) (x,powerAdd b c (y,z))) ∘ (assocOrder a b c).symm =
      powerAdd (a+b) c (powerAdd a b (x,y),z) := by
  funext i
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin (a+b) ⊕ Fin c ≃ _).surjective i
  rcases i with i|i
  · obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin b ≃ _).surjective i
    rcases i with i|i <;> simp [Function.comp_def,assocOrder,powerAdd]
  · simp [Function.comp_def,assocOrder,powerAdd]

theorem assocOrder_coordinates_back (a b c : ℕ) (x : Power R a) (y : Power R b) (z : Power R c) :
    (powerAdd (a+b) c (powerAdd a b (x,y),z)) ∘ assocOrder a b c =
      powerAdd a (b+c) (x,powerAdd b c (y,z)) := by
  rw [←assocOrder_coordinates]
  funext i
  simp only [Function.comp_apply,Equiv.symm_apply_apply]

def extendAssociation {n m p q : ℕ} (L : Matrix (Fin (m+q)) (Fin (n+p)) R) (b : ℕ) :
    Matrix (Fin (m+(q+b))) (Fin (n+(p+b))) R :=
  (diagonalBlocks L (1 : Matrix (Fin b) (Fin b) R)).submatrix
    (assocOrder m q b) (assocOrder n p b)

theorem extendAssociation_mulVec {n m p q : ℕ} (L : Matrix (Fin (m+q)) (Fin (n+p)) R)
    (b : ℕ) (x : Power R n) (y : Power R p) (z : Power R b) :
    extendAssociation L b *ᵥ powerAdd n (p+b) (x,powerAdd p b (y,z)) =
      powerAdd m (q+b)
        (((powerAdd m q).symm (L *ᵥ powerAdd n p (x,y))).1,
         powerAdd q b (((powerAdd m q).symm (L *ᵥ powerAdd n p (x,y))).2,z)) := by
  rw [extendAssociation,Matrix.submatrix_mulVec_equiv,assocOrder_coordinates,
    diagonalBlocks_mulVec,Matrix.one_mulVec]
  have he := (powerAdd (R := R) m q).apply_symm_apply (L *ᵥ powerAdd n p (x,y))
  conv_lhs => rw [←he]
  exact assocOrder_coordinates_back _ _ _ _ _ _

end Decoupling.HighDim.StableFree.Effective
