import Decoupling.HighDim.StableFreeEffectiveStageProgram

/-!
# Pure coordinate permutations and the terminal free blocks

These operations copy coefficients and perform no field arithmetic. The
permutation is exactly collectRight from generalized Schanuel, so the
recursive return swaps the two directions without choosing any bases.
-/

namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
variable {K : Type*} [Field K] {D h : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Reorder p,(a,b) into (a,p),b in the fixed Fin enumeration. -/
def collectOrder (p a b : ℕ) : Fin (p+(a+b)) ≃ Fin ((a+p)+b) :=
  (finSumFinEquiv : Fin p ⊕ Fin (a+b) ≃ _).symm.trans
    ((Equiv.sumCongr (Equiv.refl _) (finSumFinEquiv : Fin a ⊕ Fin b ≃ _).symm).trans
      ((Equiv.sumAssoc (Fin p) (Fin a) (Fin b)).symm.trans
        ((Equiv.sumCongr (Equiv.sumComm (Fin p) (Fin a)) (Equiv.refl _)).trans
          ((Equiv.sumCongr (finSumFinEquiv : Fin a ⊕ Fin p ≃ _) (Equiv.refl _)).trans
            (finSumFinEquiv : Fin (a+p) ⊕ Fin b ≃ _)))))

/-- Reindex an actual dense matrix by known row and column maps. -/
def reindexDense {m n r c : ℕ} (A : DenseMatrix K D m n h)
    (rows : Fin r → Fin m) (cols : Fin c → Fin n) : DenseMatrix K D r c h :=
  Vector.ofFn fun i => Vector.ofFn fun j => A[rows i][cols j]

theorem reindexDense_correct {m n r c : ℕ} (A : DenseMatrix K D m n h)
    (rows : Fin r → Fin m) (cols : Fin c → Fin n) :
    matrixDenote (reindexDense A rows cols) = (matrixDenote A).submatrix rows cols := by
  funext i j
  simp only [matrixDenote,reindexDense,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,Matrix.submatrix_apply]

/-- Discard the genuinely zero base modules at the terminal stage. -/
def bottomBlock {s t p q : ℕ} (A : Matrix (Fin (t+q)) (Fin (s+p)) (Laurent K D)) :
    Matrix (Fin q) (Fin p) (Laurent K D) :=
  A.submatrix (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

def bottomBlockDense {s t p q : ℕ} (A : DenseMatrix K D (t+q) (s+p) h) : DenseMatrix K D q p h :=
  reindexDense A (fun i => finSumFinEquiv (Sum.inr i)) (fun j => finSumFinEquiv (Sum.inr j))

theorem bottomBlockDense_correct {s t p q : ℕ} (A : DenseMatrix K D (t+q) (s+p) h) :
    matrixDenote (bottomBlockDense A) = bottomBlock (matrixDenote A) := reindexDense_correct _ _ _

theorem bottomBlock_mulVec {s t p q : ℕ}
    (A : Matrix (Fin (t+q)) (Fin (s+p)) (Laurent K D)) (x : Power (Laurent K D) p) :
    bottomBlock A *ᵥ x =
      ((powerAdd t q).symm (A *ᵥ powerAdd s p (0,x))).2 := by
  funext i
  change (∑ j : Fin p, A (finSumFinEquiv (Sum.inr i)) (finSumFinEquiv (Sum.inr j))*x j) = _
  change _ = ∑ j : Fin (s+p), A (finSumFinEquiv (Sum.inr i)) j * powerAdd s p (0,x) j
  rw [←Equiv.sum_comp (finSumFinEquiv : Fin s ⊕ Fin p ≃ _)]
  simp only [Fintype.sum_sum_type,powerAdd_apply_sum,Sum.elim_inl,Sum.elim_inr,
    Pi.zero_apply,mul_zero,Finset.sum_const_zero,zero_add]

/-- The copy permutation agrees with the exact collectRight coordinate map. -/
theorem collectOrder_coordinates {R : Type*} [CommRing R] (p a b : ℕ)
    (x : Power R p) (y : Power R a) (z : Power R b) :
    (powerAdd p (a+b) (x,powerAdd a b (y,z))) ∘ (collectOrder p a b).symm =
      powerAdd (a+p) b (powerAdd a p (y,x),z) := by
  funext i
  obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin (a+p) ⊕ Fin b ≃ _).surjective i
  rcases i with i|i
  · obtain ⟨i,rfl⟩ := (finSumFinEquiv : Fin a ⊕ Fin p ≃ _).surjective i
    rcases i with i|i <;>
      simp [Function.comp_def,collectOrder,powerAdd]
  · simp [Function.comp_def,collectOrder,powerAdd]

end Decoupling.HighDim.StableFree.Effective
