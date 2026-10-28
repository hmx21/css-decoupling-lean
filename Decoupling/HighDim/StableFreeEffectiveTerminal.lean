import Decoupling.HighDim.StableFreeEffectivePartialTransport

/-! Terminal matrices are the actual equivalence after discarding zero modules. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix LaurentArithmetic
universe u
variable {K : Type u} [Field K] {D h h₀ s t p q : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

private theorem bottom_forward {M N P Q : ModuleCat.{u} (Laurent K D)}
    (m : FiniteEmbedding M) (n : FiniteEmbedding N) (p : FiniteRetract P) (q : FiniteRetract Q)
    (e : EmbeddedEquiv m n p q) (x : P) :
    bottomBlock e.forward *ᵥ p.embed x = q.embed (e.equiv (0,x)).2 := by
  rw [bottomBlock_mulVec]
  have he := e.forward_eq (0,x)
  change e.forward *ᵥ powerAdd m.size p.size (m.embed 0,p.embed x) =
    powerAdd n.size q.size (n.embed (e.equiv (0,x)).1,q.embed (e.equiv (0,x)).2) at he
  rw [map_zero] at he
  rw [he,LinearEquiv.symm_apply_apply]

private theorem bottom_inverse {M N P Q : ModuleCat.{u} (Laurent K D)}
    (m : FiniteEmbedding M) (n : FiniteEmbedding N) (p : FiniteRetract P) (q : FiniteRetract Q)
    (e : EmbeddedEquiv m n p q) (y : Q) :
    bottomBlock e.inverse *ᵥ q.embed y = p.embed (e.equiv.symm (0,y)).2 := by
  rw [bottomBlock_mulVec]
  have he := e.inverse_eq (0,y)
  change e.inverse *ᵥ powerAdd n.size q.size (n.embed 0,q.embed y) =
    powerAdd m.size p.size (m.embed (e.equiv.symm (0,y)).1,p.embed (e.equiv.symm (0,y)).2) at he
  rw [map_zero] at he
  rw [he,LinearEquiv.symm_apply_apply]

/-- The terminal arrays are inverse on the actual projector images. -/
theorem terminal_correct (data : EmbeddedArrays K D s t p q h)
    (hv : StateValid (DenseTower.zero s : DenseTower K D h₀ 0 s) (.zero t) data) :
    PartialEquiv (matrixDenote data.leftProjector) (matrixDenote data.rightProjector)
      (matrixDenote (bottomBlockDense data.forward)) (matrixDenote (bottomBlockDense data.inverse)) := by
  obtain ⟨w⟩ := hv
  cases w.leftResolution with
  | zero _ hM =>
    cases w.rightResolution with
    | zero _ hN =>
      rw [bottomBlockDense_correct,bottomBlockDense_correct,w.forward_eq,w.inverse_eq,w.left_eq,w.right_eq]
      constructor
      · intro x hx
        have he : w.left.embed (w.left.project x) = x :=
          (w.left.model.projector_mulVec x).symm.trans hx
        rw [←he,bottom_forward]
        constructor
        · rw [FiniteRetract.projector_mulVec,FiniteRetract.project_embed]
        · rw [bottom_inverse]
          have hz : (0,(w.equiv.equiv (0,w.left.project x)).2) =
              w.equiv.equiv (0,w.left.project x) := Prod.ext (hN _).symm rfl
          rw [hz,w.equiv.equiv.symm_apply_apply]
      · intro y hy
        have he : w.right.embed (w.right.project y) = y :=
          (w.right.model.projector_mulVec y).symm.trans hy
        rw [←he,bottom_inverse]
        constructor
        · rw [FiniteRetract.projector_mulVec,FiniteRetract.project_embed]
        · rw [bottom_forward]
          have hz : (0,(w.equiv.equiv.symm (0,w.right.project y)).2) =
              w.equiv.equiv.symm (0,w.right.project y) := Prod.ext (hM _).symm rfl
          rw [hz,w.equiv.equiv.apply_symm_apply]

end Decoupling.HighDim.StableFree.Effective
