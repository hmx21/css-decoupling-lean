import Decoupling.HighDim.SchreyerModuleOrder

/-! # A proved initial module order for every finite rank and dimension -/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section

variable {D r : ℕ}

def orderKey (m : MonomialOrder (Fin D)) (t : Term D r) : m.syn ×ₗ Fin r :=
  toLex (m.toSyn t.1,t.2)

theorem orderKey_injective (m : MonomialOrder (Fin D)) :
    Function.Injective (orderKey (r := r) m) := by
  intro s t h
  have h' : (m.toSyn s.1,s.2)=(m.toSyn t.1,t.2) := congrArg ofLex h
  exact Prod.ext (m.toSyn.injective (congrArg (fun z : m.syn × Fin r => z.1) h')) (congrArg (fun z : m.syn × Fin r => z.2) h')

/-- Term-over-position order. The scalar order remains an explicit parameter;
Schreyer orders can subsequently replace this initial order. -/
def initialOrder (m : MonomialOrder (Fin D)) (r : ℕ) : ModuleOrder D r where
  scalarOrder := m
  termOrder := LinearOrder.lift' (orderKey m) (orderKey_injective m)
  wellFounded := InvImage.wf (orderKey m) wellFounded_lt
  shift_lt a s t h := by
    change orderKey m s < orderKey m t at h
    change orderKey m (shift a s) < orderKey m (shift a t)
    rw [orderKey,orderKey,Prod.Lex.toLex_lt_toLex] at h
    rw [orderKey,orderKey,Prod.Lex.toLex_lt_toLex]
    rcases h with h|h
    · left
      simpa only [shift,map_add,add_comm] using add_lt_add_left h (m.toSyn a)
    · right
      exact ⟨by simpa only [shift,map_add] using congrArg (fun z => m.toSyn a+z) h.1,h.2⟩
  scalar_lt a b i h := by
    change orderKey m (a,i) < orderKey m (b,i)
    exact Prod.Lex.toLex_lt_toLex.mpr (Or.inl h)

end
end Decoupling.HighDim.SchreyerModule
