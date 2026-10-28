import Decoupling.HighDim.SchreyerGroebnerDivision

/-! # Empty-module and zero-variable boundary interfaces -/
namespace Decoupling.HighDim.SchreyerModule
noncomputable section
variable {K : Type*} [Field K] {D r s : ℕ}

theorem empty_groebner (o : ModuleOrder D r) :
    IsGroebnerBasis o (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Vec K D r) ⊥ := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro f hf t ht
    have hz : f=0 := hf
    exact False.elim (ht.ne_zero hz)

theorem empty_minimal (o : ModuleOrder D r) :
    IsMinimal o (fun i : Fin 0 => Fin.elim0 i : Fin 0 → Vec K D r) := by
  constructor
  · intro i
    exact Fin.elim0 i
  · intro i
    exact Fin.elim0 i

theorem minimal_bottom_size_zero {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    (hG : IsGroebnerBasis o G ⊥) (hm : IsMinimal o G) : s=0 := by
  by_contra hs
  have hp : 0<s := Nat.pos_of_ne_zero hs
  have hz : G ⟨0,hp⟩=0 := hG.mem ⟨0,hp⟩
  exact hm.nonzero ⟨0,hp⟩ hz

theorem rank_zero_vector_eq_zero (f : Vec K D 0) : f=0 := by
  funext i
  exact Fin.elim0 i

theorem rank_zero_submodule_eq_bot (N : Submodule (Poly K D) (Vec K D 0)) : N=⊥ := by
  apply le_antisymm
  · intro f _
    exact rank_zero_vector_eq_zero f
  · exact bot_le

/-- With no variables, minimal leading divisibility already forces distinct positions. -/
theorem minimal_zero_variables_positions {o : ModuleOrder 0 r} {G : Fin s → Vec K 0 r}
    (hm : IsMinimal o G) (t : Fin s → Term 0 r) (ht : ∀ i,IsLeading o (G i) (t i)) :
    Function.Injective (fun i => (t i).2) := by
  intro i j hp
  have he : (t i).1=(t j).1 := by
    ext a
    exact Fin.elim0 a
  exact hm.minimal i j (t i) (t j) (ht i) (ht j) ⟨hp,he.le⟩

end
end Decoupling.HighDim.SchreyerModule
