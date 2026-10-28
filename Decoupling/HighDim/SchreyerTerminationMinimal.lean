import Decoupling.HighDim.SchreyerTerminationSorting
import Decoupling.HighDim.SchreyerGroebnerMinimal
import Decoupling.HighDim.SchreyerSyzygyMap
import Decoupling.HighDim.SchreyerModuleProductIndependent

/-!
# Preserving missing variables and the terminal free family

Minimal leading terms are inherited from a proved Gröbner family. Sorting
then changes only its finite indexing. At the last stage, divisibility in
one remaining variable forces distinct leading positions, which proves
independence of the actual polynomial columns and a zero actual kernel.
-/
namespace Decoupling.HighDim.SchreyerTermination
open SchreyerModule SchreyerSyzygy
noncomputable section
variable {K : Type*} [Field K] {D r s : ℕ}

theorem exists_sorted_minimal_inheriting (o : ModuleOrder D r)
    (N : Submodule (Poly K D) (Vec K D r)) (G : Fin s → Vec K D r)
    (hG : IsGroebnerBasis o G N) (P : Term D r → Prop)
    (hP : ∀ i u,IsLeading o (G i) u → P u) :
    ∃ n : ℕ, ∃ H : Fin n → Vec K D r, ∃ t : Fin n → Term D r,
      IsGroebnerBasis o H N ∧ IsMinimal o H ∧ (∀ i,IsLeading o (H i) (t i)) ∧
      (∀ i j,i<j → (t i).2=(t j).2 → LexGE (t i).1 (t j).1) ∧
      (∀ i,P (t i)) := by
  obtain ⟨n,H,t,hH,hmin,hlead,hsort⟩ := exists_sorted_minimal_groebner o N
  exact ⟨n,H,t,hH,hmin,hlead,hsort,
    fun i => minimal_leading_property hG hH hmin P hP i (t i) (hlead i)⟩

theorem terminal_linearIndependent (o : ModuleOrder D r)
    (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : IsMinimal o G) (hlead : ∀ i,IsLeading o (G i) (t i))
    (hmiss : ∀ i,MissingPrefix (D-1) (t i).1) : LinearIndependent (Poly K D) G := by
  apply linearIndependent_of_leading_positions o G t hlead
  apply terminal_positions_injective t hmiss
  intro i j hne hpos hdiv
  exact hne (hG.minimal i j (t i) (t j) (hlead i) (hlead j) ⟨hpos,hdiv⟩)

theorem columnMap_ker_eq_bot_of_independent (G : Fin s → Vec K D r)
    (hG : LinearIndependent (Poly K D) G) : LinearMap.ker (columnMap G)=⊥ := by
  classical
  apply LinearMap.ker_eq_bot'.mpr
  intro z hz
  funext i
  exact linearIndependent_iff'.mp hG Finset.univ z hz i (Finset.mem_univ i)

/-- No projective-module freeness theorem is used at the terminal step. -/
theorem terminal_kernel_eq_bot (o : ModuleOrder D r)
    (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : IsMinimal o G) (hlead : ∀ i,IsLeading o (G i) (t i))
    (hmiss : ∀ i,MissingPrefix (D-1) (t i).1) : LinearMap.ker (columnMap G)=⊥ :=
  columnMap_ker_eq_bot_of_independent G (terminal_linearIndependent o G t hG hlead hmiss)

end
end Decoupling.HighDim.SchreyerTermination
