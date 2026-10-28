import Decoupling.HighDim.SchreyerTerminationMinimal
import Decoupling.HighDim.SchreyerSyzygyKernel

/-!
# One variable is eliminated from the leading terms in each Schreyer step

The input pair family is an actual kernel Gröbner family with the proved
lcm-quotient leaders. Minimization preserves those leaders exactly, and a
finite reindexing restores descending lexicographic order for recursion.
-/
namespace Decoupling.HighDim.SchreyerTermination
open SchreyerModule SchreyerSyzygy
noncomputable section
variable {K : Type*} [Field K] {D r s n k : ℕ}

theorem next_minimal_missing (o : ModuleOrder D r) (G : Fin s → Vec K D r)
    (t : Fin s → Term D r)
    (hsort : ∀ i j,i<j → (t i).2=(t j).2 → LexGE (t i).1 (t j).1)
    (hmiss : ∀ i,MissingPrefix k (t i).1)
    (S : Fin n → Vec K D s)
    (hS : IsGroebnerBasis (inducedOrder o t) S (LinearMap.ker (columnMap G)))
    (hp : ∀ a,∃ i j,i<j ∧ (t i).2=(t j).2 ∧
      IsLeading (inducedOrder o t) (S a) (pairLeading t i j)) :
    ∃ m : ℕ, ∃ H : Fin m → Vec K D s, ∃ u : Fin m → Term D s,
      IsGroebnerBasis (inducedOrder o t) H (LinearMap.ker (columnMap G)) ∧
      IsMinimal (inducedOrder o t) H ∧
      (∀ a,IsLeading (inducedOrder o t) (H a) (u a)) ∧
      (∀ a b,a<b → (u a).2=(u b).2 → LexGE (u a).1 (u b).1) ∧
      (∀ a,MissingPrefix (k+1) (u a).1) := by
  apply exists_sorted_minimal_inheriting (inducedOrder o t) (LinearMap.ker (columnMap G)) S hS
    (fun u => MissingPrefix (k+1) u.1)
  intro a u hu
  obtain ⟨i,j,hij,hpos,hlead⟩ := hp a
  have he : u=pairLeading t i j := isLeading_unique (inducedOrder o t) hu hlead
  rw [he]
  exact lcmQuotient_missing_succ (hmiss i) (hmiss j) (hsort i j hij hpos)

end
end Decoupling.HighDim.SchreyerTermination
