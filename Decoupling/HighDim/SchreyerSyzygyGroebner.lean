import Decoupling.HighDim.SchreyerSyzygyKernel
import Decoupling.HighDim.SchreyerGroebnerCriterionPairLift

/-!
# Schreyer's theorem for the actual polynomial kernel

Over an arbitrary field, strict division of every normalized S-polynomial
constructs a genuine kernel column with its exact induced-order leader.
The resulting finite family is a Gröbner basis of the whole actual kernel.
No homogeneity, infinite-field, or pre-existing kernel-basis assumption is
used. This is a mathematical construction using proved division existence.
-/
namespace Decoupling.HighDim.SchreyerSyzygy
open SchreyerModule
noncomputable section
variable {K : Type*} [Field K] {D r s : ℕ}

theorem exists_pair_syzygy {o : ModuleOrder D r}
    {G : Fin s → Vec K D r} {N : Submodule (Poly K D) (Vec K D r)}
    (hG : IsGroebnerBasis o G N) (t : Fin s → Term D r)
    (hlead : ∀ i,IsLeading o (G i) (t i))
    (i j : Fin s) (hij : i<j) (hpos : (t i).2=(t j).2) :
    ∃ z : Vec K D s,columnMap G z=0 ∧
      IsLeading (inducedOrder o t) z (pairLeading t i j) := by
  obtain ⟨q,he,hb⟩ := hG.standardRepresentation_strict
    (sPolynomial_mem (hG.mem i) (hG.mem j) (t i) (t j))
    (sPolynomial_below (hlead i) (hlead j) hpos)
  exact ⟨pairLift G t i j q,pairLift_kernel G t i j q he,
    pairLift_leading G t hlead i j hij hpos q hb⟩

/-- The complete S-pair family, with actual kernel generation and exact leaders. -/
theorem exists_kernel_groebner {o : ModuleOrder D r}
    {G : Fin s → Vec K D r} {N : Submodule (Poly K D) (Vec K D r)}
    (hG : IsGroebnerBasis o G N) (t : Fin s → Term D r)
    (hlead : ∀ i,IsLeading o (G i) (t i)) :
    ∃ n : ℕ, ∃ S : Fin n → Vec K D s,
      IsGroebnerBasis (inducedOrder o t) S (LinearMap.ker (columnMap G)) ∧
      (∀ a, ∃ i j,i<j ∧ (t i).2=(t j).2 ∧
        IsLeading (inducedOrder o t) (S a) (pairLeading t i j)) ∧
      Submodule.span (Poly K D) (Set.range S)=LinearMap.ker (columnMap G) := by
  obtain ⟨n,S,hS,hp⟩ := kernel_groebner_of_pair_witness o G t hlead
    (exists_pair_syzygy hG t hlead)
  exact ⟨n,S,hS,hp,hS.span_eq⟩

end
end Decoupling.HighDim.SchreyerSyzygy
