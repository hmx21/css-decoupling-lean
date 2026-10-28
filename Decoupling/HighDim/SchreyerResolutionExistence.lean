import Decoupling.HighDim.SchreyerResolutionAssembly
import Decoupling.HighDim.SchreyerResolutionColumns
import Decoupling.HighDim.SchreyerTerminationStep
import Decoupling.HighDim.SchreyerSyzygyGroebner

/-!
# A finite Schreyer free resolution of every polynomial submodule

For an arbitrary field K and arbitrary D, a submodule of a finite free
module over K[x₁,…,x_D] has an actual finite free matrix resolution of length
at most D-1 (natural subtraction). Each step constructs the whole actual
kernel from S-pairs, minimizes and sorts its leading terms, and removes one
more leading variable. The final family is independent by its distinct
leading positions. No homogeneous, infinite-field, projective-freeness, or
input Gröbner-basis hypothesis remains in the endpoint.

The construction is mathematical and noncomputable; its existence choices
are not claimed to implement an executable Buchberger program or a runtime
complexity bound.
-/
namespace Decoupling.HighDim.SchreyerResolution
open SchreyerModule SchreyerSyzygy SchreyerTermination
noncomputable section
variable {K : Type*} [Field K] {D : ℕ}

/-- The inductive length bound is measured by the number of remaining
leading variables, rather than by an abstract projective dimension. -/
theorem exists_data_of_missing (n k r s : ℕ) (hkn : k+n=D-1)
    (o : ModuleOrder D r) (N : Submodule (Poly K D) (Vec K D r))
    (G : Fin s → Vec K D r) (t : Fin s → Term D r)
    (hG : IsGroebnerBasis o G N) (hmin : IsMinimal o G)
    (hlead : ∀ i,IsLeading o (G i) (t i))
    (hsort : ∀ i j,i<j → (t i).2=(t j).2 → LexGE (t i).1 (t j).1)
    (hmiss : ∀ i,MissingPrefix k (t i).1) : Nonempty (Data N n) := by
  induction n generalizing k r s with
  | zero =>
    have hk : k=D-1 := by omega
    subst k
    have hker : LinearMap.ker (columnMatrix G).mulVecLin=⊥ := by
      rw [columnMatrix_mulVecLin]
      exact terminal_kernel_eq_bot o G t hmin hlead hmiss
    exact ⟨terminal (columnMatrix G) (columnMatrix_range_of_groebner hG) hker⟩
  | succ n ih =>
    obtain ⟨a,S,hS,hpair,_⟩ := exists_kernel_groebner hG t hlead
    obtain ⟨b,H,u,hH,hHmin,hHlead,hHsort,hHmiss⟩ :=
      next_minimal_missing o G t hsort hmiss S hS hpair
    obtain ⟨A⟩ := ih (k+1) s b (by omega) (inducedOrder o t)
      (LinearMap.ker (columnMap G)) H u hH hHmin hHlead hHsort hHmiss
    have A' : Data (LinearMap.ker (columnMatrix G).mulVecLin) n := by
      simpa only [columnMatrix_mulVecLin] using A
    exact ⟨prepend (columnMatrix G) (columnMatrix_range_of_groebner hG) A'⟩

/-- Unconditional Schreyer existence over any field, in the original D variables. -/
theorem exists_data {r : ℕ} (N : Submodule (Poly K D) (Vec K D r)) :
    Nonempty (Data N (D-1)) := by
  let o : ModuleOrder D r := initialOrder MonomialOrder.lex r
  obtain ⟨s,G,t,hG,hmin,hlead,hsort⟩ := exists_sorted_minimal_groebner o N
  exact exists_data_of_missing (D-1) 0 r s (by omega) o N G t hG hmin hlead hsort
    (fun i => missingPrefix_zero (t i).1)

/-- Chosen actual matrix data, with exactness and the D-1 cutoff proved above. -/
def data {r : ℕ} (N : Submodule (Poly K D) (Vec K D r)) : Data N (D-1) :=
  Classical.choice (exists_data N)

end
end Decoupling.HighDim.SchreyerResolution
