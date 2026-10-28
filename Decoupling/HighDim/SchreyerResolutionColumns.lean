import Decoupling.HighDim.SchreyerResolutionData
import Decoupling.HighDim.SchreyerSyzygyMap
import Decoupling.HighDim.SchreyerGroebnerDivision

/-! # Actual matrix coordinates of a generating polynomial family -/
namespace Decoupling.HighDim.SchreyerResolution
open SchreyerModule SchreyerSyzygy Matrix
noncomputable section
variable {K : Type*} [Field K] {D r s : ℕ}

def columnMatrix (G : Fin s → Vec K D r) : Matrix (Fin r) (Fin s) (Poly K D) :=
  fun i j => G j i

theorem columnMatrix_mulVecLin (G : Fin s → Vec K D r) :
    (columnMatrix G).mulVecLin=columnMap G := by
  apply LinearMap.ext
  intro z
  funext i
  change (∑ j,G j i*z j)=(∑ j,z j • G j) i
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul,mul_comm]

theorem columnMap_range_of_groebner {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    {N : Submodule (Poly K D) (Vec K D r)} (hG : IsGroebnerBasis o G N) :
    LinearMap.range (columnMap G)=N := by
  apply le_antisymm
  · rintro f ⟨z,rfl⟩
    change (∑ i,z i • G i)∈N
    exact Submodule.sum_mem N (fun i _ => N.smul_mem _ (hG.mem i))
  · intro f hf
    obtain ⟨q,he,_⟩ := hG.standardRepresentation hf
    exact ⟨q,he.symm⟩

theorem columnMatrix_range_of_groebner {o : ModuleOrder D r} {G : Fin s → Vec K D r}
    {N : Submodule (Poly K D) (Vec K D r)} (hG : IsGroebnerBasis o G N) :
    LinearMap.range (columnMatrix G).mulVecLin=N := by
  rw [columnMatrix_mulVecLin]
  exact columnMap_range_of_groebner hG

end
end Decoupling.HighDim.SchreyerResolution
