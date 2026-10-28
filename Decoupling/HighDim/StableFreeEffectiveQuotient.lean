import Decoupling.HighDim.StableFreeEffectiveAbsorb

/-! Exact presentations for the two stable cokernels passed to comparison lifting. -/
namespace Decoupling.HighDim.StableFree.Effective
open Matrix
universe u
variable {R : Type u} [CommRing R] {N : ModuleCat.{u} R} {n r : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Actual relations, with zero coordinates in the adjoined free block. -/
def stabilizedRelations (D : Matrix (Fin n) (Fin r) R) (k : ℕ) : Matrix (Fin (n+k)) (Fin r) R :=
  rowBlocks D 0

theorem stabilizedQuotient_surjective (π : Power R n →ₗ[R] N) (hπ : Function.Surjective π) (k : ℕ) :
    Function.Surjective (stabilizedQuotient π k) := by
  rintro ⟨x,y⟩
  obtain ⟨a,rfl⟩ := hπ x
  exact ⟨powerAdd n k (a,y),stabilizedQuotient_apply π k a y⟩

/-- The new presentation kernel is precisely the original relation module
with zero in the actual free ancilla coordinates. -/
theorem stabilizedQuotient_kernel (π : Power R n →ₗ[R] N)
    (D : Matrix (Fin n) (Fin r) R) (hD : LinearMap.ker π = LinearMap.range D.mulVecLin) (k : ℕ) :
    LinearMap.ker (stabilizedQuotient π k) = LinearMap.range (stabilizedRelations D k).mulVecLin := by
  ext x
  obtain ⟨⟨x,y⟩,rfl⟩ := (powerAdd (R := R) n k).surjective x
  change stabilizedQuotient π k (powerAdd n k (x,y)) = 0 ↔
    ∃ z, stabilizedRelations D k *ᵥ z = powerAdd n k (x,y)
  rw [stabilizedQuotient_apply]
  constructor
  · intro he
    have hx : x ∈ LinearMap.ker π := congrArg Prod.fst he
    have hy : y = 0 := congrArg Prod.snd he
    rw [hD] at hx
    obtain ⟨z,hz⟩ := hx
    change D *ᵥ z = x at hz
    refine ⟨z,?_⟩
    rw [stabilizedRelations,rowBlocks_mulVec,Matrix.zero_mulVec,hz,hy]
  · rintro ⟨z,hz⟩
    rw [stabilizedRelations,rowBlocks_mulVec,Matrix.zero_mulVec] at hz
    have hp := (powerAdd (R := R) n k).injective hz
    have hx : x ∈ LinearMap.range D.mulVecLin := ⟨z,congrArg Prod.fst hp⟩
    rw [←hD] at hx
    exact Prod.ext hx (congrArg Prod.snd hp).symm

end Decoupling.HighDim.StableFree.Effective
