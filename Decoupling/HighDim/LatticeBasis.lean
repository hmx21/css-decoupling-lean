import Decoupling.HighDim.Translations
import Mathlib.GroupTheory.IndexNSmul
import Mathlib.LinearAlgebra.FreeModule.PID
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Full-rank retained lattices and the prescribed further coarse-graining

Source: `drafts/main.tex` 624–628 and 664–670. A finite-index subgroup of
integer translations has a genuine Z-basis of length D. The further lattice
is its image under multiplication by a natural number, with no axis-alignment
assumption. These arithmetic results do not themselves assert profile splitting.
-/

namespace Decoupling.HighDim.LatticeBasis
open Module
noncomputable section

variable {D : ℕ} (Λ : AddSubgroup (Translation D))

instance latticeFinite : Module.Finite ℤ Λ :=
  inferInstanceAs (Module.Finite ℤ Λ.toIntSubmodule)

instance latticeFree : Module.Free ℤ Λ :=
  Module.free_of_finite_type_torsion_free'

theorem finrank_eq [Λ.FiniteIndex] : Module.finrank ℤ Λ = D := by
  rw [AddSubgroup.finrank_eq_of_finiteIndex]
  simp [Translation]

def basis [Λ.FiniteIndex] : Basis (Fin D) ℤ Λ :=
  Module.finBasisOfFinrankEq ℤ Λ (finrank_eq Λ)

def coordinates [Λ.FiniteIndex] : Λ ≃+ Translation D := (basis Λ).equivFun.toAddEquiv

def renameRing (K : Type*) [CommRing K] [Λ.FiniteIndex] :
    AddMonoidAlgebra K Λ ≃+* Laurent K D :=
  AddMonoidAlgebra.mapDomainRingEquiv K (coordinates Λ)

def scaled (n : ℕ) : AddSubgroup (Translation D) :=
  Λ.map (nsmulAddMonoidHom (α := Translation D) n)

theorem scaled_le (n : ℕ) : scaled Λ n ≤ Λ := by
  rintro a ⟨b, hb, rfl⟩
  exact Λ.nsmul_mem hb n

@[simp] theorem scaled_one : scaled Λ 1 = Λ := by
  ext a
  simp [scaled]

theorem scaled_index [Λ.FiniteIndex] (n : ℕ) :
    (scaled Λ n).index = n ^ D * Λ.index := by
  rw [← AddSubgroup.relIndex_mul_index (scaled_le Λ n)]
  rw [scaled, AddSubgroup.relIndex_map_nsmul]
  rw [finrank_eq Λ]

theorem scaled_finiteIndex [Λ.FiniteIndex] {n : ℕ} (hn : n ≠ 0) :
    (scaled Λ n).FiniteIndex where
  index_ne_zero := by
    rw [scaled_index]
    exact mul_ne_zero (pow_ne_zero D hn) AddSubgroup.FiniteIndex.index_ne_zero

/-- Exactly p^(max(m-1,0)) Lambda0; natural subtraction implements the max. -/
def finalLattice (p m : ℕ) : AddSubgroup (Translation D) := scaled Λ (p ^ (m - 1))

theorem finalLattice_finiteIndex [Λ.FiniteIndex] {p : ℕ} (hp : p.Prime) (m : ℕ) :
    (finalLattice Λ p m).FiniteIndex :=
  scaled_finiteIndex Λ (pow_ne_zero _ hp.ne_zero)

@[simp] theorem finalLattice_zero (p : ℕ) : finalLattice Λ p 0 = Λ := by
  simp [finalLattice]

@[simp] theorem finalLattice_one (p : ℕ) : finalLattice Λ p 1 = Λ := by
  simp [finalLattice]

end
end Decoupling.HighDim.LatticeBasis
