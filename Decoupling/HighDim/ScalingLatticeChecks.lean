import Decoupling.HighDim.ScalingLatticeRingEquiv

/-!
# Actual finite check matrices after an arbitrary lattice-basis renaming

The matrices are the previously proved coset multiplication matrices, with
their retained coefficients renamed and their finite species enumerated.
Both topological equalities and the actual reduced quotient are transported.
-/

namespace Decoupling.HighDim.ScalingLattice

open CategoryTheory LatticeRestriction LatticePhysical Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

section Generic

variable {A B : Type} [CommRing A] [CommRing B] (ρ : A ≃+* B)
  {ι κ : Type} [Fintype ι] [Fintype κ]

local instance : RingHomInvPair ρ.toRingHom ρ.symm.toRingHom := RingHomInvPair.of_ringEquiv ρ
local instance : RingHomInvPair ρ.symm.toRingHom ρ.toRingHom := RingHomInvPair.of_ringEquiv_symm ρ

def vectorRename : (ι → A) ≃ₛₗ[ρ.toRingHom] (Fin (Fintype.card ι) → B) where
  toFun v i := ρ (v ((Fintype.equivFin ι).symm i))
  invFun v i := ρ.symm (v (Fintype.equivFin ι i))
  left_inv v := by ext i; simp
  right_inv v := by ext i; simp
  map_add' v w := by ext i; exact ρ.map_add _ _
  map_smul' a v := by ext i; exact ρ.map_mul _ _

def matrixRename (F : Matrix ι κ A) :
    Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card κ)) B :=
  fun i j => ρ (F ((Fintype.equivFin ι).symm i) ((Fintype.equivFin κ).symm j))

theorem matrixRename_mulVec (F : Matrix ι κ A) (v : κ → A) :
    matrixRename ρ F *ᵥ vectorRename ρ v = vectorRename ρ (F *ᵥ v) := by
  funext i
  change (∑ j : Fin (Fintype.card κ),
    ρ (F ((Fintype.equivFin ι).symm i) ((Fintype.equivFin κ).symm j)) *
      ρ (v ((Fintype.equivFin κ).symm j))) =
    ρ (∑ j : κ, F ((Fintype.equivFin ι).symm i) j * v j)
  simp only [← map_mul, ← map_sum]
  congr 1
  exact Fintype.sum_equiv (Fintype.equivFin κ).symm _ _ (fun _ => rfl)

theorem matrixRename_exact {ζ : Type} [Fintype ζ]
    (F : Matrix ι κ A) (G : Matrix κ ζ A)
    (h : ∀ v, F *ᵥ v = 0 ↔ ∃ z, G *ᵥ z = v) :
    ∀ v, matrixRename ρ F *ᵥ v = 0 ↔ ∃ z, matrixRename ρ G *ᵥ z = v := by
  intro v
  obtain ⟨v, rfl⟩ := (vectorRename ρ).surjective v
  rw [matrixRename_mulVec, (vectorRename ρ).map_eq_zero_iff, h]
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨vectorRename ρ z, matrixRename_mulVec ρ G z⟩
  · rintro ⟨z, hz⟩
    obtain ⟨z, rfl⟩ := (vectorRename ρ).surjective z
    rw [matrixRename_mulVec] at hz
    exact ⟨z, (vectorRename ρ).injective hz⟩

theorem matrixRename_range (F : Matrix ι κ A) :
    (LinearMap.range F.mulVecLin).map (vectorRename ρ).toLinearMap =
      LinearMap.range (matrixRename ρ F).mulVecLin := by
  ext v
  constructor
  · rintro ⟨v, ⟨z, rfl⟩, rfl⟩
    exact ⟨vectorRename ρ z, matrixRename_mulVec ρ F z⟩
  · rintro ⟨z, rfl⟩
    obtain ⟨z, rfl⟩ := (vectorRename ρ).surjective z
    exact ⟨F *ᵥ z, ⟨z, rfl⟩, (matrixRename_mulVec ρ F z).symm⟩

def quotientRename (F : Matrix ι κ A) :
    ((ι → A) ⧸ LinearMap.range F.mulVecLin) ≃ₛₗ[ρ.toRingHom]
      ((Fin (Fintype.card ι) → B) ⧸ LinearMap.range (matrixRename ρ F).mulVecLin) :=
  Submodule.Quotient.equiv _ _ (vectorRename ρ) (matrixRename_range ρ F)

/-- Bundle a semilinear coordinate change as a linear map from actual
scalar restriction, preserving its exact module structure. -/
def linearize {M N : Type} [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] (f : M ≃ₛₗ[ρ.toRingHom] N) :
    (RingChange.rename ρ).obj (ModuleCat.of A M) ≃ₗ[B] N where
  toFun m := f (show M from m)
  invFun n := f.symm n
  left_inv m := f.symm_apply_apply m
  right_inv n := f.apply_symm_apply n
  map_add' m n := f.map_add m n
  map_smul' b m := by
    change f (ρ.symm b • (show M from m)) = b • f (show M from m)
    have h := f.map_smulₛₗ (ρ.symm b) (show M from m)
    change f (ρ.symm b • (show M from m)) = ρ (ρ.symm b) • f (show M from m) at h
    rwa [ρ.apply_symm_apply] at h

end Generic

variable (K : Type) [CommRing K] {D : ℕ}
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)

def count (n : ℕ) : ℕ := Fintype.card (Fin n × Coset Λ)

def physicalMatrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    Matrix (Fin (count Λ m)) (Fin (count Λ n)) (Laurent K D) :=
  matrixRename (ringCoordinates K Λ e) (expandMatrix K Λ A)

omit [Λ.FiniteIndex] in
theorem matrixRename_dagger {ι κ : Type} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ (S K Λ)) :
    matrixRename (ringCoordinates K Λ e) (daggerS K Λ A) =
      dagger (matrixRename (ringCoordinates K Λ e) A) := by
  funext i j
  exact ringCoordinates_bar K Λ e _

@[simp] theorem physicalMatrix_dagger {m n : ℕ}
    (A : Matrix (Fin m) (Fin n) (Laurent K D)) :
    physicalMatrix K Λ e (dagger A) = dagger (physicalMatrix K Λ e A) := by
  rw [physicalMatrix, expandMatrix_dagger, matrixRename_dagger]
  rfl

/-- Actual coset-expanded, integer-basis-renamed finite CSS checks. -/
def physicalChecks {q s r : ℕ} (c : CSS.Checks K D q s r) :
    CSS.Checks K D (count Λ q) (count Λ s) (count Λ r) where
  H_X := physicalMatrix K Λ e c.H_X
  H_Z := physicalMatrix K Λ e c.H_Z

theorem physicalChecks_topological {q s r : ℕ} (c : CSS.Checks K D q s r)
    (hc : c.Topological) : (physicalChecks K Λ e c).Topological := by
  have hx := matrixRename_exact (ringCoordinates K Λ e) _ _
    (LatticeCompatibility.topological K Λ c hc).1
  have hz := matrixRename_exact (ringCoordinates K Λ e) _ _
    (LatticeCompatibility.topological K Λ c hc).2
  rw [matrixRename_dagger] at hx hz
  constructor
  · ext v
    exact hx v
  · ext v
    exact hz v

/-- The actual reduced Pauli quotient after basis renaming, not a separately
chosen module carrying the same dimensions. -/
def reducedRenameIso {q s r : ℕ} (c : CSS.Checks K D q s r) :
    (RingChange.rename (ringCoordinates K Λ e)).obj (LatticeCompatibility.reduced K Λ c) ≅
      Layers.reduced (physicalChecks K Λ e c) := by
  have h := linearize (ringCoordinates K Λ e)
    (quotientRename (ringCoordinates K Λ e)
      (daggerS K Λ (LatticeCompatibility.H_X K Λ c)))
  rw [matrixRename_dagger] at h
  exact h.toModuleIso

end
end Decoupling.HighDim.ScalingLattice
