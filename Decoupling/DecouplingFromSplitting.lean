import Decoupling.SplitAssembly
import Decoupling.StandardTarget
import Decoupling.Comparison
import Decoupling.PhysicalIsomorphism
import Decoupling.BlockCircuit

/-!
# Stable decoupling constructed from a split syndrome extension

This assembles Sections III–IV from their remaining upstream inputs: an
actual CSS free resolution, identifications of its two cohomology layers
with the actual trivial translation modules, and vanishing of the genuine
Yoneda obstruction. The augmentation isomorphism, all four comparison
identities, both stabilized stabilizer-image identities, and a finite CNOT
circuit are conclusions.

The target is the direction-first standard target of `StandardTarget`.
Its free `h = cX - t₂` factor occurs only in degree zero. Source and target
physical coordinates have opposite sum orders, so circuit matrices use the
explicit equivalence `speciesOrder` to put both in the target species order.
The Z action is `U` in those coordinates; the X action is its inverse dagger.

This theorem does not assert the upstream finite-free-resolution existence
or the coarse-graining argument which supplies the layer identifications and
vanishing obstruction. Circuit semantics are the proved cellwise Pauli-support
actions of CNOT families, with finite depth and finite displacement bounds.
-/

namespace Decoupling.DecouplingFromSplitting

open Matrix Stabilization PhysicalIsomorphism EvaluationLinear

noncomputable section

-- The concrete nested sums have larger instance trees than abstract finite indices.
set_option synthInstance.maxSize 512

abbrev Target₀ (cX t₁ t₂ : ℕ) := StandardTarget.I₀ t₁ (cX - t₂) t₂
abbrev Target₁ (t₁ t₂ : ℕ) := StandardTarget.I₁ t₁ t₂
abbrev Target₂ (t₁ t₂ : ℕ) := StandardTarget.I₂ t₁ t₂

/-- Input qubits followed by the two product-state stabilizing blocks. -/
abbrev Source (q s cX t₁ t₂ : ℕ) :=
  (Fin q ⊕ Target₀ cX t₁ t₂) ⊕ (Target₁ t₁ t₂ ⊕ Fin s)

/-- Target qubits followed by the two product-state stabilizing blocks. -/
abbrev Target (q s cX t₁ t₂ : ℕ) :=
  (Target₁ t₁ t₂ ⊕ Fin s) ⊕ (Fin q ⊕ Target₀ cX t₁ t₂)

/-- The two matrix coordinate orders use exactly the same species. -/
def speciesOrder (q s cX t₁ t₂ : ℕ) :
    Source q s cX t₁ t₂ ≃ Target q s cX t₁ t₂ :=
  Equiv.sumComm _ _

abbrev Comparison (q s cX t₁ t₂ : ℕ) :=
  ComparisonData R (Fin s) (Fin q) (Target₀ cX t₁ t₂) (Target₁ t₁ t₂)

variable {q s r : ℕ} (c : CSS.Checks q s r) (cX t₁ t₂ : ℕ)

/-- The actual stabilized input Z generators of Eq. (63). -/
def inputZ : Matrix (Source q s cX t₁ t₂) (Fin r ⊕ (Target₁ t₁ t₂ ⊕ Fin s)) R :=
  Zhat (dagger c.H_Z)

/-- The actual stabilized standard Z generators, with the two Koszul species. -/
def targetZ : Matrix (Target q s cX t₁ t₂)
    (Target₂ t₁ t₂ ⊕ (Fin q ⊕ Target₀ cX t₁ t₂)) R :=
  Ztilde (StandardTarget.D₂ t₁ t₂)

/-- All output data and certificates of the downstream decoupling theorem.
No positive-rank condition is imposed on any input or target index type. -/
structure Certificate where
  layer₂_le_cover : t₂ ≤ cX
  β : StandardTarget.Nstd t₁ (cX - t₂) t₂ ≃ₗ[R] c.N
  comparison : Comparison q s cX t₁ t₂
  input_d₁ : comparison.d₁ = c.H_X
  target_d₁ : comparison.td₁ = StandardTarget.D₁ t₁ (cX - t₂) t₂
  augmentation_square :
    (LinearMap.range c.H_X.mulVecLin).mkQ.comp comparison.φ₀.mulVecLin =
      β.toLinearMap.comp (StandardTarget.ε t₁ (cX - t₂) t₂)
  inverse : comparison.U * comparison.Uinv = 1 ∧ comparison.Uinv * comparison.U = 1
  physical_square : comparison.H_X_tilde * comparison.U = comparison.Ψ₀ * comparison.H_X_hat
  z_image : ∀ v,
    (∃ z, comparison.U *ᵥ (inputZ c cX t₁ t₂ *ᵥ z) = v) ↔
      Certificates.inImage (targetZ (q := q) (s := s) cX t₁ t₂) v
  x_image : ∀ v,
    (∃ z, dagger comparison.Uinv *ᵥ (dagger comparison.H_X_hat *ᵥ z) = v) ↔
      Certificates.inImage (dagger comparison.H_X_tilde) v
  circuit : List (Circuit.CNOT (Target q s cX t₁ t₂))
  circuit_z : Circuit.zAction circuit =
    comparison.U.submatrix id (speciesOrder q s cX t₁ t₂).symm
  circuit_x : Circuit.xAction circuit =
    dagger (comparison.Uinv.submatrix (speciesOrder q s cX t₁ t₂).symm id)
  depth : ℕ
  range : ℕ
  depth_eq : depth = circuit.length
  range_le : ∀ gate ∈ circuit, ∀ i : Fin 3, (gate.displacement i).natAbs ≤ range

variable {c cX t₁ t₂}

/-- Construct the full stable matrix and circuit conclusion from splitting.
The only upstream inputs beyond the CSS checks/topological condition are the
specified free resolution, the actual two layer identifications, and `κ = 0`.
In particular `β`, comparison maps, stabilized exactness and a circuit are
not hypotheses. -/
theorem exists_certificate (hTop : c.Topological)
    (h : ResolutionExt.CSSResolution c cX)
    (e₁ : Trivial t₁ ≃ₗ[R] h.cochain.C1)
    (e₂ : h.cochain.C2 ≃ₗ[R] Trivial t₂)
    (hκ : h.cochain.κ = 0) : Nonempty (Certificate c cX t₁ t₂) := by
  let β := SplitAssembly.augmentationIsoOfκZero h.cochain hκ e₁ e₂
  have exactF : LinearMap.range c.H_X.mulVecLin = LinearMap.ker h.cochain.ε := by
    exact (LinearMap.range c.H_X.mulVecLin).ker_mkQ.symm
  obtain ⟨d, hdF, hdG, hφ, _⟩ := Comparison.exists_comparisonData
    c.H_X (StandardTarget.D₁ t₁ (cX - t₂) t₂)
    h.cochain.ε (StandardTarget.ε t₁ (cX - t₂) t₂)
    (LinearMap.range c.H_X.mulVecLin).mkQ_surjective
    (StandardTarget.ε_surjective t₁ (cX - t₂) t₂)
    exactF (StandardTarget.exact_augmentation_matrix t₁ (cX - t₂) t₂) β
  have hF : ∀ v, d.d₁ *ᵥ v = 0 ↔ ∃ z, dagger c.H_Z *ᵥ z = v := by
    intro v
    rw [hdF]
    exact c.exact_X hTop v
  have hG : ∀ v, d.td₁ *ᵥ v = 0 ↔ ∃ z, StandardTarget.D₂ t₁ t₂ *ᵥ z = v := by
    intro v
    rw [hdG]
    change v ∈ LinearMap.ker (StandardTarget.D₁ t₁ (cX - t₂) t₂).mulVecLin ↔
      v ∈ LinearMap.range (StandardTarget.D₂ t₁ t₂).mulVecLin
    rw [StandardTarget.exact_physical_matrix t₁ (cX - t₂) t₂]
  obtain ⟨hinv, hz, hx⟩ := stable_physical_isomorphism d
    (dagger c.H_Z) (StandardTarget.D₂ t₁ t₂) hF hG
  obtain ⟨word, hwz, hwx, depth, range, hd, hr⟩ := Circuit.block_circuit
    d.L₁ d.M₁ (speciesOrder q s cX t₁ t₂)
  exact ⟨{
    layer₂_le_cover := ExplicitSplitting.second_layer_rank_le h.cochain e₂
    β := β
    comparison := d
    input_d₁ := hdF
    target_d₁ := hdG
    augmentation_square := hφ
    inverse := hinv
    physical_square := d.physical_square
    z_image := hz
    x_image := hx
    circuit := word
    circuit_z := hwz
    circuit_x := hwx
    depth := depth
    range := range
    depth_eq := hd
    range_le := hr
  }⟩

/-- A chosen complete output, obtained from the proved existence theorem. -/
def construct (hTop : c.Topological)
    (h : ResolutionExt.CSSResolution c cX)
    (e₁ : Trivial t₁ ≃ₗ[R] h.cochain.C1)
    (e₂ : h.cochain.C2 ≃ₗ[R] Trivial t₂)
    (hκ : h.cochain.κ = 0) : Certificate c cX t₁ t₂ :=
  Classical.choice (exists_certificate hTop h e₁ e₂ hκ)

namespace Certificate

variable (out : Certificate c cX t₁ t₂)

/-- The output circuit sends the stabilized input Z image onto the target Z
image, with the input species written in the common circuit coordinate order. -/
theorem circuit_z_image (v : Target q s cX t₁ t₂ → R) :
    (∃ z, Circuit.zAction out.circuit *ᵥ
      ((inputZ c cX t₁ t₂).submatrix (speciesOrder q s cX t₁ t₂).symm id *ᵥ z) = v) ↔
      Certificates.inImage (targetZ (q := q) (s := s) cX t₁ t₂) v := by
  rw [out.circuit_z]
  simpa only [Matrix.mulVec_mulVec, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id] using out.z_image v

/-- The same physical circuit sends the stabilized input X image onto the
target X image, with the manuscript's inverse-dagger convention. -/
theorem circuit_x_image (v : Target q s cX t₁ t₂ → R) :
    (∃ z, Circuit.xAction out.circuit *ᵥ
      ((dagger out.comparison.H_X_hat).submatrix
        (speciesOrder q s cX t₁ t₂).symm id *ᵥ z) = v) ↔
      Certificates.inImage (dagger out.comparison.H_X_tilde) v := by
  rw [out.circuit_x]
  change (∃ z, (dagger out.comparison.Uinv).submatrix
      id (speciesOrder q s cX t₁ t₂).symm *ᵥ
      ((dagger out.comparison.H_X_hat).submatrix
        (speciesOrder q s cX t₁ t₂).symm id *ᵥ z) = v) ↔ _
  simpa only [Matrix.mulVec_mulVec, Matrix.submatrix_mul_equiv,
    Matrix.submatrix_id_id] using out.x_image v

/-- Each element of the finite output list is a layer of disjoint physical CNOTs. -/
theorem circuit_layer_disjoint (gate : Circuit.CNOT (Target q s cX t₁ t₂))
    {n m : Translation} (hnm : n ≠ m) :
    gate.source n ≠ gate.source m ∧ gate.source n ≠ gate.destination m ∧
    gate.destination n ≠ gate.source m ∧ gate.destination n ≠ gate.destination m :=
  gate.disjoint_gates hnm

/-- The output circuit preserves the actual Laurent Pauli pairing. -/
theorem circuit_preserves_pairing :
    dagger (Circuit.xAction out.circuit) * Circuit.zAction out.circuit = 1 :=
  Circuit.circuit_preserves_pairing out.circuit

end Certificate

end
end Decoupling.DecouplingFromSplitting
