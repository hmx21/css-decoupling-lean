import Decoupling.PeriodicCircuit
import Decoupling.ExplicitMain

/-!
# Actual finite-periodic stabilizer conjugation for the final certificate

For every positive period, every Laurent generator combination specializes to
an actual finite binary generator combination. Equality of generator images is
transported by matrix factors, without assuming the periodic quotient is flat.
The literal output circuit's complex unitary conjugates the entire pure-X and
pure-Z stabilizer families exactly. The original depth/range bounds apply to
all periods. In the final main-theorem wrappers, L is measured in the final
retained lattice: if its spacing is 2n in the original lattice, the compatible
original period is 2nL. No arbitrary incompatible original-period claim is made.
-/

namespace Decoupling.PeriodicDecoupling

open Matrix PeriodicLaurent PeriodicCircuit PauliUnitary DecouplingFromSplitting

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option synthInstance.maxSize 2048

variable (L : ℕ) [NeZero L]

section Image

variable {ι k t : Type*} [Fintype ι] [DecidableEq ι]
  [Fintype k] [Fintype t] [DecidableEq k] [DecidableEq t]
  (c : List (Circuit.CNOT ι)) (D : Matrix ι k R) (E : Matrix ι t R)

/-- Every pure-Z stabilizer operator, including arbitrary products of checks,
is transported to the exact target family by the actual finite unitary. -/
theorem conjugate_Z_image
    (h : ∀ v, (∃ z, Circuit.zAction c *ᵥ (D *ᵥ z) = v) ↔ ∃ w, E *ᵥ w = v) :
    Set.range (fun z => (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) *
      Z (matrix L D *ᵥ z) * (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ)ᴴ) =
      Set.range (fun w => Z (matrix L E *ᵥ w)) := by
  have hp (v) : (∃ z, matrix L (Circuit.zAction c) *ᵥ (matrix L D *ᵥ z) = v) ↔
      ∃ w, matrix L E *ᵥ w = v := by
    simpa only [matrix_mul, Matrix.mulVec_mulVec] using image_iff L (Circuit.zAction c * D) E
      (fun v => by simpa only [Matrix.mulVec_mulVec] using h v) v
  ext O
  constructor
  · rintro ⟨z, hz⟩
    dsimp only at hz
    rw [conjugate_Z_word L c] at hz
    obtain ⟨w, hw⟩ := (hp _).mp ⟨z, rfl⟩
    refine ⟨w, ?_⟩
    dsimp only
    rw [hw]
    exact hz
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := (hp _).mpr ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    dsimp only
    rw [conjugate_Z_word L c, hz]
    exact hw

/-- The corresponding exact pure-X stabilizer family equality. -/
theorem conjugate_X_image
    (h : ∀ v, (∃ z, Circuit.xAction c *ᵥ (D *ᵥ z) = v) ↔ ∃ w, E *ᵥ w = v) :
    Set.range (fun z => (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ) *
      X (matrix L D *ᵥ z) * (unitary L c : Matrix (Bits (Site L ι)) (Bits (Site L ι)) ℂ)ᴴ) =
      Set.range (fun w => X (matrix L E *ᵥ w)) := by
  have hp (v) : (∃ z, matrix L (Circuit.xAction c) *ᵥ (matrix L D *ᵥ z) = v) ↔
      ∃ w, matrix L E *ᵥ w = v := by
    simpa only [matrix_mul, Matrix.mulVec_mulVec] using image_iff L (Circuit.xAction c * D) E
      (fun v => by simpa only [Matrix.mulVec_mulVec] using h v) v
  ext O
  constructor
  · rintro ⟨z, hz⟩
    dsimp only at hz
    rw [conjugate_X_word L c] at hz
    obtain ⟨w, hw⟩ := (hp _).mp ⟨z, rfl⟩
    refine ⟨w, ?_⟩
    dsimp only
    rw [hw]
    exact hz
  · rintro ⟨w, hw⟩
    obtain ⟨z, hz⟩ := (hp _).mpr ⟨w, rfl⟩
    refine ⟨z, ?_⟩
    dsimp only
    rw [conjugate_X_word L c, hz]
    exact hw

end Image

section Certificate

variable {q s r cX t₁ t₂ : ℕ} {c : CSS.Checks q s r}
  (out : Certificate c cX t₁ t₂)

abbrev InputZ (_out : Certificate c cX t₁ t₂) := (inputZ c cX t₁ t₂).submatrix (speciesOrder q s cX t₁ t₂).symm id
abbrev InputX := (dagger out.comparison.H_X_hat).submatrix
  (speciesOrder q s cX t₁ t₂).symm id
abbrev TargetZ (_out : Certificate c cX t₁ t₂) := targetZ (q := q) (s := s) cX t₁ t₂
abbrev TargetX := dagger out.comparison.H_X_tilde

abbrev Qubits (_out : Certificate c cX t₁ t₂) := Target q s cX t₁ t₂ × Cell L

/-- The certificate's entire Z stabilizer family is conjugated without phase. -/
theorem certificate_Z :
    Set.range (fun z => (unitary L out.circuit : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ) *
      Z (matrix L (InputZ out) *ᵥ z) *
      (unitary L out.circuit : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ)ᴴ) =
      Set.range (fun w => Z (matrix L (TargetZ out) *ᵥ w)) :=
  conjugate_Z_image L out.circuit (InputZ out) (TargetZ out) out.circuit_z_image

/-- The same literal output unitary conjugates the entire X stabilizer family. -/
theorem certificate_X :
    Set.range (fun z => (unitary L out.circuit : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ) *
      X (matrix L (InputX out) *ᵥ z) *
      (unitary L out.circuit : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ)ᴴ) =
      Set.range (fun w => X (matrix L (TargetX out) *ᵥ w)) :=
  conjugate_X_image L out.circuit (InputX out) (TargetX out) out.circuit_x_image

/-- A finite-periodic physical interpretation of a completed Laurent certificate. -/
structure Semantics where
  operation : Matrix.unitaryGroup (Bits (Qubits L out)) ℂ
  operation_eq : operation = unitary L out.circuit
  x_stabilizers : Set.range (fun z => (operation : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ) * X (matrix L (InputX out) *ᵥ z) *
    (operation : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ)ᴴ) = Set.range (fun w => X (matrix L (TargetX out) *ᵥ w))
  z_stabilizers : Set.range (fun z => (operation : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ) * Z (matrix L (InputZ out) *ᵥ z) *
    (operation : Matrix (Bits (Qubits L out)) (Bits (Qubits L out)) ℂ)ᴴ) = Set.range (fun w => Z (matrix L (TargetZ out) *ᵥ w))
  depth : out.depth = out.circuit.length
  locality : ∀ g ∈ out.circuit, ∀ p : Cell L,
    WithinRange L out.range (source L g p).2 (destination L g p).2

/-- The original certificate supplies all finite-periodic physical fields. -/
def semantics : Semantics L out where
  operation := unitary L out.circuit
  operation_eq := rfl
  x_stabilizers := certificate_X L out
  z_stabilizers := certificate_Z L out
  depth := out.depth_eq
  locality g hg _p := ⟨g.displacement, rfl, fun i => out.range_le g hg i⟩

end Certificate

/-- Direct physical finite-periodic interpretation of the certificate selected
from exactly the manuscript's original hypotheses. The period L is in the
final retained lattice, hence corresponds to original period 2nL. -/
def fromMain {q s r : ℕ} (c : CSS.Checks q s r) (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 1))]
    [FiniteDimensional (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 2))] :
    Semantics L (MainTheorem.certificate c hTop).2.2.certificate :=
  semantics L (MainTheorem.certificate c hTop).2.2.certificate


/-- The same finite-periodic physical interpretation retains the exact selected
Appendix C matrices and comparison map in `ExplicitMain`'s output. Again L
is the period in that output's final retained lattice. -/
def fromExplicitMain {q s r : ℕ} (c : CSS.Checks q s r) (hTop : c.Topological)
    [FiniteDimensional (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 1))]
    [FiniteDimensional (ZMod 2) (LayerTranslations.coefficients (LayerTranslations.layer c 2))] :
    Semantics L (ExplicitMain.construct c hTop).result.toResult.certificate :=
  semantics L (ExplicitMain.construct c hTop).result.toResult.certificate

end
end Decoupling.PeriodicDecoupling
