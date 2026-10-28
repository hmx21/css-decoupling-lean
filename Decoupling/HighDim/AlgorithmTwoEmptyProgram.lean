import Decoupling.HighDim.AlgorithmTwoPipelineOutput
import Decoupling.HighDim.AlgorithmTwoPipelineZero
import Decoupling.HighDim.PhysicalIsomorphism

/-!
# HD012 zero-input execution and its actual empty physical action

The empty branch does not enumerate the exponent box. It returns a
literal empty word and zero ancillary ranks. The native and physical
statements below concern that same output.
-/
namespace Decoupling.HighDim.AlgorithmTwo
open ArithmeticCost AlgorithmTwoPipeline

def emptyProgram (K : Type) (D : ℕ) : Work K (RuntimeOutput K D) :=
  Work.pure (RuntimeOutput.empty K D)

@[simp] theorem emptyProgram_cost (K : Type) (D : ℕ) : (emptyProgram K D).cost = 0 := rfl
@[simp] theorem emptyProgram_depth (K : Type) (D : ℕ) :
    (emptyProgram K D).value.gates.length = 0 := rfl
@[simp] theorem emptyProgram_sourceAncillas (K : Type) (D : ℕ) :
    (emptyProgram K D).value.sourceAncillas = 0 := rfl
@[simp] theorem emptyProgram_targetAncillas (K : Type) (D : ℕ) :
    (emptyProgram K D).value.targetAncillas = 0 := rfl

variable {K : Type} [Field K] {D L : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem emptyProgram_native (coords : StableFree.Coordinates C)
    [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)] (hz : inputRank coords L = 0) :
    Nonempty (HomotopyEquiv C (emptyTarget K D)) :=
  ⟨emptyEquivalence coords hz⟩

/-- On the actual zero-dimensional physical coordinate module every
check family generates the trivial subgroup. The literal empty returned
word therefore transports both actual stabilizer families. -/
theorem emptyProgram_transports {a b c d : ℕ}
    (BC : Matrix (Fin 0) (Fin a) (Laurent K D))
    (HC : Matrix (Fin b) (Fin 0) (Laurent K D))
    (BT : Matrix (Fin 0) (Fin c) (Laurent K D))
    (HT : Matrix (Fin d) (Fin 0) (Laurent K D)) :
    PhysicalIsomorphism.Transports (emptyProgram K D).value.gates (Equiv.refl (Fin 0)) HC HT BC BT := by
  change PhysicalIsomorphism.Transports ([] : List (Circuit.Layer K D (Fin 0)))
    (Equiv.refl (Fin 0)) HC HT BC BT
  unfold PhysicalIsomorphism.Transports PhysicalIsomorphism.inImage
  constructor <;> intro v <;> constructor <;> intro _ <;>
    exact ⟨0,Subsingleton.elim _ _⟩

theorem emptyProgram_local : PhysicalIsomorphism.LocalCircuit (emptyProgram K D).value.gates :=
  PhysicalIsomorphism.localCircuit _

end Decoupling.HighDim.AlgorithmTwo
