import Decoupling.HighDim.StableFreeEffectiveDense
import Decoupling.HighDim.StableFreeStageRepresentation
import Decoupling.HighDim.LaurentLinearSolverProgram

/-!
# Executable projective-lift solving with the complete Laurent solver

The actual coefficient compiler is followed by the proved complete Laurent
program. Its materialized output is decoded by pure array lookups. Known
solvability is derived from the actual module surjection and projective
retract, rather than supplied as a search-window or cost certificate.
-/

namespace Decoupling.HighDim.StableFree.Effective

open Matrix ArithmeticCost LaurentArithmetic
variable {K : Type*} [Field K] {D b c v rel k l : ℕ}
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

/-- Decode the free entries of the actual lift matrix. -/
def decodeLiftX (z : Vector (Dense K D c) ((k+rel)*l)) : DenseMatrix K D k l c :=
  Vector.ofFn fun i => Vector.ofFn fun j => z[liftUnknownEnumeration k rel l (.inl i,j)]

/-- Decode the finite relation witnesses. -/
def decodeLiftW (z : Vector (Dense K D c) ((k+rel)*l)) : DenseMatrix K D rel l c :=
  Vector.ofFn fun i => Vector.ofFn fun j => z[liftUnknownEnumeration k rel l (.inr i,j)]

theorem decodeLift_vector (z : Vector (Dense K D c) ((k+rel)*l)) :
    liftVector (matrixDenote (decodeLiftX z)) (matrixDenote (decodeLiftW z)) =
      (fun i => denote z[i]) ∘ liftUnknownEnumeration k rel l := by
  funext ij
  rcases ij with ⟨i|i,j⟩ <;>
    simp only [liftVector, decodeLiftX, decodeLiftW, matrixDenote,
      Fin.getElem_fin, Vector.getElem_ofFn, Fin.eta, Function.comp_apply] <;> rfl

/-- A genuine solution of the unflattened scalar system proves solvability
of the exact dense compiler output, through the canonical index equivalence. -/
theorem compiledLift_solvable
    (A : DenseMatrix K D v k b) (B : DenseMatrix K D v l b)
    (F : DenseMatrix K D v rel b) (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b)
    (hsol : ∃ z : LiftUnknowns k rel l → Laurent K D,
      liftCoefficients (matrixDenote A) (matrixDenote F) (matrixDenote E) (matrixDenote G) *ᵥ z =
        liftStack (matrixDenote B) 0 0) :
    ∃ z, matrixDenote (liftSystemProgram A F E G).value *ᵥ z =
      fun i => denote (liftRightDense (k := k) B)[i] := by
  obtain ⟨z,hz⟩ := hsol
  refine ⟨z ∘ (liftUnknownEnumeration k rel l).symm,?_⟩
  rw [liftSystemProgram_correct,liftRightDense_correct,Matrix.submatrix_mulVec_equiv]
  simpa only [Equiv.symm_symm, Function.comp_def, Equiv.symm_apply_apply] using
    congrArg (fun x => x ∘ (liftRowEnumeration v k l).symm) hz

/-- Any actual dense solution decodes into the original three matrix equations. -/
theorem decodedLift_equations
    (A : DenseMatrix K D v k b) (B : DenseMatrix K D v l b)
    (F : DenseMatrix K D v rel b) (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b)
    (z : Vector (Dense K D c) ((k+rel)*l))
    (hz : matrixDenote (liftSystemProgram A F E G).value *ᵥ (fun i => denote z[i]) =
      fun i => denote (liftRightDense (k := k) B)[i]) :
    matrixDenote A * matrixDenote (decodeLiftX z) - matrixDenote B =
        matrixDenote F * matrixDenote (decodeLiftW z) ∧
      matrixDenote E * matrixDenote (decodeLiftX z) = matrixDenote (decodeLiftX z) ∧
      matrixDenote (decodeLiftX z) * matrixDenote G = matrixDenote (decodeLiftX z) := by
  apply (liftEquation_iff _ _ _ _ _ _ _).mp
  rw [decodeLift_vector]
  rw [liftSystemProgram_correct,liftRightDense_correct,Matrix.submatrix_mulVec_equiv] at hz
  funext ij
  have hi := congrFun hz (liftRowEnumeration v k l ij)
  simpa only [Equiv.symm_symm, Function.comp_apply, Equiv.symm_apply_apply] using hi

variable [DecidableEq K]

/-- Complete, counted execution of one normalized projective-lift system.
The solvability proof is erased; the returned arrays come from the program's
actual `Option.get` result, not from Classical.choose. -/
def solveLiftProgram
    (A : DenseMatrix K D v k b) (B : DenseMatrix K D v l b)
    (F : DenseMatrix K D v rel b) (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b)
    (hsol : ∃ z : LiftUnknowns k rel l → Laurent K D,
      liftCoefficients (matrixDenote A) (matrixDenote F) (matrixDenote E) (matrixDenote G) *ᵥ z =
        liftStack (matrixDenote B) 0 0) :
    Work K (DenseMatrix K D k l (LaurentLinearSolver.outputBox D ((v+(k+k))*l) b) ×
      DenseMatrix K D rel l (LaurentLinearSolver.outputBox D ((v+(k+k))*l) b)) :=
  let compiled := liftSystemProgram A F E G
  let solution := LaurentLinearSolver.solveOfSolvable compiled.value (liftRightDense (k := k) B)
    (compiledLift_solvable A B F E G hsol)
  Work.bind compiled fun _ => Work.bind solution fun z => Work.pure (decodeLiftX z,decodeLiftW z)

/-- Explicit bound includes all coefficient changes and the actual complete
Laurent solver, not an abstract cost assigned to a lifting oracle. -/
def liftSolveCost (D v rel k l b : ℕ) : ℕ :=
  (v*rel+k*k+l*l)*boxSize D b +
    LaurentLinearSolver.solveCost D ((v+(k+k))*l) ((k+rel)*l) b

theorem solveLiftProgram_cost
    (A : DenseMatrix K D v k b) (B : DenseMatrix K D v l b)
    (F : DenseMatrix K D v rel b) (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b)
    (hsol : ∃ z : LiftUnknowns k rel l → Laurent K D,
      liftCoefficients (matrixDenote A) (matrixDenote F) (matrixDenote E) (matrixDenote G) *ᵥ z =
        liftStack (matrixDenote B) 0 0) :
    (solveLiftProgram A B F E G hsol).cost ≤ liftSolveCost D v rel k l b := by
  unfold solveLiftProgram
  rw [Work.bind_cost,Work.bind_cost,Work.pure_cost,add_zero,liftSystemProgram_cost]
  exact Nat.add_le_add_left (LaurentLinearSolver.solveOfSolvable_cost _ _ _) _

theorem solveLiftProgram_correct
    (A : DenseMatrix K D v k b) (B : DenseMatrix K D v l b)
    (F : DenseMatrix K D v rel b) (E : DenseMatrix K D k k b) (G : DenseMatrix K D l l b)
    (hsol : ∃ z : LiftUnknowns k rel l → Laurent K D,
      liftCoefficients (matrixDenote A) (matrixDenote F) (matrixDenote E) (matrixDenote G) *ᵥ z =
        liftStack (matrixDenote B) 0 0) :
    let result := (solveLiftProgram A B F E G hsol).value
    matrixDenote A * matrixDenote result.1 - matrixDenote B = matrixDenote F * matrixDenote result.2 ∧
      matrixDenote E * matrixDenote result.1 = matrixDenote result.1 ∧
      matrixDenote result.1 * matrixDenote G = matrixDenote result.1 := by
  exact decodedLift_equations A B F E G _
    (LaurentLinearSolver.solveOfSolvable_correct _ _ (compiledLift_solvable A B F E G hsol))

end Decoupling.HighDim.StableFree.Effective
