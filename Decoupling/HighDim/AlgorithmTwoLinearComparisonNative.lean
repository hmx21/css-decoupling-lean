import Decoupling.HighDim.AlgorithmTwoLinearComparisonGraded

/-!
# Actual finite solver output as native maps

The comparison system is solvable whenever a native prescribed map exists;
that existence is supplied by the derived-category lifting theorem in the
final toric specialization. The executed result is rebuilt as a native
cochain map with precisely the prescribed values. No solution matrix is
chosen by the semantic existence proof.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open CategoryTheory Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
variable {K : Type} [Field K] [DecidableEq K] {D n m k h : ℕ}
variable {T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

structure Represented (C : CochainComplex (ModuleCat (Laurent K D)) ℤ) (n h : ℕ) where
  coordinates : Coordinates C n
  differential : LaurentArithmetic.DenseMatrix K D n n h
  represents : coordinates.RepresentsDifferential (LaurentArithmetic.matrixDenote differential)

structure Prescribed (cT : Coordinates T m) (cC : Coordinates C n) (k h : ℕ) where
  degrees : Vector ℤ k
  source : ∀ i : Fin k, T.X (degrees.get i)
  target : ∀ i : Fin k, C.X (degrees.get i)
  sourceArray : LaurentArithmetic.DenseMatrix K D m k h
  targetArray : LaurentArithmetic.DenseMatrix K D n k h
  source_eq : ∀ i, (fun a => LaurentArithmetic.matrixDenote sourceArray a i) = cT.embed (degrees.get i) (source i)
  target_eq : ∀ i, (fun a => LaurentArithmetic.matrixDenote targetArray a i) = cC.embed (degrees.get i) (target i)

namespace Prescribed
noncomputable def Realized {cT : Coordinates T m} {cC : Coordinates C n}
    (p : Prescribed cT cC k h) (f : T ⟶ C) : Prop :=
  ∀ i, (f.f (p.degrees.get i)).hom (p.source i) = p.target i
end Prescribed

omit [DecidableEq K] in
private theorem cochainMatrix_values (cT : Coordinates T m) (cC : Coordinates C n)
    (p : Prescribed cT cC k h) (f : T ⟶ C) (hf : p.Realized f) :
    cochainMatrix cT cC f * LaurentArithmetic.matrixDenote p.sourceArray =
      LaurentArithmetic.matrixDenote p.targetArray := by
  funext a i
  change (cochainMatrix cT cC f *ᵥ (fun b => LaurentArithmetic.matrixDenote p.sourceArray b i)) a = _
  rw [p.source_eq, cochainMatrix_mulVec, hf]
  exact congrFun (p.target_eq i).symm a

omit [DecidableEq K] in
theorem comparison_exists (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) :
    ∃ X, (comparisonInput t.differential c.differential p.sourceArray p.targetArray
      t.coordinates.degree c.coordinates.degree).value.Satisfied X := by
  obtain ⟨f,hf⟩ := hex
  refine ⟨cochainMatrix t.coordinates c.coordinates f, ?_⟩
  apply (comparisonInput_correct _ _ _ _ _ _ _).mpr
  exact ⟨cochainMatrix_comm _ _ _ _ t.represents c.represents f,
    cochainMatrix_values _ _ p f hf, cochainMatrix_homogeneous _ _ f⟩

/-- The only computational input is the differential/top/cocycle arrays
and integer degree labels. Native existence rules out the failure branch. -/
def comparisonProgram (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) :
    Work K (LaurentArithmetic.DenseMatrix K D n m (resultBox D n m k h)) :=
  let input := comparisonInput t.differential c.differential p.sourceArray p.targetArray
    t.coordinates.degree c.coordinates.degree
  let result := solveOfExists input.value (comparison_exists t c p hex)
  { value := result.value
    trace := input.trace ++ result.trace }

theorem comparisonProgram_correct (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) :
    LaurentArithmetic.matrixDenote c.differential * LaurentArithmetic.matrixDenote (comparisonProgram t c p hex).value =
        LaurentArithmetic.matrixDenote (comparisonProgram t c p hex).value * LaurentArithmetic.matrixDenote t.differential ∧
      LaurentArithmetic.matrixDenote (comparisonProgram t c p hex).value * LaurentArithmetic.matrixDenote p.sourceArray =
        LaurentArithmetic.matrixDenote p.targetArray ∧
      Homogeneous t.coordinates.degree c.coordinates.degree 0
        (LaurentArithmetic.matrixDenote (comparisonProgram t c p hex).value) :=
  (comparisonInput_correct t.differential c.differential p.sourceArray p.targetArray
    t.coordinates.degree c.coordinates.degree _).mp
    (solveOfExists_correct _ (comparison_exists t c p hex))

theorem comparisonProgram_cost (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) :
    (comparisonProgram t c p hex).cost ≤ m*m*LaurentArithmetic.boxSize D h + costBound D n m k h := by
  simp only [comparisonProgram, Work.cost, List.length_append]
  exact Nat.add_le_add
    (comparisonInput_cost t.differential c.differential p.sourceArray p.targetArray
      t.coordinates.degree c.coordinates.degree).le
    (solveOfExists_cost _ (comparison_exists t c p hex))

noncomputable def comparisonMap (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) : T ⟶ C :=
  cochainMap t.coordinates c.coordinates _ _ t.represents c.represents
    (LaurentArithmetic.matrixDenote (comparisonProgram t c p hex).value)
    (comparisonProgram_correct t c p hex).2.2 (comparisonProgram_correct t c p hex).1

theorem comparisonMap_prescribed (t : Represented T m h) (c : Represented C n h)
    (p : Prescribed t.coordinates c.coordinates k h) (hex : ∃ f : T ⟶ C, p.Realized f) :
    p.Realized (comparisonMap t c p hex) := by
  intro i
  apply c.coordinates.embed_injective (p.degrees.get i)
  change c.coordinates.embed _ (component _ _ _ _ _ (p.source i)) = _
  rw [component_embed_zero _ _ _ _ (comparisonProgram_correct t c p hex).2.2, ← p.source_eq]
  have hp := congrArg (fun M : Matrix (Fin n) (Fin k) (Laurent K D) => fun a => M a i)
    (comparisonProgram_correct t c p hex).2.1
  exact hp.trans (p.target_eq i)

end Decoupling.HighDim.AlgorithmTwoLinearComparison
