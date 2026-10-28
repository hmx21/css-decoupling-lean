import Decoupling.HighDim.AlgorithmTwoLinearComparisonNative

/-!
# Counted contraction solve, with solvability derived from a quasi-isomorphism

For the actual mapping cone of a bounded free quasi-isomorphism, the
native existence theorem is used solely to show that the executed scalar
solver succeeds. The returned H, and its native contraction, are those
produced by the program, not the existence theorem's choice of homotopy.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D n h : ℕ}
variable {G T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

omit [DecidableEq K] in
theorem contraction_exists (g : Represented G n h) (hex : Nonempty (Homotopy (𝟙 G) 0)) :
    ∃ H, (contractionInput g.differential g.coordinates.degree).Satisfied H := by
  obtain ⟨s⟩ := hex
  refine ⟨homotopyMatrix g.coordinates s, ?_⟩
  exact (contractionInput_correct _ _ _).mpr
    ⟨homotopyMatrix_equation _ _ g.represents s, homotopyMatrix_homogeneous _ _⟩

/-- Intermediate contractible-system program; the cone wrapper below
obtains this existence hypothesis from the supplied quasi-isomorphism. -/
def contractionProgram (g : Represented G n h) (hex : Nonempty (Homotopy (𝟙 G) 0)) :
    Work K (LaurentArithmetic.DenseMatrix K D n n (resultBox D n n 0 h)) :=
  solveOfExists (contractionInput g.differential g.coordinates.degree) (contraction_exists g hex)

theorem contractionProgram_correct (g : Represented G n h) (hex : Nonempty (Homotopy (𝟙 G) 0)) :
    LaurentArithmetic.matrixDenote g.differential * LaurentArithmetic.matrixDenote (contractionProgram g hex).value +
      LaurentArithmetic.matrixDenote (contractionProgram g hex).value * LaurentArithmetic.matrixDenote g.differential = 1 ∧
    Homogeneous g.coordinates.degree g.coordinates.degree (-1)
      (LaurentArithmetic.matrixDenote (contractionProgram g hex).value) :=
  (contractionInput_correct _ _ _).mp (solveOfExists_correct _ (contraction_exists g hex))

theorem contractionProgram_cost (g : Represented G n h) (hex : Nonempty (Homotopy (𝟙 G) 0)) :
    (contractionProgram g hex).cost ≤ costBound D n n 0 h := solveOfExists_cost _ _

noncomputable def computedContraction (g : Represented G n h) (hex : Nonempty (Homotopy (𝟙 G) 0)) :
    Homotopy (𝟙 G) 0 :=
  AlgorithmTwoFiniteComplex.contraction g.coordinates _ _ g.represents
    (contractionProgram_correct g hex).2 (contractionProgram_correct g hex).1

/-- The actual cone call requires no contraction certificate. Bounded
original free coordinates and QuasiIso discharge solvability internally. -/
def coneContractionProgram (f : T ⟶ C) [QuasiIso f]
    (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (g : Represented (CochainComplex.mappingCone f) n h) :
    Work K (LaurentArithmetic.DenseMatrix K D n n (resultBox D n n 0 h)) :=
  solveOfExists (contractionInput g.differential g.coordinates.degree)
    (contraction_exists g ⟨AlgorithmTwoComparison.coneContraction f cT cC upperT upperC⟩)

theorem coneContractionProgram_cost (f : T ⟶ C) [QuasiIso f]
    (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (g : Represented (CochainComplex.mappingCone f) n h) :
    (coneContractionProgram f cT cC upperT upperC g).cost ≤ costBound D n n 0 h :=
  solveOfExists_cost _ (contraction_exists g ⟨AlgorithmTwoComparison.coneContraction f cT cC upperT upperC⟩)

noncomputable def solvedConeContraction (f : T ⟶ C) [QuasiIso f]
    (cT : StableFree.Coordinates T) (cC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (g : Represented (CochainComplex.mappingCone f) n h) :
    Homotopy (𝟙 (CochainComplex.mappingCone f)) 0 :=
  computedContraction g ⟨AlgorithmTwoComparison.coneContraction f cT cC upperT upperC⟩

end Decoupling.HighDim.AlgorithmTwoLinearComparison
