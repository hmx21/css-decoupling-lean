import Decoupling.HighDim.AlgorithmTwoLinearComparisonConeArray
import Decoupling.HighDim.AlgorithmTwoFiniteComplexConeMatrix

/-!
# Executable native cone assembly and contraction

The cone coordinates and signed differential are constructed from the
original represented complexes and the actual comparison matrix. The
caller provides no cone matrix, cone coordinates, or homotopy certificate.
-/
namespace Decoupling.HighDim.AlgorithmTwoLinearComparison
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] [DecidableEq K] {D m n h : ℕ}
variable {T C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

noncomputable def coneRepresentation (f : T ⟶ C) (t : Represented T m h) (c : Represented C n h)
    (A : LaurentArithmetic.DenseMatrix K D n m h)
    (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x)) :
    Represented (CochainComplex.mappingCone f) (m+n) h where
  coordinates := Coordinates.cone f t.coordinates c.coordinates
  differential := (coneArrayProgram t.differential c.differential A).value
  represents := by
    rw [coneArrayProgram_correct]
    exact coneMatrix_represents f t.coordinates c.coordinates _ _ _ t.represents c.represents hA

def coneSolveProgram (f : T ⟶ C) [QuasiIso f]
    (t : Represented T m h) (c : Represented C n h)
    (originalT : StableFree.Coordinates T) (originalC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (A : LaurentArithmetic.DenseMatrix K D n m h)
    (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x)) :
    Work K (LaurentArithmetic.DenseMatrix K D (m+n) (m+n) (resultBox D (m+n) (m+n) 0 h)) :=
  let cone := coneArrayProgram t.differential c.differential A
  let result := solveOfExists (contractionInput cone.value (coneDegree t.coordinates.degree c.coordinates.degree))
    (contraction_exists (coneRepresentation f t c A hA)
      ⟨AlgorithmTwoComparison.coneContraction f originalT originalC upperT upperC⟩)
  { value := result.value, trace := cone.trace ++ result.trace }

theorem coneSolveProgram_cost (f : T ⟶ C) [QuasiIso f]
    (t : Represented T m h) (c : Represented C n h)
    (originalT : StableFree.Coordinates T) (originalC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (A : LaurentArithmetic.DenseMatrix K D n m h)
    (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x)) :
    (coneSolveProgram f t c originalT originalC upperT upperC A hA).cost ≤
      m*m*LaurentArithmetic.boxSize D h + costBound D (m+n) (m+n) 0 h := by
  simp only [coneSolveProgram, Work.cost, List.length_append]
  exact Nat.add_le_add (coneArrayProgram_cost t.differential c.differential A).le
    (solveOfExists_cost _ _)

/-- The native contraction has the exact solved H as its lowering matrix. -/
noncomputable def coneSolveContraction (f : T ⟶ C) [QuasiIso f]
    (t : Represented T m h) (c : Represented C n h)
    (originalT : StableFree.Coordinates T) (originalC : StableFree.Coordinates C)
    (upperT upperC : ℤ) [T.IsStrictlyLE upperT] [C.IsStrictlyLE upperC]
    (A : LaurentArithmetic.DenseMatrix K D n m h)
    (hA : ∀ j x, LaurentArithmetic.matrixDenote A *ᵥ t.coordinates.embed j x =
      c.coordinates.embed j ((f.f j).hom x)) :
    Homotopy (𝟙 (CochainComplex.mappingCone f)) 0 :=
  computedContraction (coneRepresentation f t c A hA)
    ⟨AlgorithmTwoComparison.coneContraction f originalT originalC upperT upperC⟩

end Decoupling.HighDim.AlgorithmTwoLinearComparison
