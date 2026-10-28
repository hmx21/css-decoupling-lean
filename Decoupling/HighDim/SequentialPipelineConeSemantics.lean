import Decoupling.HighDim.AlgorithmTwoPipelineCone
import Decoupling.HighDim.AlgorithmTwoToricDataIndex

/-!
# HD016: the actual cone supplies the descending solver's premises

Source: appendix.tex C4, “Inverting Γ up to homotopy”, and C5,
“The lines of Algorithm 2”. These are proofs about the original cone
coordinates. No contraction matrix is computed by the historical global
solver and no additional certificate is supplied by the public caller.
-/
namespace Decoupling.HighDim.SequentialPipeline
open CategoryTheory HomologicalComplex Matrix ArithmeticCost AlgorithmTwoFiniteComplex
open AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
variable {K : Type} [Field K] [DecidableEq K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
variable (inp : Input (D := D) (L := L) (h := h) cC) (hDL : D ≤ L)
variable (s : InputLayers cC inp hDL) (t : StoredTarget cC inp hDL s)
  (g : StoredGamma cC inp hDL s t)

omit [DecidableEq K] in
theorem represented_homogeneous {G : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    {n : ℕ} (c : Coordinates G n) (d : Matrix (Fin n) (Fin n) (Laurent K D))
    (hd : c.RepresentsDifferential d) : Homogeneous c.degree c.degree 1 d := by
  have he : d = differentialMatrix c := matrix_ext c _ _ (fun j x =>
    (hd j x).trans (differentialMatrix_represents c j x).symm)
  rw [he]
  exact differentialMatrix_homogeneous c

omit [DecidableEq K] in
theorem represented_square_zero {G : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    {n : ℕ} (c : Coordinates G n) (d : Matrix (Fin n) (Fin n) (Laurent K D))
    (hd : c.RepresentsDifferential d) : d * d = 0 := by
  apply matrix_ext c
  intro j x
  rw [← Matrix.mulVec_mulVec, hd, hd, Matrix.zero_mulVec]
  have hz := congrArg (fun f : G.X j ⟶ G.X (j+1+1) => f.hom x)
    (G.d_comp_d j (j+1) (j+1+1))
  change c.embed _ ((G.d (j+1) (j+1+1)).hom ((G.d j (j+1)).hom x)) = 0
  rw [show (G.d (j+1) (j+1+1)).hom ((G.d j (j+1)).hom x) = 0 from hz, map_zero]

theorem cone_differential_properties :
    let d := LaurentArithmetic.matrixDenote (prepareCone cC inp hDL s t g).value
    let degree := coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities)
      (totalDegree cC.rank (-(L:ℤ)) (inputLength L))
    Homogeneous degree degree 1 d ∧ d*d = 0 := by
  let f := gammaMap cC inp hDL s t g
  let ft := AlgorithmTwoToricData.totalCoordinates D s.multiplicities K
  let fc := inputCoordinates (L := L) cC
  let c := Coordinates.cone f ft fc
  have hd : c.RepresentsDifferential
      (LaurentArithmetic.matrixDenote (prepareCone cC inp hDL s t g).value) := by
    rw [prepareCone_correct]
    exact coneMatrix_represents f ft fc _ _ _ (storedTarget_represents cC inp hDL s t)
      inp.represents (gammaMap_represents cC inp hDL s t g)
  exact ⟨represented_homogeneous c _ hd, represented_square_zero c _ hd⟩

/-- Every actual cone basis degree lies in this interval. Its length is
`2*(L+1)+1`; with the manuscript bound `L=D+2` it depends only on D. -/
theorem cone_degree_bounds (i : Fin (coneRank cC inp hDL s)) :
    let degree := coneDegree (AlgorithmTwoToricData.degrees D s.multiplicities)
      (totalDegree cC.rank (-(L:ℤ)) (inputLength L))
    (-((L:ℤ)+1) ≤ degree.get i ∧ degree.get i ≤ (L:ℤ)+1) := by
  dsimp only
  obtain ⟨a | b, rfl⟩ := finSumFinEquiv.surjective i
  · rw [coneDegree_get]
    have hb := AlgorithmTwoToricData.degree_bounds D s.multiplicities a
    dsimp only [Sum.elim_inl]
    omega
  · rw [coneDegree_get]
    dsimp only [Sum.elim_inr]
    rw [totalDegree_get]
    have hb := (finSigmaFinEquiv.symm b).1.isLt
    dsimp only [inputLength] at hb
    omega

/-- This is an existence proof from the actual bounded acyclic cone. It
only discharges failure branches of the new degreewise solver. -/
theorem cone_contractible :
    ∃ H : Matrix (Fin (coneRank cC inp hDL s)) (Fin (coneRank cC inp hDL s)) (Laurent K D),
      LaurentArithmetic.matrixDenote (prepareCone cC inp hDL s t g).value * H +
        H * LaurentArithmetic.matrixDenote (prepareCone cC inp hDL s t g).value = 1 := by
  obtain ⟨H, hH⟩ := cone_solvable cC inp hDL s t g
  exact ⟨H, ((AlgorithmTwoLinearComparison.contractionInput_correct _ _ _).mp hH).1⟩

end
end Decoupling.HighDim.SequentialPipeline
