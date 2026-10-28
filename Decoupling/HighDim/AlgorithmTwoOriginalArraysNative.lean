import Decoupling.HighDim.AlgorithmTwoOriginalArrays

/-! # The pure adjacent-array assembly represents the original complex -/
namespace Decoupling.HighDim.AlgorithmTwoOriginalArrays
open CategoryTheory ArithmeticCost LaurentArithmetic AlgorithmTwoFiniteComplex Matrix
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
attribute [local instance] HasDerivedCategory.standard
variable {K : Type} [Field K] {D h length : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

theorem bounded_project_single (coords : StableFree.Coordinates C) (lo : ℤ) (length : ℕ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → coords.rank j = 0)
    (i : Fin length) (a : Fin (coords.rank (lo+i))) :
    (Coordinates.ofBounded coords lo length outside).project (lo+i)
      (Pi.single (finSigmaFinEquiv ⟨i,a⟩) 1) =
      (coords.equiv (lo+i)).symm (Pi.single a 1) := by
  rw [← bounded_embed_single coords lo length outside i a]
  exact Coordinates.project_embed _ _ _

theorem assemble_native (coords : StableFree.Coordinates C) (lo : ℤ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → coords.rank j = 0)
    (d : ∀ i : Fin length, DenseMatrix K D (coords.rank (lo+i+1)) (coords.rank (lo+i)) h)
    (hd : ∀ (i : Fin length) (x : C.X (lo+i)),
      matrixDenote (d i) *ᵥ coords.equiv (lo+i) x =
        coords.equiv (lo+i+1) ((C.d (lo+i) (lo+i+1)).hom x)) :
    matrixDenote (assemble coords.rank lo d) =
      differentialMatrix (Coordinates.ofBounded coords lo length outside) := by
  apply Matrix.ext
  intro r c
  obtain ⟨⟨row,a⟩,rfl⟩ := (finSigmaFinEquiv (n := fun i : Fin length => coords.rank (lo+i))).surjective r
  obtain ⟨⟨col,b⟩,rfl⟩ := (finSigmaFinEquiv (n := fun i : Fin length => coords.rank (lo+i))).surjective c
  rw [assemble_entry]
  change _ = (Coordinates.ofBounded coords lo length outside).embed
    ((totalDegree coords.rank lo length).get (finSigmaFinEquiv ⟨col,b⟩)+1)
    ((C.d _ _).hom ((Coordinates.ofBounded coords lo length outside).project
      ((totalDegree coords.rank lo length).get (finSigmaFinEquiv ⟨col,b⟩))
      (Pi.single (finSigmaFinEquiv ⟨col,b⟩) 1))) (finSigmaFinEquiv ⟨row,a⟩)
  rw [totalDegree_at,bounded_project_single,bounded_embed_at]
  split_ifs with he
  · have hm := congrFun (hd col ((coords.equiv (lo+col)).symm (Pi.single b 1)))
      (Fin.cast (congrArg coords.rank he) a)
    rw [LinearEquiv.apply_symm_apply] at hm
    simpa [Matrix.mulVec,dotProduct,Pi.single_apply,mul_ite] using hm
  · rfl

theorem assemble_represents (coords : StableFree.Coordinates C) (lo : ℤ)
    (outside : ∀ j, j < lo ∨ lo+length ≤ j → coords.rank j = 0)
    (d : ∀ i : Fin length, DenseMatrix K D (coords.rank (lo+i+1)) (coords.rank (lo+i)) h)
    (hd : ∀ (i : Fin length) (x : C.X (lo+i)),
      matrixDenote (d i) *ᵥ coords.equiv (lo+i) x =
        coords.equiv (lo+i+1) ((C.d (lo+i) (lo+i+1)).hom x)) :
    (Coordinates.ofBounded coords lo length outside).RepresentsDifferential
      (matrixDenote (assemble coords.rank lo d)) := by
  rw [assemble_native coords lo outside d hd]
  exact differentialMatrix_represents _

variable {L : ℕ} (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

/-- Original adjacent arrays and their original-coordinate meaning are
the entire coefficient input. Formality is the original successful
coarse-graining condition, not a solver or intermediate-map certificate. -/
structure Input where
  differential : ∀ i : Fin (AlgorithmTwoPipeline.inputLength L),
    DenseMatrix K D (coords.rank (-(L:ℤ)+i+1)) (coords.rank (-(L:ℤ)+i)) h
  represents : ∀ (i : Fin (AlgorithmTwoPipeline.inputLength L)) (x : C.X (-(L:ℤ)+i)),
    matrixDenote (differential i) *ᵥ coords.equiv (-(L:ℤ)+i) x =
      coords.equiv (-(L:ℤ)+i+1) ((C.d (-(L:ℤ)+i) (-(L:ℤ)+i+1)).hom x)
  formal : ∃ old : Fin (D-1) → ℕ,
    Nonempty (DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅
      DerivedCategory.Q.obj C)

/-- The padded matrix is constructed here, with its semantic condition
proved from the original arrays, not supplied by the caller. -/
def Input.toPipeline (inp : Input (L := L) (h := h) coords) :
    AlgorithmTwoPipeline.Input (L := L) (h := h) coords where
  differential := assemble coords.rank (-(L:ℤ)) inp.differential
  represents := assemble_represents coords (-(L:ℤ))
    (AlgorithmTwoPipeline.outside_zero (L := L) coords) inp.differential inp.represents
  formal := inp.formal

end
end Decoupling.HighDim.AlgorithmTwoOriginalArrays
