import Decoupling.HighDim.AlgorithmTwoBackendOriginalData

/-!
# Original finite arrays retain their actual native complex

The coordinate maps use precisely the supplied original coordinates and
natural-number dimension transports. The original chain equation proves
SquareZero of the stored raw input, and the resulting native complex is
isomorphic to the actual original C. No new basis or comparison is chosen.
-/
namespace Decoupling.HighDim.AlgorithmTwoBackendOriginal
open CategoryTheory HomologicalComplex Matrix LaurentArithmetic AlgorithmTwoPipelineBackend
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
noncomputable section
variable {R : Type*} [CommRing R] {m n m' n' : ℕ}

def castPower (hn : n=n') : (Fin n → R) ≃ₗ[R] (Fin n' → R) := by
  subst n'
  exact LinearEquiv.refl R _

variable {K : Type} [Field K] {D h : ℕ}

theorem castDense_mulVec (hm : m=m') (hn : n=n')
    (A : DenseMatrix K D m n h) (v : Fin n → Laurent K D) :
    matrixDenote (castDense hm hn A) *ᵥ castPower hn v = castPower hm (matrixDenote A *ᵥ v) := by
  subst m'
  subst n'
  rfl

variable {L : ℕ} {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
  (coords : StableFree.Coordinates C)
  [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
  (inp : AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := h) coords)

def rawTermEquiv (j : ℤ) : C.X j ≃ₗ[Laurent K D]
    (Fin (rankAt (rawInput coords inp).ranks j) → Laurent K D) :=
  (coords.equiv j).trans (castPower (rawInput_rankAt coords inp j).symm)

theorem raw_adjacent_slot (i : Fin (AlgorithmTwoPipeline.inputLength L)) (x : C.X (-(L:ℤ)+i)) :
    matrixDenote (adjacent (rawInput coords inp) (-(L:ℤ)+i)) *ᵥ
      rawTermEquiv coords inp (-(L:ℤ)+i) x =
      rawTermEquiv coords inp (-(L:ℤ)+i+1) (((C.d (-(L:ℤ)+i) (-(L:ℤ)+i+1)).hom) x) := by
  rw [adjacent_slot]
  change matrixDenote (castDense _ _ (inp.differential i)) *ᵥ castPower _ (coords.equiv _ x) = _
  rw [castDense_mulVec, inp.represents]
  rfl

theorem raw_adjacent (j : ℤ) (x : C.X j) :
    matrixDenote (adjacent (rawInput coords inp) j) *ᵥ rawTermEquiv coords inp j x =
      rawTermEquiv coords inp (j+1) ((C.d j (j+1)).hom x) := by
  by_cases hj : -(L:ℤ) ≤ j ∧ j ≤ L
  · obtain ⟨i,hi⟩ : ∃ i : Fin (AlgorithmTwoPipeline.inputLength L), -(L:ℤ)+(i:ℤ)=j :=
      ⟨AlgorithmTwoPipelineBackend.slot L j hj, AlgorithmTwoPipelineBackend.slot_degree L j hj⟩
    subst j
    exact raw_adjacent_slot coords inp i x
  · have hz : CategoryTheory.Limits.IsZero (C.X j) := by
      by_cases hl : j < -(L:ℤ)
      · exact C.isZero_of_isStrictlyGE (-(L:ℤ)) j hl
      · exact C.isZero_of_isStrictlyLE (L:ℤ) j (by omega)
    let : Subsingleton (C.X j) := ModuleCat.subsingleton_of_isZero hz
    rw [Subsingleton.elim x 0]
    simp only [map_zero, Matrix.mulVec_zero]

/-- The full raw chain equation follows from the original native d²=0. -/
theorem raw_squareZero : SquareZero (rawInput coords inp) := by
  intro j
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  rw [Matrix.zero_mulVec, ← Matrix.mulVec_mulVec]
  let x := (rawTermEquiv coords inp j).symm v
  have hx : v = rawTermEquiv coords inp j x := (LinearEquiv.apply_symm_apply _ _).symm
  rw [hx, raw_adjacent, raw_adjacent]
  have hzero := congrArg (fun f : C.X j ⟶ C.X (j+1+1) => f x) (C.d_comp_d j (j+1) (j+1+1))
  change (C.d (j+1) (j+1+1)).hom ((C.d j (j+1)).hom x) = 0 at hzero
  rw [hzero,map_zero]

/-- Explicit native chain isomorphism in the supplied original coordinates. -/
def originalNativeIso : C ≅ nativeComplex (rawInput coords inp) (raw_squareZero coords inp) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun j => (rawTermEquiv coords inp j).toModuleIso) (by
      intro i j hij
      have hj : i+1=j := hij
      subst j
      rw [show (nativeComplex (rawInput coords inp) (raw_squareZero coords inp)).d i (i+1) =
          ModuleCat.ofHom (matrixDenote (adjacent (rawInput coords inp) i)).mulVecLin by simp only [nativeComplex,CochainComplex.of_d]]
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      exact raw_adjacent coords inp i x)

@[simp] theorem originalNativeIso_hom (j : ℤ) (x : C.X j) :
    ((originalNativeIso coords inp).hom.f j).hom x = rawTermEquiv coords inp j x := rfl

end
end Decoupling.HighDim.AlgorithmTwoBackendOriginal
