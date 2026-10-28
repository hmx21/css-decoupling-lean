import Decoupling.HighDim.AlgorithmTwoPipelineProgram
import Decoupling.HighDim.AlgorithmTwoOriginalArraysNative

/-!
# Finite data input for the closed executable backend

Ranks and coefficients are stored finite data. The canonical coordinate
complex is only a semantic interpretation of those arrays. Its coordinate
bijections are literal identity functions; no native basis is runtime data.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipelineBackend
open CategoryTheory HomologicalComplex Matrix ArithmeticCost LaurentArithmetic
open AlgorithmTwoPipeline
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {D L h : ℕ}

def slot (L : ℕ) (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) : Fin (inputLength L) :=
  ⟨(j+L).toNat,by dsimp [inputLength]; omega⟩
theorem slot_degree (L : ℕ) (j : ℤ) (hj : -(L:ℤ) ≤ j ∧ j ≤ L) : -(L:ℤ)+(slot L j hj : ℤ)=j := by
  dsimp [slot]; omega

def rankAt (ranks : Vector ℕ (inputLength L)) (j : ℤ) : ℕ :=
  if hj : -(L:ℤ) ≤ j ∧ j ≤ L then ranks.get (slot L j hj) else 0

theorem rankAt_outside (ranks : Vector ℕ (inputLength L)) (j : ℤ)
    (hj : j < -(L:ℤ) ∨ L < j) : rankAt ranks j = 0 := by
  unfold rankAt
  rw [dite_eq_right (by omega)]

theorem rankAt_slot (ranks : Vector ℕ (inputLength L)) (i : Fin (inputLength L)) :
    rankAt ranks (-(L:ℤ)+i) = ranks.get i := by
  have hi : -(L:ℤ) ≤ -(L:ℤ)+i ∧ -(L:ℤ)+i ≤ L := by have := i.isLt; dsimp [inputLength] at *; omega
  rw [rankAt,dite_eq_left hi]
  congr 1
  apply Fin.ext
  dsimp [slot]
  omega

structure RawInput (K : Type) (D L h : ℕ) where
  ranks : Vector ℕ (inputLength L)
  differential : ∀ i : Fin (inputLength L),
    DenseMatrix K D (rankAt ranks (-(L:ℤ)+i+1)) (rankAt ranks (-(L:ℤ)+i)) h

/-- Zero outside the stored finite interval, with pure coefficient copies inside. -/
def adjacent (raw : RawInput K D L h) (j : ℤ) : DenseMatrix K D (rankAt raw.ranks (j+1)) (rankAt raw.ranks j) h :=
  if hj : -(L:ℤ) ≤ j ∧ j ≤ L then
    let i := slot L j hj
    have hi : -(L:ℤ)+i=j := slot_degree L j hj
    Vector.ofFn fun a => Vector.ofFn fun b =>
      (raw.differential i)[Fin.cast (congrArg (fun z => rankAt raw.ranks (z+1)) hi.symm) a][Fin.cast (congrArg (rankAt raw.ranks) hi.symm) b]
  else StableFree.Effective.zeroMatrixDense K D h _ _

theorem adjacent_slot (raw : RawInput K D L h) (i : Fin (inputLength L)) :
    adjacent raw (-(L:ℤ)+i) = raw.differential i := by
  have hi : -(L:ℤ) ≤ -(L:ℤ)+i ∧ -(L:ℤ)+i ≤ L := by have := i.isLt; dsimp [inputLength] at *; omega
  have hs : slot L (-(L:ℤ)+i) hi=i := by apply Fin.ext; dsimp [slot]; omega
  unfold adjacent
  rw [dite_eq_left hi]
  apply Vector.ext
  intro a ha
  apply Vector.ext
  intro b hb
  simp only [Vector.getElem_ofFn,Fin.getElem_fin,Fin.val_cast]
  have hg (k : Fin (inputLength L)) (hk : k=i)
      (ha' : a < rankAt raw.ranks (-(L:ℤ)+k+1))
      (hb' : b < rankAt raw.ranks (-(L:ℤ)+k)) :
      ((raw.differential k)[a]'ha')[b]'hb' = (raw.differential i)[a][b] := by
    subst k
    rfl
  exact hg _ hs _ _


/-- The usual chain equation, not a solver or comparison certificate. -/
def SquareZero (raw : RawInput K D L h) : Prop :=
  ∀ j : ℤ, matrixDenote (adjacent raw (j+1)) * matrixDenote (adjacent raw j) = 0

noncomputable def nativeComplex (raw : RawInput K D L h) (sq : SquareZero raw) :
    CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  CochainComplex.of (fun j => ModuleCat.of (Laurent K D) (Fin (rankAt raw.ranks j) → Laurent K D))
    (fun j => ModuleCat.ofHom (matrixDenote (adjacent raw j)).mulVecLin) (by
      intro j
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      change matrixDenote (adjacent raw (j+1)) *ᵥ (matrixDenote (adjacent raw j) *ᵥ x)=0
      rw [Matrix.mulVec_mulVec,sq j,Matrix.zero_mulVec])

/-- Explicit identity coordinate functions keep this structure computable,
although Laurent denotation in the native differential is semantic only. -/
def coordinates (raw : RawInput K D L h) (sq : SquareZero raw) : StableFree.Coordinates (nativeComplex raw sq) where
  rank := rankAt raw.ranks
  equiv _ := { toFun := fun x => x
               invFun := fun x => x
               left_inv := fun _ => rfl
               right_inv := fun _ => rfl
               map_add' := fun _ _ => rfl
               map_smul' := fun _ _ => rfl }

noncomputable section

instance native_lower (raw : RawInput K D L h) (sq : SquareZero raw) :
    (nativeComplex raw sq).IsStrictlyGE (-(L:ℤ)) := by
  rw [CochainComplex.isStrictlyGE_iff]
  intro j hj
  change CategoryTheory.Limits.IsZero (ModuleCat.of (Laurent K D) (Fin (rankAt raw.ranks j) → Laurent K D))
  rw [rankAt_outside raw.ranks j (Or.inl hj)]
  exact ModuleCat.isZero_of_subsingleton _

instance native_upper (raw : RawInput K D L h) (sq : SquareZero raw) :
    (nativeComplex raw sq).IsStrictlyLE (L:ℤ) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro j hj
  change CategoryTheory.Limits.IsZero (ModuleCat.of (Laurent K D) (Fin (rankAt raw.ranks j) → Laurent K D))
  rw [rankAt_outside raw.ranks j (Or.inr hj)]
  exact ModuleCat.isZero_of_subsingleton _

theorem adjacent_native (raw : RawInput K D L h) (sq : SquareZero raw)
    (i : Fin (inputLength L)) (x : (nativeComplex raw sq).X (-(L:ℤ)+i)) :
    matrixDenote (raw.differential i) *ᵥ (coordinates raw sq).equiv (-(L:ℤ)+i) x =
      (coordinates raw sq).equiv (-(L:ℤ)+i+1)
        (((nativeComplex raw sq).d (-(L:ℤ)+i) (-(L:ℤ)+i+1)).hom x) := by
  rw [show (nativeComplex raw sq).d (-(L:ℤ)+i) (-(L:ℤ)+i+1) =
      ModuleCat.ofHom (matrixDenote (adjacent raw (-(L:ℤ)+i))).mulVecLin by simp only [nativeComplex,CochainComplex.of_d]]
  change matrixDenote (raw.differential i) *ᵥ x = matrixDenote (adjacent raw (-(L:ℤ)+i)) *ᵥ x
  rw [adjacent_slot]

end
end Decoupling.HighDim.AlgorithmTwoPipelineBackend
