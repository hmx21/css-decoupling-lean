import Decoupling.HighDim.AlgorithmOneFiniteInput
import Decoupling.HighDim.AlgorithmTwoPipelineChecks

/-!
# A genuine finite dense-array representation always exists

Finite Laurent supports give one common finite integer box for the finite
family of original adjacent differential entries. This proves existence
of Algorithm 2's supplied input representation, without asserting an
algorithm or polynomial cost for choosing the input bases or for Algorithm 1.
The representation theorem applies to every given coordinate system, so it
also covers supplied physical coordinates without changing their basis.
-/
namespace Decoupling.HighDim.AlgorithmOneFiniteInput
open Matrix CategoryTheory LaurentArithmetic
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [CommRing K] {D : ℕ}

/-- Maximum absolute exponent over the actual finite Laurent support. -/
def supportRadius (f : Laurent K D) : ℕ :=
  f.coeff.support.sup (fun a => Finset.univ.sup (fun i : Fin D => (a i).natAbs))

theorem supported_supportRadius (f : Laurent K D) : LaurentBoxes.Supported f (supportRadius f) := by
  classical
  intro a ha
  rw [LaurentBoxes.mem_box]
  intro i
  have h₁ : (a i).natAbs ≤ Finset.univ.sup (fun i : Fin D => (a i).natAbs) :=
    Finset.le_sup (f := fun i : Fin D => (a i).natAbs) (Finset.mem_univ i)
  have h₂ : Finset.univ.sup (fun i : Fin D => (a i).natAbs) ≤ supportRadius f :=
    Finset.le_sup (f := fun a : Translation D => Finset.univ.sup (fun i : Fin D => (a i).natAbs)) ha
  have hn := h₁.trans h₂
  have hn' : ((a i).natAbs : ℤ) ≤ (supportRadius f : ℤ) := by exact_mod_cast hn
  have hp : a i ≤ ((a i).natAbs : ℤ) := Int.le_natAbs
  have hm : -(a i) ≤ ((a i).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(a i)))
  omega

/-- Literal coefficient enumeration of a supported polynomial. -/
def encodeInBox (f : Laurent K D) (B : ℕ) : Dense K D B :=
  Vector.ofFn fun k => f.coeff (exponentAt D B k)

theorem encodeInBox_correct (f : Laurent K D) (B : ℕ) (hf : LaurentBoxes.Supported f B) :
    denote (encodeInBox f B) = f := by
  apply denote_eq_of_coeff _ f hf
  intro k
  simp only [encodeInBox,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta]

/-- Covers empty families and zero-dimensional translation groups as well. -/
theorem finite_family_dense {I : Type} [Fintype I] (f : I → Laurent K D) :
    ∃ B : ℕ, ∃ arrays : I → Dense K D B, ∀ i, denote (arrays i) = f i := by
  classical
  let B := Finset.univ.sup (fun i => supportRadius (f i))
  refine ⟨B,fun i => encodeInBox (f i) B,fun i => encodeInBox_correct (f i) B ?_⟩
  apply LaurentBoxes.supported_mono (supported_supportRadius (f i))
  exact Finset.le_sup (f := fun i => supportRadius (f i)) (Finset.mem_univ i)

end
end Decoupling.HighDim.AlgorithmOneFiniteInput

namespace Decoupling.HighDim.AlgorithmOne
open CategoryTheory Matrix LaurentArithmetic AlgorithmTwoPipeline
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000
variable {K : Type} [Field K] {D L : ℕ}
  {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}

/-- Every already bounded finite-free original complex with its original
formal profile admits a dense input array representation. -/
theorem originalInput_exists (coords : StableFree.Coordinates C)
    [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]
    (hf : ∃ old : Fin (D-1) → ℕ,
      Nonempty (DerivedCategory.Q.obj (Toric.stackModel K D (Toric.copyForms D old)) ≅ DerivedCategory.Q.obj C)) :
    ∃ B : ℕ, Nonempty (AlgorithmTwoOriginalArrays.Input (D := D) (L := L) (h := B) coords) := by
  let I := (i : Fin (inputLength L)) ×
    (Fin (coords.rank (-(L:ℤ)+i+1)) × Fin (coords.rank (-(L:ℤ)+i)))
  let f : I → Laurent K D := fun z => degreeMatrix coords (-(L:ℤ)+z.1) (-(L:ℤ)+z.1+1) z.2.1 z.2.2
  obtain ⟨B,a,ha⟩ := AlgorithmOneFiniteInput.finite_family_dense f
  let d : ∀ i : Fin (inputLength L),
      DenseMatrix K D (coords.rank (-(L:ℤ)+i+1)) (coords.rank (-(L:ℤ)+i)) B :=
    fun i => Vector.ofFn fun row => Vector.ofFn fun col => a ⟨i,(row,col)⟩
  have hd (i : Fin (inputLength L)) : matrixDenote (d i) = degreeMatrix coords (-(L:ℤ)+i) (-(L:ℤ)+i+1) := by
    funext row col
    simpa only [d,matrixDenote,Fin.getElem_fin,Vector.getElem_ofFn,Fin.eta,f] using ha ⟨i,(row,col)⟩
  refine ⟨B,⟨{ differential := d, formal := hf, represents := ?_ }⟩⟩
  intro i x
  rw [hd,degreeMatrix_action,LinearEquiv.symm_apply_apply]

variable {p q s r : ℕ} [Fact p.Prime] (c : CSS.Checks (ZMod p) D q s r)

/-- Under the original code hypotheses, both finite-free coordinates and a
common-box dense representation of the successful complex exist. All inputs
required by the Algorithm 2 representation are thereby accounted for. -/
theorem successComplex_originalInput_exists (hc : c.Topological) (hD : 2 ≤ D) (h : Layers.FiniteXLayers c) :
    ∃ coords : StableFree.Coordinates (successComplex c hc h),
      ∃ B : ℕ, Nonempty (AlgorithmTwoOriginalArrays.Input (D := D) (L := D+2) (h := B) coords) := by
  obtain ⟨coords⟩ := successComplex_coordinates c hc h
  exact ⟨coords,originalInput_exists coords (successComplex_formal c hc hD h)⟩

end
end Decoupling.HighDim.AlgorithmOne
