import Decoupling.HighDim.AlgorithmTwoPipelineInput
import Decoupling.HighDim.DenseCircuitPermutationTheta

/-!
# Zero-total-rank branch without a radius-dependent computation

An original input with no total free coordinates is the zero complex,
including every degree outside the interval. Its target is the empty
actual toric stack and its word is literally empty. No coefficient box
is enumerated and the field-operation trace is empty for every radius.
-/
namespace Decoupling.HighDim.AlgorithmTwoPipeline
open CategoryTheory CategoryTheory.Limits HomologicalComplex ArithmeticCost
open AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable {K : Type} [Field K] {D L h : ℕ}
variable {C : CochainComplex (ModuleCat (Laurent K D)) ℤ}
variable (cC : StableFree.Coordinates C) [C.IsStrictlyGE (-(L:ℤ))] [C.IsStrictlyLE (L:ℤ)]

include cC in
theorem rank_zero_of_total_zero (hz : inputRank cC L = 0) (j : ℤ) : cC.rank j = 0 := by
  by_cases hj : j < -(L:ℤ) ∨ -(L:ℤ)+inputLength L ≤ j
  · exact outside_zero cC j hj
  · let i : Fin (inputLength L) := ⟨(j+L).toNat, by dsimp only [inputLength] at *; omega⟩
    have hi : -(L:ℤ)+(i:ℤ)=j := by dsimp [i]; omega
    have hn : cC.rank (-(L:ℤ)+(i:ℤ)) ≤ inputRank cC L :=
      Finset.single_le_sum (f := fun a : Fin (inputLength L) => cC.rank (-(L:ℤ)+(a:ℤ)))
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    rw [hi,hz] at hn
    omega

theorem term_subsingleton_of_total_zero (hz : inputRank cC L = 0) (j : ℤ) : Subsingleton (C.X j) := by
  have hj := rank_zero_of_total_zero cC hz j
  let : Subsingleton (StableFree.Power (Laurent K D) (cC.rank j)) := by rw [hj]; infer_instance
  exact (cC.equiv j).injective.subsingleton

theorem complex_isZero_of_total_zero (hz : inputRank cC L = 0) : IsZero C := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (term_subsingleton_of_total_zero cC hz j).elim _ _

def zeroMultiplicities (D : ℕ) : Vector ℕ (D-1) := Vector.replicate (D-1) 0

def emptyProgram (K : Type) (D : ℕ) : Work K (Vector ℕ (D-1) × List (Circuit.Layer K D (Fin 0))) :=
  Work.pure (zeroMultiplicities D, [])

omit [Field K] in
@[simp] theorem emptyProgram_cost : (emptyProgram K D).cost = 0 := rfl
omit [Field K] in
@[simp] theorem emptyProgram_depth : (emptyProgram K D).value.2.length = 0 := rfl

noncomputable section

def emptyTarget (K : Type) [Field K] (D : ℕ) : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  Toric.stackModel K D (Toric.copyForms D (fun _ => 0))

theorem emptyTarget_term_subsingleton (j : ℤ) : Subsingleton ((emptyTarget K D).X j) := by
  let : IsEmpty (Toric.Copies D (fun _ => 0)) := ⟨fun i => Fin.elim0 i.2⟩
  exact (Toric.stackTermIso K D (Toric.copyForms D (fun _ => 0)) j).toLinearEquiv.injective.subsingleton

theorem emptyTarget_isZero : IsZero (emptyTarget K D) := by
  rw [IsZero.iff_id_eq_zero]
  apply HomologicalComplex.Hom.ext
  funext j
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  exact (emptyTarget_term_subsingleton (K := K) (D := D) j).elim _ _

/-- The empty runtime output has a native equivalence to the actual input. -/
def emptyEquivalence (hz : inputRank cC L = 0) : HomotopyEquiv C (emptyTarget K D) where
  hom := 0
  inv := 0
  homotopyHomInvId := Homotopy.ofEq (by
    rw [zero_comp]
    exact ((IsZero.iff_id_eq_zero C).mp (complex_isZero_of_total_zero cC hz)).symm)
  homotopyInvHomId := Homotopy.ofEq (by
    rw [zero_comp]
    exact ((IsZero.iff_id_eq_zero (emptyTarget K D)).mp emptyTarget_isZero).symm)

end
end Decoupling.HighDim.AlgorithmTwoPipeline
