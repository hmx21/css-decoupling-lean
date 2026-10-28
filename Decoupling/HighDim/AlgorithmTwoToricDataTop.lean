import Decoupling.HighDim.AlgorithmTwoToricDataBasis
import Decoupling.HighDim.AlgorithmTwoToricDataProgram

/-! # The stored top columns are the genuine empty Koszul cells -/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul LaurentArithmetic
open AlgorithmTwoComparison
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1)) (K : Type) [Field K]

local instance toricDataTopFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem emptyCell_degree (c : Copy D t) :
    cellDegree D t c (subsetIndex D ∅) = (c.1.val : ℤ) + 1 := by
  simp [cellDegree, subsetAt_index]

theorem extendedCell_transport (j : ℤ) (k : ℕ) (a b : ℤ)
    (ha : j - (k : ℤ) = a) (hb : j - (k : ℤ) = b) (v : Term (Laurent K D) D k) :
    eqToHom (congrArg (Toric.model K D j).X (ha.symm.trans hb))
      (((laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) ha).inv v) =
      ((laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE j) hb).inv v := by
  subst a
  subst b
  rfl

theorem copyCellVector_empty (c : Copy D t) :
    eqToHom (congrArg (Toric.model K D ((c.1.val : ℤ) + 1)).X (emptyCell_degree D t c))
      (copyCellVector D t K c (subsetIndex D ∅)) = toricTop K D ((c.1.val : ℤ) + 1) := by
  have hs (I : Cell D 0) :
      Finsupp.single I (1 : Laurent K D) = (zeroTermEquiv (Laurent K D)).symm 1 := by
    apply (zeroTermEquiv (Laurent K D)).injective
    rw [zeroTermEquiv_single, LinearEquiv.apply_symm_apply]
  have hzero : (subsetAt D (subsetIndex D ∅)).card = 0 := by simp [subsetAt_index]
  rw [copyCellVector_eq_at D t K c _ 0 hzero]
  rw [extendedCell_transport D K ((c.1.val : ℤ) + 1) 0
    (cellDegree D t c (subsetIndex D ∅)) ((c.1.val : ℤ) + 1)
      (by simpa using (emptyCell_degree D t c).symm) (by simp)]
  change ((laurentComplex K D).extendXIso
    (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1))
      (i := 0) (i' := (c.1.val : ℤ) + 1) (by simp)).inv
        (Finsupp.single (cellOfSet (subsetAt D (subsetIndex D ∅)) hzero) 1) = _
  rw [hs]
  rfl

theorem component_transport {A B : CochainComplex (ModuleCat (Laurent K D)) ℤ}
    (f : A ⟶ B) (a b : ℤ) (hab : a = b) (x : A.X a) :
    eqToHom (congrArg B.X hab) (f.f a x) = f.f b (eqToHom (congrArg A.X hab) x) := by
  subst b
  rfl

theorem stackCellVector_empty (c : Copy D t) :
    eqToHom (congrArg (nativeStack D t K).X (emptyCell_degree D t c))
      (stackCellVector D t K c (subsetIndex D ∅)) =
      stackTop K D (Toric.copyForms D (multiplicities D t)) c := by
  rw [stackCellVector]
  dsimp +instances only [nativeStack, Toric.stackModel, Toric.copyForms]
  rw [component_transport, copyCellVector_empty]
  rfl
  exact emptyCell_degree D t c

theorem totalEmbed_transport (a b : ℤ) (hab : a = b) (x : (nativeStack D t K).X a) :
    totalEmbed D t K b (eqToHom (congrArg (nativeStack D t K).X hab) x) =
      totalEmbed D t K a x := by
  subst b
  rfl

theorem totalEmbed_top (c : Copy D t) :
    totalEmbed D t K ((c.1.val : ℤ) + 1)
      (stackTop K D (Toric.copyForms D (multiplicities D t)) c) =
      Pi.single (topLabel D t c) 1 := by
  rw [← stackCellVector_empty D t K c, totalEmbed_transport, stackCellVector_coordinates]
  rfl
  exact emptyCell_degree D t c

theorem exponentAt_zero (a : Fin (LaurentArithmetic.boxSize D 0)) :
    exponentAt D 0 a = 0 := by
  funext i
  have hi := ((finFunctionFinEquiv (m := 2 * 0 + 1) (n := D)).symm a i).isLt
  dsimp [exponentAt]
  omega

theorem denote_radius_zero_constant (s : K) :
    denote (Vector.ofFn (fun _ : Fin (LaurentArithmetic.boxSize D 0) => s)) = constant s := by
  apply denote_eq_of_coeff
  · intro a ha
    have ha0 : a = 0 := by
      by_contra he
      have hz : (constant s : Laurent K D).coeff a = 0 := by
        simp [constant, AddMonoidAlgebra.coeff_single, Ne.symm he]
      exact Finsupp.mem_support_iff.mp ha hz
    subst a
    simp [LaurentBoxes.mem_box]
  · intro a
    rw [exponentAt_zero]
    simp [constant, AddMonoidAlgebra.coeff_single]

theorem topArray_entry (r : Fin (totalRank D t)) (c : Fin (copyCount D t)) :
    matrixDenote (topArray (K := K) D t) r c =
      if r = topLabel D t (copyEquiv D t c) then (1 : Laurent K D) else 0 := by
  simp only [matrixDenote, topArray, Fin.getElem_fin, Vector.getElem_ofFn]
  change denote (Vector.ofFn (fun _ : Fin (LaurentArithmetic.boxSize D 0) =>
    if r = topLabel D t (copyEquiv D t c) then (1 : K) else 0)) = _
  rw [denote_radius_zero_constant]
  split_ifs <;> simp only [map_one, map_zero]

theorem topProgram_native (c : Fin (copyCount D t)) :
    (matrixDenote (topProgram (K := K) D t).value).col c =
      (totalCoordinates D t K).embed ((copyEquiv D t c).1.val + 1)
        (stackTop K D (Toric.copyForms D (multiplicities D t)) (copyEquiv D t c)) := by
  rw [show (totalCoordinates D t K).embed _ _ = Pi.single (topLabel D t (copyEquiv D t c)) 1
    from totalEmbed_top D t K _]
  funext r
  change matrixDenote (topArray (K := K) D t) r c = _
  rw [topArray_entry]
  simp [Pi.single_apply]

end
end Decoupling.HighDim.AlgorithmTwoToricData
