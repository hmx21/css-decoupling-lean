import Decoupling.HighDim.AlgorithmTwoToricDataBasis
import Decoupling.HighDim.AlgorithmTwoToricDataBoundary
import Decoupling.HighDim.AlgorithmTwoToricDataGrading
import Decoupling.HighDim.AlgorithmTwoFiniteComplexMatrix

/-! # Faithful native differential in the materialised mask coordinates -/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul Matrix
open LaurentArithmetic AlgorithmTwoFiniteComplex
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1500000
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1)) (K : Type) [Field K]

local instance toricDataDifferentialFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

theorem copyCellVector_d_read (c : Copy D t) (m : Fin (2 ^ D))
    (a : GradeMask D ((c.1.val : ℤ) + 1) (cellDegree D t c m + 1)) :
    individualCoordinates K D ((c.1.val : ℤ) + 1) (cellDegree D t c m + 1)
      ((Toric.model K D ((c.1.val : ℤ) + 1)).d (cellDegree D t c m) (cellDegree D t c m + 1)
        (copyCellVector D t K c m)) a =
      denote (faceDense (-1 : K) (subsetAt D a.val) (subsetAt D m)) := by
  let k := (subsetAt D a.val).card
  have hcard : (subsetAt D m).card = k + 1 := by
    have ha := a.property
    dsimp [cellDegree, k] at *
    omega
  have hs : (c.1.val : ℤ) + 1 - (k + 1 : ℕ) = cellDegree D t c m := by
    dsimp [cellDegree]
    rw [hcard]
    simp
  have ht : (c.1.val : ℤ) + 1 - (k : ℤ) = cellDegree D t c m + 1 := a.property
  rw [individualCoordinates_eq_at K D ((c.1.val : ℤ) + 1) (cellDegree D t c m + 1) k ht,
    individualCoordinatesAt_apply, copyCellVector_eq_at D t K c m (k + 1) hcard]
  let I := cellOfSet (subsetAt D m) hcard
  let J := cellOfSet (subsetAt D a.val) (show (subsetAt D a.val).card = k from rfl)
  let es := (laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1)) hs
  let et := (laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1)) ht
  change (show Term (Laurent K D) D k from et.hom
    ((Toric.model K D ((c.1.val : ℤ) + 1)).d (cellDegree D t c m) (cellDegree D t c m + 1)
      (es.inv (Finsupp.single I 1)))) J = _
  have hdiff : (Toric.model K D ((c.1.val : ℤ) + 1)).d
      (cellDegree D t c m) (cellDegree D t c m + 1) =
      es.hom ≫ (laurentComplex K D).d (k + 1) k ≫ et.inv :=
    (laurentComplex K D).extend_d_eq (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1)) hs ht
  change (show Term (Laurent K D) D k from
    (es.inv ≫ (Toric.model K D ((c.1.val : ℤ) + 1)).d _ _ ≫ et.hom) (Finsupp.single I 1)) J = _
  rw [hdiff]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  have hd0 : (laurentComplex K D).d (k + 1) k = boundary (Laurent K D) (difference K) k :=
    complex_d (Laurent K D) (difference K) k
  rw [hd0]
  change (show Term (Laurent K D) D k from
    boundary (Laurent K D) (difference K) k (Finsupp.single I 1)) J = _
  have h := (faceDense_boundary (K := K) J I).symm
  simpa only [I, J, cellSet_cellOfSet] using h

theorem stackCellVector_d_coordinates (c : Copy D t) (m : Fin (2 ^ D)) :
    totalEmbed D t K (cellDegree D t c m + 1)
      ((nativeStack D t K).d (cellDegree D t c m) (cellDegree D t c m + 1)
        (stackCellVector D t K c m)) =
      (matrixDenote (differentialArray D t (-1 : K))).col ((labelEquiv D t).symm (c, m)) := by
  classical
  let M := fun c : Copy D t => Toric.model K D ((c.1.val : ℤ) + 1)
  funext r
  obtain ⟨⟨c', m'⟩, rfl⟩ := (labelEquiv D t).symm.surjective r
  by_cases hn : (c'.1.val : ℤ) + 1 - (subsetAt D m').card = cellDegree D t c m + 1
  · rw [totalEmbed_label D t K _ _ c' m' hn]
    change individualCoordinates K D _ _
      (((nativeStack D t K).d _ _ ≫ (biproduct.π M c').f _) (stackCellVector D t K c m)) _ = _
    dsimp only [nativeStack, Toric.stackModel, Toric.copyForms]
    rw [← (biproduct.π M c').comm]
    by_cases hc : c' = c
    · subst c'
      have hp := congrArg (fun f => f.f (cellDegree D t c m)) (biproduct.ι_π_self M c)
      change (biproduct.ι M c).f _ ≫ (biproduct.π M c).f _ = 𝟙 _ at hp
      change individualCoordinates K D _ _
        ((M c).d _ _ (((biproduct.ι M c).f _ ≫ (biproduct.π M c).f _) (copyCellVector D t K c m))) _ = _
      rw [hp]
      change individualCoordinates K D _ _
        ((M c).d _ _ (copyCellVector D t K c m)) ⟨m', hn⟩ = _
      rw [copyCellVector_d_read]
      simp only [Matrix.col, Matrix.transpose_apply, differentialArray_entry, Equiv.apply_symm_apply, ite_true]
    · have hp := congrArg (fun f => f.f (cellDegree D t c m)) (biproduct.ι_π_ne M (Ne.symm hc))
      change (biproduct.ι M c).f _ ≫ (biproduct.π M c').f _ = 0 at hp
      change individualCoordinates K D _ _
        ((M c').d _ _ (((biproduct.ι M c).f _ ≫ (biproduct.π M c').f _) (copyCellVector D t K c m))) _ = _
      rw [hp]
      simp [Matrix.col, Matrix.transpose_apply, differentialArray_entry, hc]
  · have hd : (degrees D t).get ((labelEquiv D t).symm (c', m')) ≠ cellDegree D t c m + 1 := by
      simpa only [degrees_get, labelDegree, Equiv.apply_symm_apply] using hn
    have hz := differentialArray_homogeneous (K := K) D t ((labelEquiv D t).symm (c', m'))
      ((labelEquiv D t).symm (c, m)) (by rw [label_degree_eq D t c m]; exact hd)
    change (if h : (degrees D t).get ((labelEquiv D t).symm (c', m')) = cellDegree D t c m + 1 then
      stackGradeCoordinates D t K _ _ ⟨_, h⟩ else 0) = _
    rw [dite_eq_right hd]
    exact hz.symm

theorem nativeDifferential_entry_at (r a : Fin (totalRank D t)) (n : ℤ)
    (ha : (degrees D t).get a = n) :
    differentialMatrix (totalCoordinates D t K) r a =
      totalEmbed D t K (n + 1) ((nativeStack D t K).d n (n + 1)
        (totalProject D t K n (Pi.single a 1))) r := by
  subst n
  rfl

/-- The complete materialised array is the matrix of the actual
toric-stack differential in the proved total coordinates. -/
theorem differentialArray_native :
    matrixDenote (differentialArray D t (-1 : K)) =
      differentialMatrix (totalCoordinates D t K) := by
  apply Matrix.ext
  intro r a
  obtain ⟨⟨c, m⟩, rfl⟩ := (labelEquiv D t).symm.surjective a
  rw [nativeDifferential_entry_at D t K r _ (cellDegree D t c m) (label_degree_eq D t c m),
    totalProject_single]
  exact (congrFun (stackCellVector_d_coordinates D t K c m) r).symm

theorem differentialProgram_represents :
    (totalCoordinates D t K).RepresentsDifferential (matrixDenote (differentialProgram (K := K) D t).value) := by
  rw [differentialProgram_value, differentialArray_native]
  exact differentialMatrix_represents _

end
end Decoupling.HighDim.AlgorithmTwoToricData
