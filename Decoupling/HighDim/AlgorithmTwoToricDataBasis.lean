import Decoupling.HighDim.AlgorithmTwoToricDataCoordinates
import Decoupling.HighDim.AlgorithmTwoComparisonTopCoordinate

/-!
# The actual cell vector corresponding to each total coordinate

The vectors are constructed by the real Koszul cell inclusion and
the actual stack injection. Their coordinates are proved to be the
stored unit vectors, so later matrix comparisons concern the original
toric complex rather than a proxy complex.
-/
namespace Decoupling.HighDim.AlgorithmTwoToricData
open CategoryTheory CategoryTheory.Limits HomologicalComplex Koszul
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1200000
noncomputable section
variable (D : ℕ) (t : Vector ℕ (D - 1)) (K : Type) [Field K]

local instance toricDataBasisFiniteBiproducts : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

def cellDegree (c : Copy D t) (m : Fin (2 ^ D)) : ℤ :=
  (c.1.val : ℤ) + 1 - (subsetAt D m).card

def copyCellVector (c : Copy D t) (m : Fin (2 ^ D)) :
    (Toric.model K D ((c.1.val : ℤ) + 1)).X (cellDegree D t c m) :=
  ((laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1))
    (i := (subsetAt D m).card) (i' := cellDegree D t c m) rfl).inv
      (Finsupp.single (orderedCell D m) 1)

def stackCellVector (c : Copy D t) (m : Fin (2 ^ D)) :
    (nativeStack D t K).X (cellDegree D t c m) :=
  (biproduct.ι (fun c : Copy D t => Toric.model K D ((c.1.val : ℤ) + 1)) c).f
    (cellDegree D t c m) (copyCellVector D t K c m)

theorem copyCellVector_eq_at (c : Copy D t) (m : Fin (2 ^ D)) (k : ℕ)
    (hk : (subsetAt D m).card = k) :
    copyCellVector D t K c m =
      ((laurentComplex K D).extendXIso (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1))
        (i := k) (i' := cellDegree D t c m) (by dsimp [cellDegree]; rw [hk])).inv
          (Finsupp.single (cellOfSet (subsetAt D m) hk) 1) := by
  subst k
  rfl

theorem copyCellVector_coordinates (c : Copy D t) (m : Fin (2 ^ D))
    (a : GradeMask D ((c.1.val : ℤ) + 1) (cellDegree D t c m)) :
    individualCoordinates K D ((c.1.val : ℤ) + 1) (cellDegree D t c m)
      (copyCellVector D t K c m) a = if a.val = m then 1 else 0 := by
  classical
  rw [individualCoordinates_eq_at K D ((c.1.val : ℤ) + 1) (cellDegree D t c m) (subsetAt D m).card rfl,
    individualCoordinatesAt_apply]
  have hcard : (subsetAt D a.val).card = (subsetAt D m).card := by
    have := a.property
    dsimp [cellDegree] at this
    omega
  have hx : ((laurentComplex K D).extendXIso
      (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1))
      (i := (subsetAt D m).card) (i' := cellDegree D t c m) rfl).hom
        (copyCellVector D t K c m) = Finsupp.single (orderedCell D m) 1 := by
    exact (show _ ≅ _ from (laurentComplex K D).extendXIso
      (ComplexShape.embeddingUpIntLE ((c.1.val : ℤ) + 1))
      (i := (subsetAt D m).card) (i' := cellDegree D t c m) rfl).toLinearEquiv.apply_symm_apply _
  rw [hx]
  have he : cellOfSet (subsetAt D a.val) hcard = orderedCell D m ↔ a.val = m := by
    constructor
    · intro h
      apply (subsetEquiv D).injective
      change subsetAt D a.val = subsetAt D m
      rw [← cellSet_cellOfSet (subsetAt D a.val) hcard, h]
      exact cellSet_cellOfSet _ _
    · intro h
      apply Toric.Hodge.directions_injective
      change cellSet (cellOfSet (subsetAt D a.val) hcard) = cellSet (orderedCell D m)
      rw [cellSet_cellOfSet]
      change subsetAt D a.val = cellSet (cellOfSet (subsetAt D m) rfl)
      rw [cellSet_cellOfSet, h]
  change (Finsupp.single (orderedCell D m) (1 : Laurent K D))
    (cellOfSet (subsetAt D a.val) hcard) = _
  rw [Finsupp.single_apply]
  have he' : orderedCell D m = cellOfSet (subsetAt D a.val) hcard ↔ a.val = m := eq_comm.trans he
  rw [he']
  split_ifs <;> rfl

theorem label_degree_eq (c : Copy D t) (m : Fin (2 ^ D)) :
    (degrees D t).get ((labelEquiv D t).symm (c, m)) = cellDegree D t c m := by
  simp [labelDegree, cellDegree]

theorem stackCellVector_coordinates (c : Copy D t) (m : Fin (2 ^ D)) :
    totalEmbed D t K (cellDegree D t c m) (stackCellVector D t K c m) =
      Pi.single ((labelEquiv D t).symm (c, m)) 1 := by
  classical
  let M := fun c : Copy D t => Toric.model K D ((c.1.val : ℤ) + 1)
  funext i
  obtain ⟨⟨c', m'⟩, rfl⟩ := (labelEquiv D t).symm.surjective i
  by_cases hn : (c'.1.val : ℤ) + 1 - (subsetAt D m').card = cellDegree D t c m
  · rw [totalEmbed_label D t K _ _ c' m' hn]
    by_cases hc : c' = c
    · subst c'
      have hp := congrArg (fun f => f.f (cellDegree D t c m))
        (biproduct.ι_π_self M c)
      change (biproduct.ι M c).f _ ≫ (biproduct.π M c).f _ = 𝟙 _ at hp
      change individualCoordinates K D _ _ (((biproduct.ι M c).f _ ≫ (biproduct.π M c).f _)
        (copyCellVector D t K c m)) ⟨m', hn⟩ = _
      rw [hp]
      change individualCoordinates K D _ _ (copyCellVector D t K c m) ⟨m', hn⟩ = _
      rw [copyCellVector_coordinates]
      simp [Pi.single_apply]
    · have hp := congrArg (fun f => f.f (cellDegree D t c m))
        (biproduct.ι_π_ne M (Ne.symm hc))
      change (biproduct.ι M c).f _ ≫ (biproduct.π M c').f _ = 0 at hp
      change individualCoordinates K D _ _ (((biproduct.ι M c).f _ ≫ (biproduct.π M c').f _)
        (copyCellVector D t K c m)) ⟨m', hn⟩ = _
      rw [hp]
      simp [hc]
  · have hd : (degrees D t).get ((labelEquiv D t).symm (c', m')) ≠ cellDegree D t c m := by
      simpa only [degrees_get, labelDegree, Equiv.apply_symm_apply] using hn
    have hne : (labelEquiv D t).symm (c', m') ≠ (labelEquiv D t).symm (c, m) :=
      fun he => hd (he ▸ label_degree_eq D t c m)
    change (if h : (degrees D t).get ((labelEquiv D t).symm (c', m')) = cellDegree D t c m then
      stackGradeCoordinates D t K _ _ ⟨_, h⟩ else 0) = _
    rw [dite_eq_right hd]
    simp [hne]

theorem totalProject_single (c : Copy D t) (m : Fin (2 ^ D)) :
    totalProject D t K (cellDegree D t c m) (Pi.single ((labelEquiv D t).symm (c, m)) 1) =
      stackCellVector D t K c m := by
  rw [← stackCellVector_coordinates]
  exact (totalCoordinates D t K).project_embed _ _

end
end Decoupling.HighDim.AlgorithmTwoToricData
