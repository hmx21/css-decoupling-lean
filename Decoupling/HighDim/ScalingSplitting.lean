import Decoupling.HighDim.PostnikovInduction
import Decoupling.HighDim.ExtRestrictionVanishing

/-!
# The p-scaling splitting theorem for actual derived objects

Combines the proved native Ext restriction lemma with the canonical
Postnikov induction. Augmentation-trivial finite homology is the only
object hypothesis here. For CSS profiles on Lambda0 it is proved from
the common translation kernel, rather than assumed in the final theorem.
-/

namespace Decoupling.HighDim.ScalingSplitting

open CategoryTheory CategoryTheory.Limits
open PostnikovInduction ExactIteration FiniteBiproduct TrivialLayers
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

def TrivialFinite (M : ModuleCat.{0} (Laurent K D)) : Prop :=
  AugmentationAction M ∧ FiniteDimensional K (Layers.coefficients M)

theorem augmentationAction_of_iso {M N : ModuleCat.{0} (Laurent K D)} (e : M ≅ N)
    (h : AugmentationAction M) : AugmentationAction N := by
  intro a m
  obtain ⟨x, rfl⟩ := e.toLinearEquiv.surjective m
  exact (e.toLinearEquiv.map_smul a x).symm.trans
    ((congrArg e.toLinearEquiv (h a x)).trans (e.toLinearEquiv.map_smul _ _))

theorem trivialFinite_of_iso {M N : ModuleCat.{0} (Laurent K D)} (e : M ≅ N)
    (h : TrivialFinite M) : TrivialFinite N := by
  have : FiniteDimensional K ((ModuleCat.restrictScalars constant).obj M) := h.2
  exact ⟨augmentationAction_of_iso e h.1,
    Module.Finite.equiv (((ModuleCat.restrictScalars constant).mapIso e).toLinearEquiv)⟩

abbrev restriction (n : ℕ) := ModuleCat.restrictScalars (Koszul.scaling K D n)

/-- Restriction fixes a genuinely augmentation-trivial module as a module,
including its coefficient dimension. The underlying equivalence is identity. -/
def trivialRestrictionIso (n : ℕ) (M : ModuleCat.{0} (Laurent K D)) (h : AugmentationAction M) :
    (restriction n).obj M ≅ M :=
  (show (restriction n).obj M ≃ₗ[Laurent K D] M from
    { toFun m := m
      invFun m := m
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' a m := by
        change Koszul.scaling K D n a • (show M from m) = a • (show M from m)
        rw [h (Koszul.scaling K D n a), Koszul.augmentation_scaling, h a] }).toModuleIso

theorem trivialFinite_restriction (n : ℕ) (M : ModuleCat.{0} (Laurent K D))
    (h : TrivialFinite M) : TrivialFinite ((restriction n).obj M) :=
  trivialFinite_of_iso (trivialRestrictionIso n M h.1).symm h

def trivialIterateIso (n k : ℕ) (M : ModuleCat.{0} (Laurent K D)) (h : AugmentationAction M) :
    (iterate (restriction n) k).obj M ≅ M := by
  induction k with
  | zero => exact Iso.refl M
  | succ k ih => exact (restriction n).mapIso ih ≪≫ trivialRestrictionIso n M h

theorem iterate_finrank (n k : ℕ) (M : ModuleCat.{0} (Laurent K D)) (h : AugmentationAction M) :
    Module.finrank K (Layers.coefficients ((iterate (restriction n) k).obj M)) =
      Module.finrank K (Layers.coefficients M) :=
  (((ModuleCat.restrictScalars constant).mapIso (trivialIterateIso n k M h)).toLinearEquiv).finrank_eq

variable (p : ℕ) [Fact p.Prime] [CharP K p]

/-- The native derived splitting, with the precise cardinal-minus-one
number of p-restrictions. No Ext vanishing or formality is assumed. -/
theorem exists_split (s : Finset ℤ) (hs : s.Nonempty)
    (X : DerivedCategory (ModuleCat.{0} (Laurent K D)))
    (hX : Supported X s) (hLayers : ∀ i ∈ s, TrivialFinite (H X i)) :
    Nonempty ((derived (restriction p) (s.card - 1)).obj X ≅
      sumObj (fun i => (DerivedCategory.singleFunctor (ModuleCat.{0} (Laurent K D)) i).obj (H X i)) s) := by
  obtain ⟨e⟩ := PostnikovInduction.exists_split (restriction p) TrivialFinite
    (fun e h => trivialFinite_of_iso e h) (trivialFinite_restriction p)
    (fun A B hA hB n hn a => by
      have : FiniteDimensional K (Layers.coefficients A) := hA.2
      obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      exact ExtRestrictionVanishing.of_augmentationAction p A B hA.1 hB.1 n a)
    s hs X hX hLayers
  exact ⟨e ≪≫ biproduct.mapIso (fun i =>
    (DerivedCategory.singleFunctor (ModuleCat.{0} (Laurent K D)) i).mapIso
      (trivialIterateIso p (s.card - 1) (H X i) (hLayers i i.property).1))⟩

/-- Includes the empty-support case: the whole derived object is then
zero, and natural subtraction prescribes zero restrictions. -/
theorem exists_split_including_empty (s : Finset ℤ)
    (X : DerivedCategory (ModuleCat.{0} (Laurent K D)))
    (hX : Supported X s) (hLayers : ∀ i ∈ s, TrivialFinite (H X i)) :
    Nonempty ((derived (restriction p) (s.card - 1)).obj X ≅
      sumObj (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i)) s) := by
  by_cases hs : s.Nonempty
  · exact exists_split p s hs X hX hLayers
  · have hs0 : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have : X.IsLE 0 := supported_isLE hX 0 (by simp)
    have : X.IsGE 1 := supported_isGE hX 1 (by simp)
    have hzero : IsZero X := DerivedCategory.TStructure.t.isZero X 0 1
    have hsum : IsZero (sumObj
        (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj (H X i)) ∅) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply biproduct.hom_ext
      intro i
      exact (Finset.notMem_empty _ i.property).elim
    exact ⟨hzero.isoZero ≪≫ hsum.isoZero.symm⟩

end
end Decoupling.HighDim.ScalingSplitting
