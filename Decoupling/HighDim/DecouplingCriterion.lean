import Decoupling.HighDim.TwoLayerMultiplicity
import Decoupling.HighDim.CorollaryOneZDual

/-!
# HD010 Theorem 1: an arbitrary prescribed lattice and arbitrary multiplicities

The physical predicate existentially quantifies the toric multiplicities.
There is no finite-dimensional-layer premise and no replacement of the
multiplicities by a possibly zero finrank of an infinite-dimensional module.
-/
namespace Decoupling.HighDim.DecouplingCriterion
open CategoryTheory ScalingLattice
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex] (e : Λ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

/-- Stable local SUM/SWAP decoupling of the actual coarse checks onto some
finite stack of the permitted positive toric types, on exactly Λ. -/
def DecouplesOn : Prop :=
  ∃ t : Fin (D - 1) → ℕ, Toric.DecouplesToStack (ZMod p) D (Toric.copyForms D t)
    (physicalChecks (ZMod p) Λ e c)

/-- The existential native profile condition in Theorem 1. -/
def HasToricProfile : Prop :=
  ∃ t : Fin (D - 1) → ℕ, Nonempty (TwoLayer.onLatticeProfile Λ e c ≅
    Toric.splitTarget (ZMod p) D (Toric.copyForms D t))

/-- For each proposed multiplicity, the same-lattice physical statement
is equivalent to the actual restricted native profile statement. -/
theorem decouples_to_multiplicities_iff (hc : c.Topological) (t : Fin (D - 1) → ℕ) :
    Toric.DecouplesToStack (ZMod p) D (Toric.copyForms D t)
      (physicalChecks (ZMod p) Λ e c) ↔
      Nonempty (TwoLayer.onLatticeProfile Λ e c ≅
        Toric.splitTarget (ZMod p) D (Toric.copyForms D t)) := by
  rw [Toric.decouples_iff_split _ _ (physicalChecks_topological _ _ _ _ hc) (by
    intro i
    have := i.1.isLt
    change i.1.val + 1 ≤ D
    omega)]
  exact ⟨fun ⟨f⟩ => ⟨physicalChecksRestrictionIso (ZMod p) Λ e c ≪≫ f⟩,
    fun ⟨f⟩ => ⟨(physicalChecksRestrictionIso (ZMod p) Λ e c).symm ≪≫ f⟩⟩

/-- Theorem 1, X-side, without any finite-dimensionality assumption. -/
theorem theorem1_X (hc : c.Topological) : DecouplesOn Λ e c ↔ HasToricProfile Λ e c := by
  exact exists_congr (decouples_to_multiplicities_iff Λ e c hc)

/-- The basis of the prescribed actual subgroup can be chosen internally. -/
theorem theorem1_X_canonical (hc : c.Topological) :
    DecouplesOn Λ (LatticeBasis.coordinates Λ) c ↔
      HasToricProfile Λ (LatticeBasis.coordinates Λ) c :=
  theorem1_X Λ (LatticeBasis.coordinates Λ) c hc

end
end Decoupling.HighDim.DecouplingCriterion
