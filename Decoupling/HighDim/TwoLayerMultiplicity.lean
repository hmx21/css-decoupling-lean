import Decoupling.HighDim.TwoLayerLattice
import Decoupling.HighDim.SplitMultiplicity

/-!
# Original toric multiplicities on any lattice inside the common kernel

Source: Corollary 2, HD008. This connects a derived splitting on an
arbitrary Γ ⊆ Λ₀ with physical same-Γ SUM/SWAP decoupling, using precisely
the original t_j, with no further coarse-graining and no new lattice.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits ScalingLattice TrivialLayers PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex] (e : Γ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r)

abbrev onLatticeProfile := (latticeRestriction Γ e).mapDerivedCategory.obj (Profile.S_X c)

/-- Actual physical decoupling on Γ with the original superselection multiplicities. -/
def DecouplesOn : Prop := Toric.DecouplesToStack (ZMod p) D
  (Toric.copyForms D (SplitMultiplicity.multiplicities c)) (physicalChecks (ZMod p) Γ e c)

theorem decouplesOn_iff_nativeSplit (hc : c.Topological) :
    DecouplesOn Γ e c ↔ Nonempty (onLatticeProfile Γ e c ≅
      Toric.splitTarget (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c))) := by
  rw [DecouplesOn, Toric.decouples_iff_split _ _ (physicalChecks_topological _ _ _ _ hc) (by
    intro i
    have := i.1.isLt
    change i.1.val + 1 ≤ D
    omega)]
  constructor
  · rintro ⟨f⟩
    exact ⟨physicalChecksRestrictionIso (ZMod p) Γ e c ≪≫ f⟩
  · rintro ⟨f⟩
    exact ⟨(physicalChecksRestrictionIso (ZMod p) Γ e c).symm ≪≫ f⟩

variable (h : Layers.FiniteXLayers c) (hΓ : Γ ≤ Translations.lambda0 c)

def onLatticeLayerIso (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    (latticeRestriction Γ e).obj (Layers.layer c j) ≅
      coefficientVector (ZMod p) D (Layers.multiplicity c j) := by
  let := h j hj hjD
  exact (coordinateCoefficientEquiv Γ e (Layers.layer c j)
    (fun a m => (Translations.mem_lambda0_iff c a).mp (hΓ a.property) j hj hjD m)).toModuleIso ≪≫
      (ModuleCat.restrictScalars augmentation).mapIso
        (Module.finBasis (ZMod p) (Layers.coefficients (Layers.layer c j))).equivFun.toModuleIso

def onLatticeHomologyIso (n : ℕ) : H (onLatticeProfile Γ e c) (n + 1 : ℕ) ≅
    (latticeRestriction Γ e).obj (Layers.layer c (n + 1)) :=
  ExactDerivedHomology.homologyIso (latticeRestriction Γ e) (Profile.S_X c) (n + 1 : ℕ) ≪≫
    (latticeRestriction Γ e).mapIso (Profile.homologyEquivLayer c n).toModuleIso

def onLatticeHomologyCoordinates (i : Profile.support c) :
    H (onLatticeProfile Γ e c) i ≅
      coefficientVector (ZMod p) D (Layers.multiplicity c i.val.toNat) := by
  obtain ⟨hpos, hlt, hcast⟩ := SplitMultiplicity.support_bounds c i
  let n := i.val.toNat - 1
  have hn : i.val.toNat = n + 1 := by dsimp [n]; omega
  have hni : ((n + 1 : ℕ) : ℤ) = i := by omega
  exact eqToIso (congrArg (H (onLatticeProfile Γ e c)) hni.symm) ≪≫
    onLatticeHomologyIso Γ e c n ≪≫ onLatticeLayerIso Γ e c h hΓ (n + 1)
      (by omega) (by omega) ≪≫ eqToIso (congrArg (coefficientVector (ZMod p) D)
        (congrArg (Layers.multiplicity c) hn.symm))

/-- Every original multiplicity, including zero ones, is retained in the target. -/
def onLatticeHomologyToToricIso :
    FiniteBiproduct.sumObj (fun i => (DerivedCategory.singleFunctor
      (ModuleCat (Laurent (ZMod p) D)) i).obj (H (onLatticeProfile Γ e c) i)) (Profile.support c) ≅
      Toric.splitTarget (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c)) := by
  let B := fun i : Profile.support c => (DerivedCategory.singleFunctor
    (ModuleCat (Laurent (ZMod p) D)) i).obj (Koszul.coefficientModule (ZMod p) D)
  let e₁ := biproduct.mapIso (fun i : Profile.support c =>
    (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) i).mapIso
      (onLatticeHomologyCoordinates Γ e c h hΓ i) ≪≫
      SplitMultiplicity.singleVectorIso (ZMod p) D i (Layers.multiplicity c i.val.toNat))
  let e₂ := biproductBiproductIso (fun i : Profile.support c =>
    Fin (Layers.multiplicity c i.val.toNat)) (fun i _ => B i)
  let e₃ : Toric.splitTarget (ZMod p) D (Toric.copyForms D (SplitMultiplicity.multiplicities c)) ≅
      ⨁ (fun x : SplitMultiplicity.SupportedCopies c => B x.1) :=
    biproduct.whiskerEquiv
      (f := fun x : Toric.Copies D (SplitMultiplicity.multiplicities c) =>
        (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D))
          (Toric.copyForms D (SplitMultiplicity.multiplicities c) x + 1)).obj
            (Koszul.coefficientModule (ZMod p) D))
      (g := fun x : SplitMultiplicity.SupportedCopies c => B x.1)
      (SplitMultiplicity.copiesEquiv c) (fun _ => Iso.refl _)
  exact e₁ ≪≫ e₂ ≪≫ e₃.symm

include h hΓ in
theorem decouplesOn_of_formal (hc : c.Topological)
    (hf : Nonempty (onLatticeProfile Γ e c ≅ FiniteBiproduct.sumObj
      (fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent (ZMod p) D)) i).obj
        (H (onLatticeProfile Γ e c) i)) (Profile.support c))) : DecouplesOn Γ e c := by
  obtain ⟨f⟩ := hf
  exact (decouplesOn_iff_nativeSplit Γ e c hc).mpr
    ⟨f ≪≫ onLatticeHomologyToToricIso Γ e c h hΓ⟩

end
end Decoupling.HighDim.TwoLayer
