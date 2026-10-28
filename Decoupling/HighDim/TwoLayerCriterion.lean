import Decoupling.HighDim.TwoLayerMultiplicity
import Decoupling.HighDim.TwoLayerFormality
import Decoupling.HighDim.TwoLayerNested
import Decoupling.HighDim.KoszulLatticeFiniteExt

/-!
# Corollary 2: the actual code on an arbitrary prescribed lattice

Both directions concern stable physical SUM/SWAP decoupling with the
original multiplicities. The common translation kernel is necessary,
and with at most two layers the sole remaining obstruction is the actual
canonical native Ext attachment. No further coarse-graining is allowed.
-/

namespace Decoupling.HighDim.TwoLayer
open CategoryTheory CategoryTheory.Limits PostnikovInduction
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {p D q s r : ℕ} [Fact p.Prime]
  (Γ : AddSubgroup (Translation D)) [Γ.FiniteIndex] (e : Γ ≃+ Translation D)
  (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteXLayers c)

omit [Γ.FiniteIndex] in
theorem onLattice_supported (hc : c.Topological) (hD : 1 ≤ D) :
    Supported (onLatticeProfile Γ e c) (Profile.support c) := by
  intro i hi
  exact ((latticeRestriction Γ e).map_isZero
    (Profile.homology_isZero_outside_support c hc hD i hi)).of_iso
      (ExactDerivedHomology.homologyIso (latticeRestriction Γ e) (Profile.S_X c) i)

theorem decouplesOn_le_lambda0 (hd : DecouplesOn Γ e c) : Γ ≤ Translations.lambda0 c :=
  le_lambda0_of_decouples Γ e c _ (fun i => by
    have := i.1.isLt
    change i.1.val + 1 ≤ D
    omega) hd

include h in
theorem decouplesOn_iff_formal (hc : c.Topological) (hΓ : Γ ≤ Translations.lambda0 c) :
    DecouplesOn Γ e c ↔ Nonempty (onLatticeProfile Γ e c ≅
      homologySum (onLatticeProfile Γ e c) (Profile.support c)) := by
  rw [decouplesOn_iff_nativeSplit Γ e c hc]
  let et := onLatticeHomologyToToricIso Γ e c h hΓ
  exact ⟨fun ⟨f⟩ => ⟨f ≪≫ et.symm⟩, fun ⟨f⟩ => ⟨f ≪≫ et⟩⟩

include h in
theorem decouplesOn_iff_commonKernel_and_connecting (hc : c.Topological) (hD : 1 ≤ D)
    (hm : Layers.nonzeroLayerCount c ≤ 2) :
    DecouplesOn Γ e c ↔ Γ ≤ Translations.lambda0 c ∧
      ∀ j, connecting (onLatticeProfile Γ e c) j = 0 := by
  constructor
  · intro hd
    have hΓ := decouplesOn_le_lambda0 Γ e c hd
    exact ⟨hΓ, connecting_zero_of_formal _ _ ((decouplesOn_iff_formal Γ e c h hc hΓ).mp hd)⟩
  · rintro ⟨hΓ, hk⟩
    apply (decouplesOn_iff_formal Γ e c h hc hΓ).mpr
    exact (formal_iff_all_connecting _ _ (onLattice_supported Γ e c hc hD)
      (by simpa only [Profile.support_card] using hm)).mpr hk

include h in
/-- The zero- and one-layer boundaries have no attachment obstruction. -/
theorem decouplesOn_iff_commonKernel_of_atMostOne (hc : c.Topological) (hD : 1 ≤ D)
    (hm : Layers.nonzeroLayerCount c ≤ 1) :
    DecouplesOn Γ e c ↔ Γ ≤ Translations.lambda0 c := by
  refine ⟨decouplesOn_le_lambda0 Γ e c, fun hΓ => ?_⟩
  apply (decouplesOn_iff_formal Γ e c h hc hΓ).mpr
  exact formal_of_card_le_one _ _ (onLattice_supported Γ e c hc hD)
    (by simpa only [Profile.support_card] using hm)

abbrev fromKernelRestriction (hΓ : Γ ≤ Translations.lambda0 c) :=
  ModuleCat.restrictScalars (KoszulLattice.latticeMap (ZMod p)
    (nestedCoordinateMap (Translations.lambda0 c) Γ hΓ (TrivialLayers.lambda0Coordinates c h) e))

def fromKernelProfileIso (hΓ : Γ ≤ Translations.lambda0 c) :
    (fromKernelRestriction Γ e c h hΓ).mapDerivedCategory.obj (Lambda0Profile.profile c h) ≅
      onLatticeProfile Γ e c :=
  nestedProfileIso (Translations.lambda0 c) Γ hΓ (TrivialLayers.lambda0Coordinates c h) e
    (ZMod p) (Profile.S_X c)

variable (hc : c.Topological) (hD : 1 ≤ D) (i j : ℤ) (hij : i < j)
  (hs : Profile.support c = {i, j})

def canonicalGluing := nativeGluing (Lambda0Profile.profile c h) i j hij
  (hs ▸ Lambda0Profile.supported c h hc hD)

theorem decouplesOn_iff_nativeGluing_zero (hΓ : Γ ≤ Translations.lambda0 c) :
    DecouplesOn Γ e c ↔
      (canonicalGluing c h hc hD i j hij hs).mapExactFunctor (fromKernelRestriction Γ e c h hΓ) = 0 := by
  rw [decouplesOn_iff_formal Γ e c h hc hΓ, canonicalGluing,
    nativeGluing_map_zero_iff_formal]
  rw [formal_iff_of_iso (fromKernelProfileIso Γ e c h hΓ), ← hs]

/-- Full two-layer criterion, including necessity of the common kernel.
The dependent witness is only the proved inclusion needed to define the
actual restriction from Λ₀ to Γ. -/
theorem decouplesOn_iff_kernel_and_nativeGluing :
    DecouplesOn Γ e c ↔ ∃ hΓ : Γ ≤ Translations.lambda0 c,
      (canonicalGluing c h hc hD i j hij hs).mapExactFunctor (fromKernelRestriction Γ e c h hΓ) = 0 := by
  constructor
  · intro hd
    exact ⟨decouplesOn_le_lambda0 Γ e c hd,
      (decouplesOn_iff_nativeGluing_zero Γ e c h hc hD i j hij hs _).mp hd⟩
  · rintro ⟨hΓ, hk⟩
    exact (decouplesOn_iff_nativeGluing_zero Γ e c h hc hD i j hij hs hΓ).mpr hk

end
end Decoupling.HighDim.TwoLayer
