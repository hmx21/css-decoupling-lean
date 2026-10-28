import Decoupling.HighDim.GluedNativeCone

/-!
# An elementary native homology comparison

This criterion proves a native quasi-isomorphism from explicit module
surjectivity and an actual boundary description of its middle kernel.
It is used to justify the concrete check-to-cone comparison.
-/

namespace Decoupling.HighDim.Glued
open CategoryTheory CategoryTheory.Limits
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {R : Type} [CommRing R]

/-- The actual native homology class of a concrete cycle. -/
def cycleClass (S : ShortComplex (ModuleCat R)) (x : S.X₂) (hx : S.g x = 0) : S.homology :=
  S.homologyπ (S.moduleCatCyclesIso.inv ⟨x, hx⟩)

theorem cycleClass_ι (S : ShortComplex (ModuleCat R)) (x : S.X₂) (hx : S.g x = 0) :
    S.homologyι (cycleClass S x hx) = S.pOpcycles x := by
  change (S.homologyπ ≫ S.homologyι) (S.moduleCatCyclesIso.inv ⟨x, hx⟩) = _
  rw [ShortComplex.homology_π_ι]
  change S.pOpcycles ((S.moduleCatCyclesIso.inv ≫ S.iCycles) ⟨x, hx⟩) = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

theorem cycleClass_eq_zero_iff (S : ShortComplex (ModuleCat R))
    (x : S.X₂) (hx : S.g x = 0) :
    cycleClass S x hx = 0 ↔ ∃ z, S.f z = x := by
  rw [← (ModuleCat.mono_iff_injective S.homologyι).mp inferInstance |>.eq_iff]
  rw [cycleClass_ι, map_zero, ShortComplex.moduleCat_pOpcycles_eq_zero_iff]
  rfl

theorem cycleClass_surjective (S : ShortComplex (ModuleCat R)) (h : S.homology) :
    ∃ (x : S.X₂) (hx : S.g x = 0), cycleClass S x hx = h := by
  obtain ⟨z, rfl⟩ := (ModuleCat.epi_iff_surjective S.homologyπ).mp inferInstance h
  let x := S.moduleCatCyclesIso.hom z
  refine ⟨x.val, x.property, ?_⟩
  change S.homologyπ (S.moduleCatCyclesIso.inv (S.moduleCatCyclesIso.hom z)) = _
  change S.homologyπ ((S.moduleCatCyclesIso.hom ≫ S.moduleCatCyclesIso.inv) z) = _
  rw [Iso.hom_inv_id]
  rfl

theorem homologyMap_cycleClass {S T : ShortComplex (ModuleCat R)} (φ : S ⟶ T)
    (x : S.X₂) (hx : S.g x = 0) :
    ShortComplex.homologyMap φ (cycleClass S x hx) =
      cycleClass T (φ.τ₂ x) (by
        change (φ.τ₂ ≫ T.g) x = 0
        rw [φ.comm₂₃]
        change φ.τ₃ (S.g x) = 0
        rw [hx, map_zero]) := by
  apply (ModuleCat.mono_iff_injective T.homologyι).mp inferInstance
  rw [cycleClass_ι]
  change (S.homologyπ ≫ ShortComplex.homologyMap φ ≫ T.homologyι)
    (S.moduleCatCyclesIso.inv ⟨x, hx⟩) = _
  rw [ShortComplex.π_homologyMap_ι]
  change T.pOpcycles (φ.τ₂ ((S.moduleCatCyclesIso.inv ≫ S.iCycles) ⟨x, hx⟩)) = _
  rw [ShortComplex.moduleCatCyclesIso_inv_iCycles]
  rfl

/-- Surjective component comparison with exact middle kernel. Each
hypothesis is an explicit assertion about the actual module maps. -/
theorem quasiIso_of_surjective_exact_kernel {S T : ShortComplex (ModuleCat R)}
    (φ : S ⟶ T) (h₁ : Function.Surjective φ.τ₁)
    (h₂ : Function.Surjective φ.τ₂) (h₃ : Function.Injective φ.τ₃)
    (hk : ∀ x : S.X₂, φ.τ₂ x = 0 → ∃ z, S.f z = x) : ShortComplex.QuasiIso φ := by
  rw [ShortComplex.quasiIso_iff, ConcreteCategory.isIso_iff_bijective]
  constructor
  · apply (injective_iff_map_eq_zero (ShortComplex.homologyMap φ).hom).mpr
    intro c hc
    obtain ⟨x, hx, rfl⟩ := cycleClass_surjective S c
    rw [homologyMap_cycleClass] at hc
    obtain ⟨z, hz⟩ := (cycleClass_eq_zero_iff T _ _).mp hc
    obtain ⟨w, rfl⟩ := h₁ z
    have hcomm := congrArg (fun m : S.X₁ ⟶ T.X₂ => m w) φ.comm₁₂.symm
    change φ.τ₂ (S.f w) = T.f (φ.τ₁ w) at hcomm
    have hx0 : φ.τ₂ (x - S.f w) = 0 := by rw [map_sub, hcomm, hz, sub_self]
    obtain ⟨u, hu⟩ := hk (x - S.f w) hx0
    apply (cycleClass_eq_zero_iff S x hx).mpr
    refine ⟨u + w, ?_⟩
    rw [map_add, hu, sub_add_cancel]
  · intro c
    obtain ⟨y, hy, rfl⟩ := cycleClass_surjective T c
    obtain ⟨x, rfl⟩ := h₂ y
    have hx : S.g x = 0 := by
      apply h₃
      have hcomm := congrArg (fun m : S.X₂ ⟶ T.X₃ => m x) φ.comm₂₃
      change T.g (φ.τ₂ x) = φ.τ₃ (S.g x) at hcomm
      rw [← hcomm, hy, map_zero]
    exact ⟨cycleClass S x hx, homologyMap_cycleClass φ x hx⟩

end
end Decoupling.HighDim.Glued
