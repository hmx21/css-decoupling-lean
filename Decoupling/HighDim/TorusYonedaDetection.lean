import Decoupling.HighDim.TorusRepresentable
import Decoupling.HighDim.MinimalLatticeYoneda

/-!
# Transporting native Yoneda detection into the actual Postnikov probe

This module proves the shift and composition comparison. The algebraic
nonvanishing theorem for native Yoneda products is passed explicitly to
this comparison and is discharged in the final application.
-/

namespace Decoupling.HighDim.Torus
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] {D : ℕ}

/-- Native Yoneda-product detection detects actual connecting components
between single layers. Every change of shift is an explicit derived
isomorphism, and the comparison uses the native `Ext.comp_hom` theorem. -/
theorem single_detection_of_native
    (A B : ModuleCat (Laurent K D)) (i j : ℤ) (_hi : 1 ≤ i) (hij : i < j) (hj : j < D)
    (hDetect : ∀ κ : Ext A B (j - i + 1).toNat, κ ≠ 0 →
      ∃ α : Ext (Koszul.coefficientModule K D) A ((D : ℤ) - j).toNat,
        α.comp κ rfl ≠ 0)
    (f : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A ⟶
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj B)⟦(1 : ℤ)⟧)
    (hf : ∀ g : probe K D ⟶ _, g ≫ f = 0) : f = 0 := by
  let m := ((D : ℤ) - j).toNat
  let n := (j - i + 1).toNat
  have hm : (m : ℤ) + j = D := by dsimp [m]; rw [Int.toNat_of_nonneg (by omega)]; omega
  have hn : (n : ℤ) = j - i + 1 := Int.toNat_of_nonneg (by omega)
  let eA : ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A)⟦j⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj A :=
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso j 0 j (by omega)).app A
  let eB₁ : ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj B)⟦(1 : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (i - 1)).obj B :=
    ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso 1 (i - 1) i (by omega)).app B
  let eB : (((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj B)⟦(1 : ℤ)⟧)⟦j⟧ ≅
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj B)⟦(n : ℤ)⟧ :=
    (shiftFunctor (Derived K D) j).mapIso eB₁ ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso j (-n) (i - 1)
        (by omega)).app B ≪≫
      (((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso n (-n) 0
        (by omega)).app B).symm
  let eP : ((probe K D)⟦j⟧)⟦(m : ℤ)⟧ ≅
      (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj
        (Koszul.coefficientModule K D) :=
    (shiftFunctor (Derived K D) (m : ℤ)).mapIso
      (((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso j m D (by omega)).app
        (Koszul.coefficientModule K D)) ≪≫
      ((DerivedCategory.singleFunctors (ModuleCat (Laurent K D))).shiftIso m 0 m (by omega)).app
        (Koszul.coefficientModule K D)
  let κ : Ext A B n := Ext.homEquiv.symm (eA.inv ≫ f⟦j⟧' ≫ eB.hom)
  have hκ : κ = 0 := by
    by_contra hκ
    obtain ⟨α, hα⟩ := hDetect κ hκ
    let G := shiftFunctor (Derived K D) j ⋙ shiftFunctor (Derived K D) (m : ℤ)
    let g' : G.obj (probe K D) ⟶
        G.obj ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A) :=
      eP.hom ≫ α.hom ≫ eA.inv⟦(m : ℤ)⟧'
    let g := G.preimage g'
    have hg : g' ≫ G.map f = 0 := by
      rw [← G.map_preimage g', ← Functor.map_comp, hf, Functor.map_zero]
    have hcomp : α.hom ≫ κ.hom⟦(m : ℤ)⟧' = 0 := by
      have hh := congrArg (fun u => eP.inv ≫ u ≫ eB.hom⟦(m : ℤ)⟧') hg
      simpa only [κ, Ext.hom, Equiv.apply_symm_apply, Functor.map_comp,
        g', G, Functor.comp_map, Category.assoc, Iso.inv_hom_id_assoc,
        comp_zero, zero_comp] using hh
    apply hα
    apply Ext.ext
    rw [Ext.comp_hom, Ext.zero_hom]
    rw [ShiftedHom.comp, ← Category.assoc, hcomp, zero_comp]
  have hzero := congrArg Ext.hom hκ
  rw [Ext.zero_hom] at hzero
  simp only [κ, Ext.hom, Equiv.apply_symm_apply] at hzero

  have hshift : f⟦j⟧' = 0 := by
    apply (cancel_epi eA.inv).mp
    apply (cancel_mono eB.hom).mp
    simpa only [Category.assoc, comp_zero, zero_comp] using hzero
  exact (shiftFunctor (Derived K D) j).map_injective (by simpa using hshift)

/-- Every actual nonzero connecting component is detected by the torus
probe. The needed Yoneda nonvanishing is proved on the native Koszul
resolution in `YonedaDetection.native_detects`. -/
theorem probe_detects_connecting
    (A B : ModuleCat (Laurent K D)) [Module.Finite K (Layers.coefficients A)]
    (hA : TrivialLayers.AugmentationAction A) (hB : TrivialLayers.AugmentationAction B)
    (i j : ℤ) (hi : 1 ≤ i) (hij : i < j) (hj : j < D)
    (f : (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) j).obj A ⟶
      ((DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) i).obj B)⟦(1 : ℤ)⟧)
    (hf : ∀ g : probe K D ⟶ _, g ≫ f = 0) : f = 0 := by
  apply single_detection_of_native A B i j hi hij hj (fun κ hκ => ?_) f hf
  apply YonedaDetection.native_detects K D A B hA hB _ _ _ κ hκ
  have hn : ((j - i + 1).toNat : ℤ) = j - i + 1 := Int.toNat_of_nonneg (by omega)
  have hm : ((((D : ℤ) - j).toNat) : ℤ) = (D : ℤ) - j := Int.toNat_of_nonneg (by omega)
  omega

end
end Decoupling.HighDim.Torus
