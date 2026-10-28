import Decoupling.HighDim.KoszulContractionTensor

/-!
# The actual Hom-valued contraction chain map

HD010, Appendix B.3. Each ordered cell gives an iterated interior product
on the literal tensor resolution. A table of coefficient-linear maps is
then combined with those products by a finite sum of genuine cocycles.
-/

namespace Decoupling.HighDim.KoszulContraction
open CategoryTheory CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers ExtValuesTensor CochainComplex.HomComplex
open scoped TensorProduct
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

variable {K : Type} [Field K] {D : ℕ}
  (B A : ModuleCat (Laurent K D))
  [FiniteDimensional K (Layers.coefficients B)]
  [FiniteDimensional K (Layers.coefficients A)]

/-- The literal coefficient map commutes with the tensor differential. -/
def coefficientChain (g : Layers.coefficients B →ₗ[K] Layers.coefficients A) :
    tensorComplex B ⟶ tensorComplex A where
  f q := ModuleCat.ofHom (tensorMap LinearMap.id g)
  comm' i j hij := by
    change j + 1 = i at hij
    subst i
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro z
    induction z using TensorProduct.inductionOn with
    | add x y hx hy => simp_all only [map_add]
    | tmul v b =>
      change (tensorComplex A).d (j + 1) j (tensorMap LinearMap.id g (v ⊗ₜ[K] b)) =
        tensorMap LinearMap.id g ((tensorComplex B).d (j + 1) j (v ⊗ₜ[K] b))
      simp only [tensorComplex_d_tmul, tensorMap_tmul, LinearMap.id_apply]

variable (hB : AugmentationAction B) (hA : AugmentationAction A)

def coefficientMap (g : Layers.coefficients B →ₗ[K] Layers.coefficients A) :
    complex B hB ⟶ complex A hA :=
  HomologicalComplex.extendMap (coefficientChain B A g) ComplexShape.embeddingDownNat

theorem coefficientMap_f (g : Layers.coefficients B →ₗ[K] Layers.coefficients A) (q : ℕ) :
    (coefficientMap B A hB hA g).f (-(q : ℤ)) =
      ((resolution B hB).cochainComplexXIso (-(q : ℤ)) q rfl).hom ≫
        (coefficientChain B A g).f q ≫
          ((resolution A hA).cochainComplexXIso (-(q : ℤ)) q rfl).inv := by
  simp only [coefficientMap, HomologicalComplex.extendMap_f _
    ComplexShape.embeddingDownNat (i := q) (i' := -(q : ℤ)) rfl,
    ProjectiveResolution.cochainComplexXIso]
  rfl

/-- A table produces an actual cocycle, without an assumed compatibility. -/
def tableCocycle (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) :
    Cocycle (complex B hB) (complex A hA) (n : ℤ) :=
  ∑ I : Cell D n, composeCocycle (cellCocycle B hB n I)
    (Cocycle.ofHom (coefficientMap B A hB hA (f I))) (add_zero _)

/-- The genuine shifted chain map lifting the Hom-valued table. -/
def tableMap (n : ℕ)
    (f : Cell D n → (Layers.coefficients B →ₗ[K] Layers.coefficients A)) :
    complex B hB ⟶ (complex A hA)⟦(n : ℤ)⟧ :=
  Cocycle.equivHomShift.symm (tableCocycle B A hB hA n f)

variable {A}

/-- An iterated contraction component, written in literal tensor terms. -/
def cellComponent {n : ℕ} (I : Cell D n) (q : ℕ) :
    (tensorComplex B).X (q + n) ⟶ (tensorComplex B).X q :=
  ((resolution B hB).cochainComplexXIso (-((q + n : ℕ) : ℤ)) (q + n) rfl).inv ≫
    (cellCocycle B hB n I : Cochain (complex B hB) (complex B hB) (n : ℤ)).v
      (-((q + n : ℕ) : ℤ)) (-(q : ℤ)) (by omega) ≫
        ((resolution B hB).cochainComplexXIso (-(q : ℤ)) q rfl).hom

theorem cellComponent_zero (I : Cell D 0) (q : ℕ) :
    cellComponent B hB I q = 𝟙 ((tensorComplex B).X q) := by
  simp [cellComponent, cellCocycle, Cocycle.ofHom]

theorem cellComponent_succ {n : ℕ} (I : Cell D (n + 1)) (q : ℕ) :
    cellComponent B hB I q = direction B (I 0) (q + n) ≫ cellComponent B hB (face I 0) q := by
  dsimp only [cellComponent, cellCocycle, composeCocycle, Cocycle.mk_coe]
  simp only [Cocycle.mk_coe]
  erw [Cochain.comp_v _ _ _ (-((q + (n + 1) : ℕ) : ℤ)) (-((q + n : ℕ) : ℤ))
    (-(q : ℤ)) (by omega) (by omega)]
  simp only [directionCocycle, Cocycle.mk_coe]
  erw [directionCochain_v]
  simp only [Category.assoc]
  erw [Iso.inv_hom_id_assoc]
  rfl

end
end Decoupling.HighDim.KoszulContraction
