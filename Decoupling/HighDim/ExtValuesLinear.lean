import Decoupling.HighDim.ExtValuesTensorTable
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear

/-!
# Prime-field linear native Ext tables

All additive table equivalences are explicitly promoted to F_p-linear
isomorphisms using the canonical scalar actions on the actual native Ext
and on the actual cochains.
-/
namespace Decoupling.HighDim.ExtValues
open CategoryTheory CategoryTheory.Abelian Koszul TrivialLayers
open scoped ModuleCat.Algebra
noncomputable section
variable {p D : ℕ} [Fact p.Prime]

def finiteExtLinearEquiv (B A : ModuleCat (Laurent (ZMod p) D))
    [FiniteDimensional (ZMod p) (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A) (n : ℕ) :
    Ext B A n ≃ₗ[ZMod p]
      (Cell D n → (Layers.coefficients B →ₗ[ZMod p] Layers.coefficients A)) :=
  { finiteExtEquiv B A hB hA n with
    map_smul' := ZMod.map_smul (finiteExtEquiv B A hB hA n) }

def nativeAlternatingLinearEquiv (B A : ModuleCat (Laurent (ZMod p) D))
    [FiniteDimensional (ZMod p) (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A) (n : ℕ) :
    Ext B A n ≃ₗ[ZMod p]
      ((Fin D → ZMod p) [⋀^Fin n]→ₗ[ZMod p]
        (Layers.coefficients B →ₗ[ZMod p] Layers.coefficients A)) :=
  { nativeAlternatingEquiv B A hB hA n with
    map_smul' := ZMod.map_smul (nativeAlternatingEquiv B A hB hA n) }

end
end Decoupling.HighDim.ExtValues

namespace Decoupling.HighDim.ExtValuesTensor
open CategoryTheory CategoryTheory.Abelian Koszul TrivialLayers
open scoped ModuleCat.Algebra
noncomputable section
variable {p D : ℕ} [Fact p.Prime]

def tensorExtLinearEquiv (B A : ModuleCat (Laurent (ZMod p) D))
    [FiniteDimensional (ZMod p) (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference (ZMod p) i • a = 0) (n : ℕ) :
    Ext B A n ≃ₗ[ZMod p] ((tensorComplex B).X n ⟶ A) :=
  { tensorExtEquiv B A hB hA n with
    map_smul' := ZMod.map_smul (tensorExtEquiv B A hB hA n) }

end
end Decoupling.HighDim.ExtValuesTensor
