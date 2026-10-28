import Decoupling.HighDim.ToricSplitLayers
import Decoupling.HighDim.PostnikovTruncation

/-!
# Canonical gluing vanishes on every genuine split target

Vanishing is proved for every cutoff and is invariant under a mere derived
object isomorphism. No compatibility with a supplied Postnikov tower is required.
-/

namespace Decoupling.HighDim.PostnikovTruncation

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R]

theorem connecting_single (M : ModuleCat R) (j n : ℤ) :
    (triangle ((DerivedCategory.singleFunctor (ModuleCat R) j).obj M) n).mor₃ = 0 := by
  let X := (DerivedCategory.singleFunctor (ModuleCat R) j).obj M
  change (t.truncGEδLT n).app X = 0
  by_cases h : j < n
  · have : t.IsLE X (n - 1) := t.isLE_of_le X j (n - 1) (by omega)
    exact (t.isZero_truncGE_obj_of_isLE (n - 1) n (by omega) X).eq_of_src _ _
  · have : t.IsGE X n := t.isGE_of_ge X n j (by omega)
    have hz := t.isZero_truncLT_obj_of_isGE n X
    exact ((shiftFunctor _ (1 : ℤ)).map_isZero hz).eq_of_tgt _ _

theorem connecting_biproduct {ι : Type} [Fintype ι]
    (X : ι → DerivedCategory (ModuleCat R)) (n : ℤ)
    (h : ∀ i, (triangle (X i) n).mor₃ = 0) :
    (triangle (⨁ X) n).mor₃ = 0 := by
  change (t.truncGEδLT n).app (⨁ X) = 0
  have hid : (t.truncGE n).map (∑ i, biproduct.π X i ≫ biproduct.ι X i) =
      𝟙 ((t.truncGE n).obj (⨁ X)) := by rw [biproduct.total, CategoryTheory.Functor.map_id]
  rw [← Category.id_comp ((t.truncGEδLT n).app (⨁ X)), ← hid,
    Functor.map_sum, Preadditive.sum_comp]
  apply Finset.sum_eq_zero
  intro i _
  rw [Functor.map_comp, Category.assoc, (t.truncGEδLT n).naturality]
  change (t.truncGE n).map (biproduct.π X i) ≫
    (triangle (X i) n).mor₃ ≫ _ = 0
  rw [h i, zero_comp, comp_zero]

theorem connecting_of_iso {X Y : DerivedCategory (ModuleCat R)}
    (e : X ≅ Y) (n : ℤ) (h : (triangle Y n).mor₃ = 0) :
    (triangle X n).mor₃ = 0 := by
  apply (cancel_mono (((t.truncLT n) ⋙ shiftFunctor _ (1 : ℤ)).map e.hom)).mp
  change (t.truncGEδLT n).app X ≫ _ = 0 ≫ _
  rw [← (t.truncGEδLT n).naturality]
  change _ ≫ (triangle Y n).mor₃ = _
  rw [h, comp_zero, zero_comp]

end
end Decoupling.HighDim.PostnikovTruncation

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits
noncomputable section
attribute [local instance] HasDerivedCategory.standard

variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

theorem splitTarget_connecting (n : ℤ) :
    (PostnikovTruncation.triangle (splitTarget K D forms) n).mor₃ = 0 :=
  PostnikovTruncation.connecting_biproduct _ n
    (fun i => PostnikovTruncation.connecting_single _ (forms i + 1) n)

end
end Decoupling.HighDim.Toric
