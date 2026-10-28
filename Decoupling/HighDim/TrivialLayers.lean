import Decoupling.HighDim.LatticeCompatibility
import Decoupling.HighDim.LatticeBasis
import Decoupling.HighDim.KoszulResolution

/-!
# The genuine Ext layers become coefficient modules on their common kernel

Source: `drafts/main.tex`, the definition of Lambda0 and Theorem 1.  The
augmentation action below is proved from the actual monomial action, not
assumed for a renamed Ext object.  Choosing vector-space coordinates changes
neither the underlying coefficient field nor its original finite dimension.
-/

namespace Decoupling.HighDim.TrivialLayers

open CategoryTheory LatticeRestriction
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}

/-- A coefficient vector space, with Laurent scalars acting by augmentation. -/
def coefficientObject (V : ModuleCat K) : ModuleCat (Laurent K D) :=
  (ModuleCat.restrictScalars augmentation).obj V

/-- An explicit assertion about the scalar action on the original module. -/
def AugmentationAction (M : ModuleCat (Laurent K D)) : Prop :=
  ∀ a : Laurent K D, ∀ m : M, a • m = constant (D := D) (augmentation a) • m

/-- The identity on elements is Laurent-linear once its scalar action has
been proved to factor through augmentation. -/
def coefficientEquiv (M : ModuleCat (Laurent K D)) (h : AugmentationAction M) :
    M ≃ₗ[Laurent K D] coefficientObject (D := D) (Layers.coefficients M) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' a m := h a m

section Coordinates

variable [StrongRankCondition K]

/-- A genuine finite coefficient module, with the number of coordinates
equal to the original coefficient-field dimension. -/
def coordinateIso (M : ModuleCat (Laurent K D))
    [Module.Free K (Layers.coefficients M)] [Module.Finite K (Layers.coefficients M)]
    (h : AugmentationAction M) :
    M ≅ coefficientObject (D := D) (ModuleCat.of K
      (Fin (Module.finrank K (Layers.coefficients M)) → K)) :=
  (coefficientEquiv M h).toModuleIso ≪≫
    (ModuleCat.restrictScalars augmentation).mapIso
      (Module.finBasis K (Layers.coefficients M)).equivFun.toModuleIso

end Coordinates

variable (K) (D)

/-- Literal finite coordinates for an augmentation module. -/
abbrev coefficientVector (n : ℕ) : ModuleCat (Laurent K D) :=
  coefficientObject (ModuleCat.of K (Fin n → K))

def coordinateInclusion (n : ℕ) (i : Fin n) :
    Koszul.coefficientModule K D ⟶ coefficientVector K D n :=
  (ModuleCat.restrictScalars augmentation).map (ModuleCat.ofHom (LinearMap.single K (fun _ : Fin n => K) i))

def coordinateProjection (n : ℕ) (i : Fin n) :
    coefficientVector K D n ⟶ Koszul.coefficientModule K D :=
  (ModuleCat.restrictScalars augmentation).map (ModuleCat.ofHom (LinearMap.proj i))

/-- The finite identity decomposition, also valid for n = 0. -/
theorem sum_projection_inclusion (n : ℕ) :
    ∑ i : Fin n, coordinateProjection K D n i ≫ coordinateInclusion K D n i =
      𝟙 (coefficientVector K D n) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  funext j
  simp only [ModuleCat.hom_sum, ModuleCat.hom_comp, ModuleCat.hom_id,
    LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.id_apply]
  change (∑ i : Fin n, Pi.single i (v i)) j = v j
  simp [Finset.sum_apply, Pi.single_apply]

variable {K D}

section Retained

variable (Λ : AddSubgroup (Translation D)) (M : ModuleCat (Laurent K D))

def augmentationS : S K Λ →+* K := augmentation.comp (retained K Λ).subtype

/-- Monomials in the retained lattice fix the module, hence every retained
scalar acts through its coefficient sum. No finite-index assumption is needed. -/
theorem scalar_action_of_fixed
    (h : ∀ a : Λ, ∀ m : M, monomial K (a : Translation D) • m = m)
    (s : S K Λ) (m : M) :
    (s : Laurent K D) • m = constant (D := D) (augmentationS Λ s) • m := by
  obtain ⟨f, rfl⟩ := (latticeEquiv K Λ).surjective s
  change embed K Λ f • m = constant (D := D) (augmentation (embed K Λ f)) • m
  refine AddMonoidAlgebra.induction_on
    (motive := fun f : AddMonoidAlgebra K Λ =>
      embed K Λ f • m = constant (D := D) (augmentation (embed K Λ f)) • m) f ?_ ?_ ?_
  · intro a
    change embed K Λ (AddMonoidAlgebra.single a 1) • m =
      constant (D := D) (augmentation (embed K Λ (AddMonoidAlgebra.single a 1))) • m
    rw [embed_single]
    simpa only [augmentation_single, map_one, one_smul, monomial] using h a m
  · intro f g hf hg
    simp only [map_add, add_smul, hf, hg]
  · intro c f hf
    have hs : c • f = AddMonoidAlgebra.single 0 c * f := by
      ext a
      simp
    rw [hs, map_mul, embed_single]
    change (constant c * embed K Λ f) • m = _
    rw [mul_smul, hf, ← mul_smul, map_mul, augmentation_single, map_mul]

/-- The same elementwise identity, now bundled as an actual isomorphism
over the retained ring. -/
def retainedCoefficientEquiv
    (h : ∀ a : Λ, ∀ m : M, monomial K (a : Translation D) • m = m) :
    (LatticeExt.restriction K Λ).obj M ≃ₗ[S K Λ]
      (ModuleCat.restrictScalars (augmentationS Λ)).obj (Layers.coefficients M) where
  toFun m := m
  invFun m := m
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s m := scalar_action_of_fixed Λ M h s m

end Retained

section Lambda0

variable {p q s r : ℕ} [Fact p.Prime]
  (c : CSS.Checks (ZMod p) D q s r)

/-- The whole actual selected Ext layer has augmentation action on Lambda0. -/
theorem lambda0_scalar_action (j : ℕ) (hj : 1 ≤ j) (hjD : j < D)
    (a : S (ZMod p) (Translations.lambda0 c)) (m : Layers.layer c j) :
    (a : Laurent (ZMod p) D) • m =
      constant (D := D) (augmentationS (Translations.lambda0 c) a) • m :=
  scalar_action_of_fixed (Translations.lambda0 c) (Layers.layer c j)
    (fun a m => (Translations.mem_lambda0_iff c a).mp a.property j hj hjD m) a m

/-- Lambda0 restriction yields precisely t_j coefficient coordinates, where
t_j is the original finrank. This includes zero layers without choosing a vector. -/
def lambda0_layerIso (h : Layers.FiniteXLayers c)
    (j : ℕ) (hj : 1 ≤ j) (hjD : j < D) :
    (LatticeExt.restriction (ZMod p) (Translations.lambda0 c)).obj (Layers.layer c j) ≅
      (ModuleCat.restrictScalars (augmentationS (Translations.lambda0 c))).obj
        (ModuleCat.of (ZMod p) (Fin (Layers.multiplicity c j) → ZMod p)) := by
  letI := h j hj hjD
  exact (retainedCoefficientEquiv (Translations.lambda0 c) (Layers.layer c j)
    (fun a m => (Translations.mem_lambda0_iff c a).mp a.property j hj hjD m)).toModuleIso ≪≫
      (ModuleCat.restrictScalars (augmentationS (Translations.lambda0 c))).mapIso
        (Module.finBasis (ZMod p) (Layers.coefficients (Layers.layer c j))).equivFun.toModuleIso

end Lambda0

end
end Decoupling.HighDim.TrivialLayers
