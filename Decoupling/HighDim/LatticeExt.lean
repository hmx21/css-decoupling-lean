import Decoupling.HighDim.LatticePhysical
import Decoupling.HighDim.Ext
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Genuine derived Ext under arbitrary finite-index lattice restriction

The trace perfect pairing identifies coextension of the retained ring with
the original Laurent ring. Restriction/coextension adjunction then gives
the comparison in every degree, using actual derived-category Ext.
Source: `drafts/appendix.tex:263–306`. This provides natural Ext equivalences
for arbitrary dimension and coefficients; it does not yet provide the
isomorphism of the entire derived profile.
-/

namespace Decoupling.HighDim.LatticeExt

open LatticeRestriction CategoryTheory CategoryTheory.Abelian
open scoped ModuleCat.Algebra

noncomputable section

set_option backward.isDefEq.respectTransparency false

/-- Bundle a linear equivalence between already bundled modules, avoiding
any change of their given module structures. -/
def moduleIso {A : Type} [CommRing A] {M N : ModuleCat A} (e : M ≃ₗ[A] N) : M ≅ N where
  hom := ModuleCat.ofHom e.toLinearMap
  inv := ModuleCat.ofHom e.symm.toLinearMap
  hom_inv_id := by ext x; exact e.symm_apply_apply x
  inv_hom_id := by ext x; exact e.apply_symm_apply x

variable (K : Type) [CommRing K] {D : ℕ}

variable (Λ : AddSubgroup (Translation D)) [Λ.FiniteIndex]

abbrev restriction : ModuleCat (Laurent K D) ⥤ ModuleCat (S K Λ) :=
  ModuleCat.restrictScalars (algebraMap (S K Λ) (Laurent K D))

abbrev coextension : ModuleCat (S K Λ) ⥤ ModuleCat (Laurent K D) :=
  ModuleCat.coextendScalars (algebraMap (S K Λ) (Laurent K D))

def restrictedSelfEquiv : (Laurent K D) ≃ₗ[S K Λ] (restriction K Λ).obj (ModuleCat.of (Laurent K D) (Laurent K D)) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance restrictedSelfFree : Module.Free (S K Λ) ((restriction K Λ).obj (ModuleCat.of (Laurent K D) (Laurent K D))) :=
  Module.Free.of_equiv (restrictedSelfEquiv K Λ)

instance coextension_additive : (coextension K Λ).Additive where
  map_add := rfl

instance coextension_preservesEpis : (coextension K Λ).PreservesEpimorphisms where
  preserves {X Y} f _ := by
    apply (ModuleCat.epi_iff_surjective _).mpr
    intro g
    obtain ⟨h, hh⟩ := Module.projective_lifting_property f.hom
      (ModuleCat.CoextendScalars.equiv _ Y g) ((ModuleCat.epi_iff_surjective f).mp inferInstance)
    refine ⟨(ModuleCat.CoextendScalars.equiv _ X).symm h, ?_⟩
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    exact DFunLike.congr_fun hh a

instance coextension_preservesFiniteLimits : Limits.PreservesFiniteLimits (coextension K Λ) :=
  inferInstanceAs (Limits.PreservesFiniteLimits
    (ModuleCat.coextendScalars (algebraMap (S K Λ) (Laurent K D))))

instance coextension_preservesFiniteColimits : Limits.PreservesFiniteColimits (coextension K Λ) := by
  let : (coextension K Λ).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (coextension K Λ)
  exact Functor.preservesFiniteColimits_of_preservesHomology (coextension K Λ)

/-- The perfect pairing is linear for the coinduced full-ring action. -/
def coextensionSelfEquiv : (Laurent K D) ≃ₗ[(Laurent K D)] (coextension K Λ).obj (ModuleCat.of (S K Λ) (S K Λ)) where
  toFun r := (ModuleCat.CoextendScalars.equiv _ _).symm
    ((pairingMap K Λ r).comp (restrictedSelfEquiv K Λ).symm.toLinearMap)
  invFun g := (pairingEquiv K Λ).symm
    ((ModuleCat.CoextendScalars.equiv _ _ g).comp (restrictedSelfEquiv K Λ).toLinearMap)
  left_inv r := by
    change (pairingEquiv K Λ).symm (pairingEquiv K Λ r) = r
    exact (pairingEquiv K Λ).symm_apply_apply r
  right_inv g := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    exact DFunLike.congr_fun ((pairingEquiv K Λ).apply_symm_apply
      ((ModuleCat.CoextendScalars.equiv _ _ g).comp (restrictedSelfEquiv K Λ).toLinearMap)) a
  map_add' r s := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change τ K Λ ((show (Laurent K D) from a) * (r + s)) =
      τ K Λ ((show (Laurent K D) from a) * r) + τ K Λ ((show (Laurent K D) from a) * s)
    rw [mul_add, map_add]
  map_smul' r s := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change τ K Λ ((show (Laurent K D) from a) * (r * s)) = τ K Λ (((show (Laurent K D) from a) * r) * s)
    rw [mul_assoc]

instance restriction_linear : (restriction K Λ).Linear (S K Λ) where
  map_smul _ _ := rfl

instance coextension_linear : (coextension K Λ).Linear (S K Λ) where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change r • f (g (show (Laurent K D) from a)) =
      f (g ((show (Laurent K D) from a) * algebraMap (S K Λ) (Laurent K D) r))
    rw [mul_comm]
    change r • f ((ModuleCat.CoextendScalars.equiv _ X g) a) =
      f ((ModuleCat.CoextendScalars.equiv _ X g) (r • a))
    rw [map_smul, map_smul]

def coextensionSelfIso : ModuleCat.of (Laurent K D) (Laurent K D) ≅ (coextension K Λ).obj (ModuleCat.of (S K Λ) (S K Λ)) :=
  (coextensionSelfEquiv K Λ).toModuleIso

/-- Transport the second variable of genuine Ext through the proved trace pairing. -/
def targetEquiv (M : ModuleCat (Laurent K D)) (i : ℕ) :
    Ext M (ModuleCat.of (Laurent K D) (Laurent K D)) i ≃ₗ[S K Λ]
      Ext M ((coextension K Λ).obj (ModuleCat.of (S K Λ) (S K Λ))) i where
  toLinearMap := (Ext.mk₀ (coextensionSelfIso K Λ).hom).postcompOfLinear (S K Λ) M (add_zero i)
  invFun e := e.comp (Ext.mk₀ (coextensionSelfIso K Λ).inv) (add_zero i)
  left_inv e := by
    change (e.comp (Ext.mk₀ (coextensionSelfIso K Λ).hom) (add_zero i)).comp
      (Ext.mk₀ (coextensionSelfIso K Λ).inv) (add_zero i) = e
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id]
  right_inv e := by
    change (e.comp (Ext.mk₀ (coextensionSelfIso K Λ).inv) (add_zero i)).comp
      (Ext.mk₀ (coextensionSelfIso K Λ).hom) (add_zero i) = e
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id]

/-- Native derived Ext duality under arbitrary finite-index restriction,
in every nonnegative degree. -/
def extEquiv (M : ModuleCat (Laurent K D)) (i : ℕ) :
    Ext M (ModuleCat.of (Laurent K D) (Laurent K D)) i ≃ₗ[S K Λ]
      Ext ((restriction K Λ).obj M) (ModuleCat.of (S K Λ) (S K Λ)) i :=
  (targetEquiv K Λ M i).trans
    ((ModuleCat.restrictCoextendScalarsAdj (algebraMap (S K Λ) (Laurent K D))).extLinearEquiv (S K Λ)).symm

/-- The actual trace as a morphism out of the scalar-restricted coefficient module. -/
def traceMorphism : (restriction K Λ).obj (ModuleCat.of (Laurent K D) (Laurent K D)) ⟶ ModuleCat.of (S K Λ) (S K Λ) :=
  ModuleCat.ofHom ((τ K Λ).comp (restrictedSelfEquiv K Λ).symm.toLinearMap)

theorem pairing_counit :
    (restriction K Λ).map (coextensionSelfIso K Λ).hom ≫
      (ModuleCat.restrictCoextendScalarsAdj (algebraMap (S K Λ) (Laurent K D))).counit.app
        (ModuleCat.of (S K Λ) (S K Λ)) = traceMorphism K Λ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change τ K Λ (1 * (show (Laurent K D) from r)) = τ K Λ (show (Laurent K D) from r)
  rw [one_mul]

/-- The abstract adjunction equivalence is exactly restriction of the
derived extension followed by coefficient extraction. -/
theorem extEquiv_apply (M : ModuleCat (Laurent K D)) (i : ℕ) (e : Ext M (ModuleCat.of (Laurent K D) (Laurent K D)) i) :
    extEquiv K Λ M i e =
      (e.mapExactFunctor (restriction K Λ)).comp (Ext.mk₀ (traceMorphism K Λ)) (add_zero i) := by
  change ((e.comp (Ext.mk₀ (coextensionSelfIso K Λ).hom) (add_zero i)).mapExactFunctor
    (restriction K Λ)).comp (Ext.mk₀
      ((ModuleCat.restrictCoextendScalarsAdj (algebraMap (S K Λ) (Laurent K D))).counit.app
        (ModuleCat.of (S K Λ) (S K Λ)))) (add_zero i) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, pairing_counit]

theorem extEquiv_naturality {M N : ModuleCat (Laurent K D)} (f : M ⟶ N) (i : ℕ)
    (e : Ext N (ModuleCat.of (Laurent K D) (Laurent K D)) i) :
    extEquiv K Λ M i ((Ext.mk₀ f).comp e (zero_add i)) =
      (Ext.mk₀ ((restriction K Λ).map f)).comp (extEquiv K Λ N i e) (zero_add i) := by
  rw [extEquiv_apply, extEquiv_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

@[simp] theorem extEquiv_mk₀ {M : ModuleCat (Laurent K D)} (f : M ⟶ ModuleCat.of (Laurent K D) (Laurent K D)) :
    extEquiv K Λ M 0 (Ext.mk₀ f) =
      Ext.mk₀ ((restriction K Λ).map f ≫ traceMorphism K Λ) := by
  rw [extEquiv_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

def conjugateS (M : ModuleCat (S K Λ)) : ModuleCat (S K Λ) :=
  (ModuleCat.restrictScalars (barS K Λ).toRingHom).obj M

/-- Conjugation and scalar restriction commute for the literal subgroup subring. -/
def conjugationRestrictionEquiv (M : ModuleCat (Laurent K D)) :
    (restriction K Λ).obj (Layers.conjugate M) ≃ₗ[S K Λ]
      conjugateS K Λ ((restriction K Λ).obj M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s x := by
    change bar (s : (Laurent K D)) • (show M from x) = (barS K Λ s : (Laurent K D)) • (show M from x)
    rw [coe_barS]

def conjugateMapEquiv {M N : ModuleCat (S K Λ)} (e : M ≃ₗ[S K Λ] N) :
    conjugateS K Λ M ≃ₗ[S K Λ] conjugateS K Λ N where
  toFun x := e (show M from x)
  invFun x := e.symm (show N from x)
  left_inv x := e.symm_apply_apply x
  right_inv x := e.apply_symm_apply x
  map_add' x y := e.map_add x y
  map_smul' s x := e.map_smul (barS K Λ s) x

def sourceEquiv {M N : ModuleCat (S K Λ)} (e : M ≅ N) (T : ModuleCat (S K Λ)) (i : ℕ) :
    Ext M T i ≃ₗ[S K Λ] Ext N T i where
  toLinearMap := (Ext.mk₀ e.inv).precompOfLinear (S K Λ) T (zero_add i)
  invFun a := (Ext.mk₀ e.hom).comp a (zero_add i)
  left_inv a := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add i)) (zero_add i) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv a := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add i)) (zero_add i) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

/-- The manuscript's conjugated Ext convention commutes with arbitrary
finite-index lattice restriction, in every degree. -/
def conjugateExtEquiv (M : ModuleCat (Laurent K D)) (i : ℕ) :
    Ext (Layers.conjugate M) (ModuleCat.of (Laurent K D) (Laurent K D)) i ≃ₗ[S K Λ]
      Ext (conjugateS K Λ ((restriction K Λ).obj M)) (ModuleCat.of (S K Λ) (S K Λ)) i :=
  (extEquiv K Λ (Layers.conjugate M) i).trans
    (sourceEquiv K Λ (conjugationRestrictionEquiv K Λ M).toModuleIso _ i)

end

end Decoupling.HighDim.LatticeExt
