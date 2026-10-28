import Decoupling.GeneralLatticePhysical
import Decoupling.ExtLayers
import Mathlib.Algebra.Category.ModuleCat.ChangeOfRingsExact
import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
import Mathlib.CategoryTheory.Abelian.Exact

/-!
# Genuine derived Ext under arbitrary finite-index lattice restriction

The trace perfect pairing identifies coextension of the retained ring with
the original Laurent ring. Restriction/coextension adjunction then gives
the comparison in every degree, using actual derived-category Ext.
-/

namespace Decoupling.GeneralLatticeExt

open GeneralLatticeRestriction CategoryTheory CategoryTheory.Abelian
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

variable (Λ : AddSubgroup Translation) [Λ.FiniteIndex]

abbrev restriction : ModuleCat R ⥤ ModuleCat (S Λ) :=
  ModuleCat.restrictScalars (algebraMap (S Λ) R)

abbrev coextension : ModuleCat (S Λ) ⥤ ModuleCat R :=
  ModuleCat.coextendScalars (algebraMap (S Λ) R)

def restrictedSelfEquiv : R ≃ₗ[S Λ] (restriction Λ).obj (ModuleCat.of R R) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

instance restrictedSelfFree : Module.Free (S Λ) ((restriction Λ).obj (ModuleCat.of R R)) :=
  Module.Free.of_equiv (restrictedSelfEquiv Λ)

instance coextension_additive : (coextension Λ).Additive where
  map_add := rfl

instance coextension_preservesEpis : (coextension Λ).PreservesEpimorphisms where
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

instance coextension_preservesFiniteLimits : Limits.PreservesFiniteLimits (coextension Λ) :=
  inferInstanceAs (Limits.PreservesFiniteLimits
    (ModuleCat.coextendScalars (algebraMap (S Λ) R)))

instance coextension_preservesFiniteColimits : Limits.PreservesFiniteColimits (coextension Λ) := by
  let : (coextension Λ).PreservesHomology :=
    Functor.preservesHomology_of_preservesEpis_and_kernels (coextension Λ)
  exact Functor.preservesFiniteColimits_of_preservesHomology (coextension Λ)

/-- The perfect pairing is linear for the coinduced full-ring action. -/
def coextensionSelfEquiv : R ≃ₗ[R] (coextension Λ).obj (ModuleCat.of (S Λ) (S Λ)) where
  toFun r := (ModuleCat.CoextendScalars.equiv _ _).symm
    ((pairingMap Λ r).comp (restrictedSelfEquiv Λ).symm.toLinearMap)
  invFun g := (pairingEquiv Λ).symm
    ((ModuleCat.CoextendScalars.equiv _ _ g).comp (restrictedSelfEquiv Λ).toLinearMap)
  left_inv r := by
    change (pairingEquiv Λ).symm (pairingEquiv Λ r) = r
    exact (pairingEquiv Λ).symm_apply_apply r
  right_inv g := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    exact DFunLike.congr_fun ((pairingEquiv Λ).apply_symm_apply
      ((ModuleCat.CoextendScalars.equiv _ _ g).comp (restrictedSelfEquiv Λ).toLinearMap)) a
  map_add' r s := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change τ Λ ((show R from a) * (r + s)) =
      τ Λ ((show R from a) * r) + τ Λ ((show R from a) * s)
    rw [mul_add, map_add]
  map_smul' r s := by
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change τ Λ ((show R from a) * (r * s)) = τ Λ (((show R from a) * r) * s)
    rw [mul_assoc]

instance restriction_linear : (restriction Λ).Linear (S Λ) where
  map_smul _ _ := rfl

instance coextension_linear : (coextension Λ).Linear (S Λ) where
  map_smul {X Y} f r := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    apply ModuleCat.CoextendScalars.ext
    apply LinearMap.ext
    intro a
    change r • f (g (show R from a)) =
      f (g ((show R from a) * algebraMap (S Λ) R r))
    rw [mul_comm]
    change r • f ((ModuleCat.CoextendScalars.equiv _ X g) a) =
      f ((ModuleCat.CoextendScalars.equiv _ X g) (r • a))
    rw [map_smul, map_smul]

def coextensionSelfIso : ModuleCat.of R R ≅ (coextension Λ).obj (ModuleCat.of (S Λ) (S Λ)) :=
  (coextensionSelfEquiv Λ).toModuleIso

/-- Transport the second variable of genuine Ext through the proved trace pairing. -/
def targetEquiv (M : ModuleCat R) (i : ℕ) :
    Ext M (ModuleCat.of R R) i ≃ₗ[S Λ]
      Ext M ((coextension Λ).obj (ModuleCat.of (S Λ) (S Λ))) i where
  toLinearMap := (Ext.mk₀ (coextensionSelfIso Λ).hom).postcompOfLinear (S Λ) M (add_zero i)
  invFun e := e.comp (Ext.mk₀ (coextensionSelfIso Λ).inv) (add_zero i)
  left_inv e := by
    change (e.comp (Ext.mk₀ (coextensionSelfIso Λ).hom) (add_zero i)).comp
      (Ext.mk₀ (coextensionSelfIso Λ).inv) (add_zero i) = e
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.hom_inv_id, Ext.comp_mk₀_id]
  right_inv e := by
    change (e.comp (Ext.mk₀ (coextensionSelfIso Λ).inv) (add_zero i)).comp
      (Ext.mk₀ (coextensionSelfIso Λ).hom) (add_zero i) = e
    rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.comp_mk₀_id]

/-- Native derived Ext duality under arbitrary finite-index restriction,
in every nonnegative degree. -/
def extEquiv (M : ModuleCat R) (i : ℕ) :
    Ext M (ModuleCat.of R R) i ≃ₗ[S Λ]
      Ext ((restriction Λ).obj M) (ModuleCat.of (S Λ) (S Λ)) i :=
  (targetEquiv Λ M i).trans
    ((ModuleCat.restrictCoextendScalarsAdj (algebraMap (S Λ) R)).extLinearEquiv (S Λ)).symm

/-- The actual trace as a morphism out of the scalar-restricted coefficient module. -/
def traceMorphism : (restriction Λ).obj (ModuleCat.of R R) ⟶ ModuleCat.of (S Λ) (S Λ) :=
  ModuleCat.ofHom ((τ Λ).comp (restrictedSelfEquiv Λ).symm.toLinearMap)

theorem pairing_counit :
    (restriction Λ).map (coextensionSelfIso Λ).hom ≫
      (ModuleCat.restrictCoextendScalarsAdj (algebraMap (S Λ) R)).counit.app
        (ModuleCat.of (S Λ) (S Λ)) = traceMorphism Λ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro r
  change τ Λ (1 * (show R from r)) = τ Λ (show R from r)
  rw [one_mul]

/-- The abstract adjunction equivalence is exactly restriction of the
derived extension followed by coefficient extraction. -/
theorem extEquiv_apply (M : ModuleCat R) (i : ℕ) (e : Ext M (ModuleCat.of R R) i) :
    extEquiv Λ M i e =
      (e.mapExactFunctor (restriction Λ)).comp (Ext.mk₀ (traceMorphism Λ)) (add_zero i) := by
  change ((e.comp (Ext.mk₀ (coextensionSelfIso Λ).hom) (add_zero i)).mapExactFunctor
    (restriction Λ)).comp (Ext.mk₀
      ((ModuleCat.restrictCoextendScalarsAdj (algebraMap (S Λ) R)).counit.app
        (ModuleCat.of (S Λ) (S Λ)))) (add_zero i) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀, pairing_counit]

theorem extEquiv_naturality {M N : ModuleCat R} (f : M ⟶ N) (i : ℕ)
    (e : Ext N (ModuleCat.of R R) i) :
    extEquiv Λ M i ((Ext.mk₀ f).comp e (zero_add i)) =
      (Ext.mk₀ ((restriction Λ).map f)).comp (extEquiv Λ N i e) (zero_add i) := by
  rw [extEquiv_apply, extEquiv_apply, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.comp_assoc_of_third_deg_zero]

@[simp] theorem extEquiv_mk₀ {M : ModuleCat R} (f : M ⟶ ModuleCat.of R R) :
    extEquiv Λ M 0 (Ext.mk₀ f) =
      Ext.mk₀ ((restriction Λ).map f ≫ traceMorphism Λ) := by
  rw [extEquiv_apply, Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

def conjugateS (M : ModuleCat (S Λ)) : ModuleCat (S Λ) :=
  (ModuleCat.restrictScalars (barS Λ).toRingHom).obj M

/-- Conjugation and scalar restriction commute for the literal subgroup subring. -/
def conjugationRestrictionEquiv (M : ModuleCat R) :
    (restriction Λ).obj (ExtLayers.conjugate M) ≃ₗ[S Λ]
      conjugateS Λ ((restriction Λ).obj M) where
  toFun x := x
  invFun x := x
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' s x := by
    change bar (s : R) • (show M from x) = (barS Λ s : R) • (show M from x)
    rw [coe_barS]

def conjugateMapEquiv {M N : ModuleCat (S Λ)} (e : M ≃ₗ[S Λ] N) :
    conjugateS Λ M ≃ₗ[S Λ] conjugateS Λ N where
  toFun x := e (show M from x)
  invFun x := e.symm (show N from x)
  left_inv x := e.symm_apply_apply x
  right_inv x := e.apply_symm_apply x
  map_add' x y := e.map_add x y
  map_smul' s x := e.map_smul (barS Λ s) x

def sourceEquiv {M N : ModuleCat (S Λ)} (e : M ≅ N) (T : ModuleCat (S Λ)) (i : ℕ) :
    Ext M T i ≃ₗ[S Λ] Ext N T i where
  toLinearMap := (Ext.mk₀ e.inv).precompOfLinear (S Λ) T (zero_add i)
  invFun a := (Ext.mk₀ e.hom).comp a (zero_add i)
  left_inv a := by
    change (Ext.mk₀ e.hom).comp ((Ext.mk₀ e.inv).comp a (zero_add i)) (zero_add i) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.hom_inv_id, Ext.mk₀_id_comp]
  right_inv a := by
    change (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp a (zero_add i)) (zero_add i) = a
    rw [Ext.mk₀_comp_mk₀_assoc, e.inv_hom_id, Ext.mk₀_id_comp]

/-- The manuscript's conjugated Ext convention commutes with arbitrary
finite-index lattice restriction, in every degree. -/
def conjugateExtEquiv (M : ModuleCat R) (i : ℕ) :
    Ext (ExtLayers.conjugate M) (ModuleCat.of R R) i ≃ₗ[S Λ]
      Ext (conjugateS Λ ((restriction Λ).obj M)) (ModuleCat.of (S Λ) (S Λ)) i :=
  (extEquiv Λ (ExtLayers.conjugate M) i).trans
    (sourceEquiv Λ (conjugationRestrictionEquiv Λ M).toModuleIso _ i)

end

end Decoupling.GeneralLatticeExt
