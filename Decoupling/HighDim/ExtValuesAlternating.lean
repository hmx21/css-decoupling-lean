import Decoupling.HighDim.ExtValuesFinite
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Ordered-cell tables and alternating forms

Source: equation `eq:kappa-values` following Lemma `lem:values`.
The equivalence is the universal property of genuine exterior powers,
with the ordered-cell basis identified with the standard wedge basis.
-/

namespace Decoupling.HighDim.ExtValues

open Koszul
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type*) [CommRing K] (D n : ℕ)

/-- The standard exterior-power basis, indexed by the exact ordered cells
used in the project's Laurent Koszul complex. -/
def exteriorCellBasis : Module.Basis (Cell D n) K (⋀[K]^n (Fin D → K)) :=
  ((Pi.basisFun K (Fin D)).exteriorPower n).reindex Set.powersetCard.ofFinEmbEquiv.symm

theorem exteriorCellBasis_apply (I : Cell D n) :
    exteriorCellBasis K D n I =
      exteriorPower.ιMulti K n (fun i => Pi.single (I i) 1) := by
  simp [exteriorCellBasis, Module.Basis.reindex_apply,
    exteriorPower.basis_apply, exteriorPower.ιMulti_family]
  congr 1
  funext i
  exact Pi.basisFun_apply K (Fin D) (I i)

theorem exteriorCellBasis_repr (v : Fin n → (Fin D → K)) (I : Cell D n) :
    (exteriorCellBasis K D n).repr (exteriorPower.ιMulti K n v) I =
      Matrix.det (fun i j => v i (I j)) := by
  simp [exteriorCellBasis, Module.Basis.repr_reindex,
    exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  rfl

variable {K D n}
variable (V : Type*) [AddCommGroup V] [Module K V]

/-- Arbitrary Hom-valued ordered tables are exactly alternating forms.
No divisibility by n! or restriction on characteristic is used. -/
def tableAlternatingEquiv : (Cell D n → V) ≃ₗ[K]
    AlternatingMap K (Fin D → K) V (Fin n) :=
  ((exteriorCellBasis K D n).constr K).trans
    exteriorPower.alternatingMapLinearEquiv.symm

theorem tableAlternatingEquiv_basis (v : Cell D n → V) (I : Cell D n) :
    tableAlternatingEquiv (K := K) V v (fun i => Pi.single (I i) 1) = v I := by
  simp only [tableAlternatingEquiv, LinearEquiv.trans_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply,
    LinearMap.compAlternatingMap_apply, ← exteriorCellBasis_apply]
  exact (exteriorCellBasis K D n).constr_basis K v I

/-- The signed minors formula, valid over every commutative ring. -/
theorem tableAlternatingEquiv_apply (f : Cell D n → V)
    (v : Fin n → (Fin D → K)) :
    tableAlternatingEquiv (K := K) V f v =
      ∑ I : Cell D n, Matrix.det (fun i j => v i (I j)) • f I := by
  simp only [tableAlternatingEquiv, LinearEquiv.trans_apply,
    exteriorPower.alternatingMapLinearEquiv_symm_apply,
    LinearMap.compAlternatingMap_apply, Module.Basis.constr_apply_fintype]
  apply Finset.sum_congr rfl
  intro I _
  rw [Module.Basis.equivFun_apply, exteriorCellBasis_repr]

variable {V}

theorem alternating_eq_zero_iff_cell_values
    (f : AlternatingMap K (Fin D → K) V (Fin n)) :
    f = 0 ↔ ∀ I : Cell D n, f (fun i => Pi.single (I i) 1) = 0 := by
  constructor
  · intro h I; simp [h]
  · intro h
    obtain ⟨v, rfl⟩ := (tableAlternatingEquiv (K := K) V).surjective f
    have hv : v = 0 := by
      funext I
      simpa only [tableAlternatingEquiv_basis, Pi.zero_apply] using h I
    simp [hv]

theorem alternating_comp_eq_zero_iff_range
    (f : AlternatingMap K (Fin D → K) V (Fin n))
    (a : (Fin D → K) →ₗ[K] (Fin D → K)) :
    f.compLinearMap a = 0 ↔
      ∀ v : Fin n → (Fin D → K), (∀ i, v i ∈ LinearMap.range a) → f v = 0 := by
  constructor
  · intro h v hv
    choose u hu using hv
    have he : v = a ∘ u := funext fun i => (hu i).symm
    rw [he]
    exact DFunLike.congr_fun h u
  · intro h
    apply AlternatingMap.ext
    intro u
    exact h (fun i => a (u i)) (fun i => ⟨u i, rfl⟩)

section Native

variable {K : Type} [Field K] {D : ℕ}
open CategoryTheory CategoryTheory.Abelian TrivialLayers

/-- The basis-independent alternating form of a genuine derived Ext class. -/
def nativeAlternatingEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) :
    Ext B A n ≃+ AlternatingMap K (Fin D → K)
      (Layers.coefficients B →ₗ[K] Layers.coefficients A) (Fin n) :=
  (finiteExtEquiv B A hB hA n).trans
    (tableAlternatingEquiv (Layers.coefficients B →ₗ[K] Layers.coefficients A)).toAddEquiv

theorem nativeAlternatingEquiv_apply (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n)
    (v : Fin n → (Fin D → K)) :
    nativeAlternatingEquiv B A hB hA n e v =
      ∑ I : Cell D n, Matrix.det (fun i j => v i (I j)) • finiteExtEquiv B A hB hA n e I :=
  tableAlternatingEquiv_apply (K := K) _ _ _

@[simp] theorem finiteExtEquiv_apply_basis (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n) (I : Cell D n)
    (i : Fin (Module.finrank K (Layers.coefficients B))) :
    finiteExtEquiv B A hB hA n e I (Module.finBasis K (Layers.coefficients B) i) =
      (show Layers.coefficients A from coefficientTableEquiv A
        (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
          ((Ext.mk₀ (sourceInclusion B hB i)).comp e (zero_add n)) I) := by
  change ((Module.finBasis K (Layers.coefficients B)).constr K _) _ = _
  rw [Module.Basis.constr_basis]
  rfl

theorem nativeAlternatingEquiv_apply_basis (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (hA : AugmentationAction A) (n : ℕ) (e : Ext B A n)
    (v : Fin n → (Fin D → K)) (i : Fin (Module.finrank K (Layers.coefficients B))) :
    nativeAlternatingEquiv B A hB hA n e v (Module.finBasis K (Layers.coefficients B) i) =
      ∑ I : Cell D n, Matrix.det (fun a b => v a (I b)) •
        (show Layers.coefficients A from coefficientTableEquiv A
          (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA) n
            ((Ext.mk₀ (sourceInclusion B hB i)).comp e (zero_add n)) I) := by
  rw [nativeAlternatingEquiv_apply]
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, finiteExtEquiv_apply_basis]

end Native
end
end Decoupling.HighDim.ExtValues
