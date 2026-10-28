import Decoupling.HighDim.Ext
import Mathlib.GroupTheory.Index
import Mathlib.RingTheory.Finiteness.Cardinality

/-!
# The actual common kernel of the layer translation actions

Source: `drafts/main.tex` 639–680. This defines Lambda0 as the full common
kernel, not as an unspecified smaller rectangular lattice. Finite index is
deduced from finite dimensionality over a finite field. No layer is assumed
nonzero. Full rank and lattice-basis selection are separate obligations.
-/

namespace Decoupling.HighDim.Translations

open CategoryTheory Layers
noncomputable section
attribute [local instance] Classical.propDecidable

variable {K : Type} [CommRing K] {D : ℕ}

def translationEquiv (M : ModuleCat (Laurent K D)) (a : Translation D) :
    coefficients M ≃ₗ[K] coefficients M where
  toFun m := monomial K a • (show M from m)
  invFun m := monomial K (-a) • (show M from m)
  left_inv m := by
    change monomial K (-a) • (monomial K a • (show M from m)) = m
    rw [← mul_smul, monomial_neg_mul, one_smul]
  right_inv m := by
    change monomial K a • (monomial K (-a) • (show M from m)) = m
    rw [← mul_smul, monomial_mul_neg, one_smul]
  map_add' m n := by
    exact smul_add (monomial K a) (show M from m) (show M from n)
  map_smul' c m := by
    change monomial K a • (constant (D := D) c • (show M from m)) =
      constant (D := D) c • (monomial K a • (show M from m))
    exact smul_comm _ _ _

def representation (M : ModuleCat (Laurent K D)) :
    Multiplicative (Translation D) →* (coefficients M ≃ₗ[K] coefficients M) where
  toFun a := translationEquiv M a.toAdd
  map_one' := by
    ext m
    change monomial K (0 : Translation D) • (show M from m) = m
    rw [monomial_zero, one_smul]
  map_mul' a b := by
    ext m
    change monomial K (a.toAdd + b.toAdd) • (show M from m) =
      monomial K a.toAdd • (monomial K b.toAdd • (show M from m))
    rw [← monomial_mul, mul_smul]

variable {ι : Type} (E : ι → ModuleCat (Laurent K D))

def retained : AddSubgroup (Translation D) :=
  (MonoidHom.pi (fun i => representation (E i))).ker.toAddSubgroup

theorem mem_retained_iff (a : Translation D) :
    a ∈ retained E ↔ ∀ i, representation (E i) (Multiplicative.ofAdd a) = 1 := by
  change (fun i => representation (E i) (Multiplicative.ofAdd a)) =
    (1 : ∀ i, coefficients (E i) ≃ₗ[K] coefficients (E i)) ↔ _
  exact funext_iff

theorem mem_retained_iff_fixes (a : Translation D) :
    a ∈ retained E ↔ ∀ i, ∀ e : E i, monomial K a • e = e := by
  rw [mem_retained_iff]
  constructor
  · intro h i e
    exact DFunLike.congr_fun (h i) e
  · intro h i
    ext e
    exact h i e

theorem retained_eq_top_of_subsingleton [∀ i, Subsingleton (E i)] : retained E = ⊤ := by
  apply top_unique
  intro a _
  exact (mem_retained_iff_fixes E a).mpr (fun i e => Subsingleton.elim _ _)

end

noncomputable section
variable {K : Type} [Field K] [Finite K] {D : ℕ} {ι : Type} [Finite ι]
variable (E : ι → ModuleCat (Laurent K D))

theorem retained_finiteIndex [∀ i, FiniteDimensional K (Layers.coefficients (E i))] :
    (retained E).FiniteIndex := by
  let : ∀ i, Finite (Layers.coefficients (E i)) := fun i => Module.finite_of_finite K
  let : ∀ i, Finite (Layers.coefficients (E i) ≃ₗ[K] Layers.coefficients (E i)) :=
    fun i => Finite.of_injective
      (fun e : Layers.coefficients (E i) ≃ₗ[K] Layers.coefficients (E i) =>
        (e : Layers.coefficients (E i) → Layers.coefficients (E i))) DFunLike.coe_injective
  apply Subgroup.finiteIndex_toAddSubgroup_iff.mpr
  infer_instance

end

noncomputable section
variable {p D q s r : ℕ} [Fact p.Prime]

abbrev PositiveDegree (D : ℕ) := {j : Fin D // 0 < j.val}

def layerFamily (c : CSS.Checks (ZMod p) D q s r) (j : PositiveDegree D) :
    ModuleCat (Laurent (ZMod p) D) := Layers.layer c j.val.val

/-- Exactly the Lambda0 in Theorem 1, using the genuine Ext layers. -/
def lambda0 (c : CSS.Checks (ZMod p) D q s r) : AddSubgroup (Translation D) :=
  retained (layerFamily c)

theorem lambda0_finiteIndex (c : CSS.Checks (ZMod p) D q s r) (h : Layers.FiniteXLayers c) :
    (lambda0 c).FiniteIndex := by
  let : ∀ j : PositiveDegree D,
      FiniteDimensional (ZMod p) (Layers.coefficients (layerFamily c j)) :=
    fun j => h j.val.val j.property j.val.isLt
  exact retained_finiteIndex (layerFamily c)

theorem mem_lambda0_iff (c : CSS.Checks (ZMod p) D q s r) (a : Translation D) :
    a ∈ lambda0 c ↔ ∀ j : ℕ, 1 ≤ j → j < D →
      ∀ e : Layers.layer c j, monomial (ZMod p) a • e = e := by
  rw [lambda0, mem_retained_iff_fixes]
  constructor
  · intro h j hj hjD e
    exact h ⟨⟨j, hjD⟩, hj⟩ e
  · intro h j e
    exact h j.val.val j.property j.val.isLt e

end
end Decoupling.HighDim.Translations
