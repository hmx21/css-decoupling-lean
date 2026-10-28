import Mathlib.Algebra.Algebra.Bilinear
import Mathlib.LinearAlgebra.Dual.Defs

/-!
# Dual restriction from a perfect coefficient-extraction pairing

This is the general algebraic interface for the dual-restriction equation
of the coarse-graining argument.  The concrete retained Laurent rings instantiate
it in `RestrictionDuality`; their perfect pairing is proved there.
The interface applies to arbitrary modules, and its dual identification
is natural under the original module maps.
-/

noncomputable section

namespace Decoupling.FrobeniusDuality

variable (A B : Type*) [CommRing A] [CommRing B] [Algebra A B]

/-- Data of a coefficient-extraction functional with its proved perfect pairing. -/
structure Pairing where
  trace : B →ₗ[A] A
  dualEquiv : B ≃ₗ[A] (B →ₗ[A] A)
  dual_apply : ∀ r a, dualEquiv r a = trace (a * r)

namespace Pairing

variable {A B}
variable (d : Pairing A B)

/-- The perfect pairing detects equality. -/
theorem separating {r s : B} (h : ∀ a, d.trace (a * r) = d.trace (a * s)) : r = s := by
  apply d.dualEquiv.injective
  apply LinearMap.ext
  intro a
  simpa only [d.dual_apply] using h a

variable {V : Type*} [AddCommGroup V] [Module B V] [Module A V] [IsScalarTower A B V]

/-- The functional in the variable `a` used to reconstruct an `B`-linear dual vector. -/
def orbitFunctional (g : V →ₗ[A] A) (v : V) : B →ₗ[A] A where
  toFun a := g (a • v)
  map_add' a b := by simp [add_smul]
  map_smul' r a := by simp [smul_assoc]

def liftValue (g : V →ₗ[A] A) (v : V) : B :=
  d.dualEquiv.symm (orbitFunctional g v)

/-- Characterizing identity from the manuscript's proof of dual restriction. -/
theorem liftValue_spec (g : V →ₗ[A] A) (v : V) (a : B) :
    d.trace (a * d.liftValue g v) = g (a • v) := by
  rw [← d.dual_apply]
  exact DFunLike.congr_fun (d.dualEquiv.apply_symm_apply (orbitFunctional g v)) a

/-- The reconstructed functional is linear over the full, original ring. -/
def liftLinear (g : V →ₗ[A] A) : V →ₗ[B] B where
  toFun := d.liftValue g
  map_add' v w := by
    apply d.separating
    intro a
    rw [d.liftValue_spec, mul_add, map_add, d.liftValue_spec, d.liftValue_spec]
    simp [smul_add]
  map_smul' r v := by
    apply d.separating
    intro a
    change d.trace (a * d.liftValue g (r • v)) = d.trace (a * (r * d.liftValue g v))
    rw [d.liftValue_spec, ← mul_assoc, d.liftValue_spec, mul_smul]

/-- Restrict an original-ring functional and compose it with coefficient extraction. -/
def restrictDual : (V →ₗ[B] B) →ₗ[A] (V →ₗ[A] A) where
  toFun f := d.trace.comp (f.restrictScalars A)
  map_add' f g := by ext v; simp
  map_smul' r f := by ext v; simp

@[simp] theorem restrictDual_apply (f : V →ₗ[B] B) (v : V) :
    d.restrictDual f v = d.trace (f v) := rfl

theorem lift_restrictDual (f : V →ₗ[B] B) : d.liftLinear (d.restrictDual f) = f := by
  apply LinearMap.ext
  intro v
  apply d.separating
  intro a
  rw [show d.liftLinear (d.restrictDual f) v = d.liftValue (d.restrictDual f) v from rfl,
    d.liftValue_spec, restrictDual_apply, map_smul]
  rfl

theorem restrictDual_lift (g : V →ₗ[A] A) : d.restrictDual (d.liftLinear g) = g := by
  apply LinearMap.ext
  intro v
  change d.trace (d.liftValue g v) = g v
  simpa only [one_mul, one_smul] using d.liftValue_spec g v 1

/-- The natural dual restriction equivalence, valid for every original-ring module. -/
def dualRestrictEquiv : (V →ₗ[B] B) ≃ₗ[A] (V →ₗ[A] A) where
  __ := d.restrictDual
  invFun := d.liftLinear
  left_inv := d.lift_restrictDual
  right_inv := d.restrictDual_lift

@[simp] theorem dualRestrictEquiv_apply (f : V →ₗ[B] B) (v : V) :
    d.dualRestrictEquiv f v = d.trace (f v) := rfl

variable {W : Type*} [AddCommGroup W] [Module B W] [Module A W] [IsScalarTower A B W]

/-- Dual restriction commutes with precomposition by the actual original-ring map. -/
theorem naturality (f : V →ₗ[B] W) (g : W →ₗ[B] B) :
    d.dualRestrictEquiv (g.comp f) =
      (d.dualRestrictEquiv g).comp (f.restrictScalars A) := rfl

end Pairing

end Decoupling.FrobeniusDuality
