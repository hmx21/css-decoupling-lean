import Decoupling.RetainedRing
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.Algebra.Module.Projective

/-!
# The eight parity monomials form a basis over the retained ring

The retained ring is the actual subring `S = 𝔽₂[x±²,y±²,z±²]` from
`RetainedRing`. This file constructs its basis of `R` indexed by
`Fin 3 → Fin 2`, with basis vector `x^α y^β z^δ` at the parity vector
`(α,β,δ)`. Negative Laurent exponents are included through Euclidean division
on `ℤ`, not division on natural exponents.
-/

namespace Decoupling.CoarseBasis

open RetainedRing Module

noncomputable section

/-- The eight parity vectors, in coordinate order `(x,y,z)`. -/
abbrev Parity := Fin 3 → Fin 2

/-- A parity vector regarded as an integer translation exponent. -/
def parityExponent (p : Parity) : Translation := fun i => (p i : ℤ)

/-- Unique decomposition of an integer exponent vector into parity and half. -/
def exponentEquiv : Translation ≃ Parity × Translation where
  toFun a := (fun i => (Int.divModEquiv 2 (a i)).2,
    fun i => (Int.divModEquiv 2 (a i)).1)
  invFun p i := (Int.divModEquiv 2).symm (p.2 i, p.1 i)
  left_inv a := by
    funext i
    exact (Int.divModEquiv 2).symm_apply_apply (a i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.snd ((Int.divModEquiv 2).apply_symm_apply (p.2 i, p.1 i))
    · funext i
      exact congrArg Prod.fst ((Int.divModEquiv 2).apply_symm_apply (p.2 i, p.1 i))

theorem exponentEquiv_symm (p : Parity) (a : Translation) :
    exponentEquiv.symm (p, a) = doubleExponent a + parityExponent p := by
  funext i
  simp [exponentEquiv, Int.divModEquiv, doubleExponent, parityExponent, mul_comm]

/-- Group Laurent coefficients by parity, and rename even-exponent coefficients
as elements of the actual retained subring. Scalar compatibility will follow
from identifying its inverse with the canonical linear assembly map. -/
def decomposeAddEquiv : R ≃+ (Parity →₀ S) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr exponentEquiv).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv
          (AddMonoidAlgebra.coeffAddEquiv.symm.trans renameEquiv.toAddEquiv)

@[simp] theorem decompose_single (a : Translation) (t : ZMod 2) :
    decomposeAddEquiv (AddMonoidAlgebra.single a t) =
      Finsupp.single (exponentEquiv a).1
        (renameEquiv (AddMonoidAlgebra.single (exponentEquiv a).2 t)) := by
  simp [decomposeAddEquiv, Finsupp.domCongr]

/-- Canonical `S`-linear assembly from the parity monomials. -/
def assemble : (Parity →₀ S) →ₗ[S] R :=
  Finsupp.linearCombination S (fun p => monomial (parityExponent p))

@[simp] theorem assemble_single (p : Parity) (s : S) :
    assemble (Finsupp.single p s) = s • monomial (parityExponent p) := by
  simp [assemble]

theorem renamed_single_smul (a : Translation) (t : ZMod 2) (p : Parity) :
    renameEquiv (AddMonoidAlgebra.single a t) • monomial (parityExponent p) =
      AddMonoidAlgebra.single (doubleExponent a + parityExponent p) t := by
  rw [Algebra.smul_def]
  change embed (AddMonoidAlgebra.single a t) * monomial (parityExponent p) = _
  simp [embed, monomial]

/-- Reassembling the parity decomposition recovers every Laurent polynomial. -/
theorem assemble_decompose (r : R) : assemble (decomposeAddEquiv r) = r := by
  have h : assemble.toAddMonoidHom.comp decomposeAddEquiv.toAddMonoidHom =
      AddMonoidHom.id R := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a t
    change assemble (decomposeAddEquiv (AddMonoidAlgebra.single a t)) =
      AddMonoidAlgebra.single a t
    rw [decompose_single, assemble_single, renamed_single_smul, ← exponentEquiv_symm]
    rw [exponentEquiv.symm_apply_apply]
  exact DFunLike.congr_fun h r

theorem assemble_eq_inverse : (assemble : (Parity →₀ S) → R) = decomposeAddEquiv.symm := by
  funext v
  simpa only [decomposeAddEquiv.apply_symm_apply] using
    assemble_decompose (decomposeAddEquiv.symm v)

theorem assemble_bijective : Function.Bijective assemble := by
  rw [assemble_eq_inverse]
  exact decomposeAddEquiv.symm.bijective

/-- The actual `S`-linear equivalence between eight retained coefficients and `R`. -/
def assemblyEquiv : (Parity →₀ S) ≃ₗ[S] R :=
  LinearEquiv.ofBijective assemble assemble_bijective

/-- Equation (28): `R` has the eight parity monomials as an `S`-basis. -/
def parityBasis : Basis Parity S R := Basis.ofRepr assemblyEquiv.symm

/-- The basis coordinates are precisely the explicit coefficient grouping. -/
theorem parityBasis_repr (r : R) : parityBasis.repr r = decomposeAddEquiv r := by
  apply assemblyEquiv.injective
  change assemblyEquiv (assemblyEquiv.symm r) = assemble (decomposeAddEquiv r)
  rw [assemblyEquiv.apply_symm_apply, assemble_decompose]

@[simp] theorem parityBasis_apply (p : Parity) :
    parityBasis p = monomial (parityExponent p) := by
  change assemble (Finsupp.single p 1) = monomial (parityExponent p)
  rw [assemble_single, one_smul]

/-- The displayed monomial form `x^α y^β z^δ` in equation (28). -/
theorem parityBasis_xyz (p : Parity) :
    parityBasis p = x ^ (p 0).val * y ^ (p 1).val * z ^ (p 2).val := by
  rw [parityBasis_apply]
  simp only [x, y, z, monomial, AddMonoidAlgebra.single_pow, one_pow,
    AddMonoidAlgebra.single_mul_single, one_mul]
  congr 1
  funext i
  fin_cases i <;> simp [parityExponent, translationBasis]

/-- This is an actual module-freeness instance over the retained subring. -/
instance retainedModuleFree : Module.Free S R := Module.Free.of_basis parityBasis

instance retainedModuleFinite : Module.Finite S R := Module.Finite.of_basis parityBasis

theorem parity_card : Fintype.card Parity = 8 := by decide

/-- The retained-ring rank of `R` is eight. -/
theorem finrank_retained : Module.finrank S R = 8 := by
  rw [Module.finrank_eq_card_basis parityBasis, parity_card]

/-- A free `R`-module stays free after restricting scalars to the retained ring. -/
theorem free_restrict_of_free (M : Type*) [AddCommMonoid M]
    [Module S M] [Module R M] [IsScalarTower S R M] [Module.Free R M] :
    Module.Free S M := Module.Free.trans (R := S) (S := R) (M := M)

/-- In particular, every restricted free resolution term is projective over `S`. -/
theorem projective_restrict_of_free (M : Type*) [AddCommMonoid M]
    [Module S M] [Module R M] [IsScalarTower S R M] [Module.Free R M] :
    Module.Projective S M := by
  let : Module.Free S M := free_restrict_of_free M
  infer_instance

end

end Decoupling.CoarseBasis
