import Mathlib.Algebra.Polynomial.Laurent
import Mathlib.LinearAlgebra.TensorProduct.Basis
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
import Mathlib.CategoryTheory.Abelian.Projective.Dimension

/-!
# The canonical sequence for a Laurent extension

The induced module is the actual tensor product `A[T;T⁻¹] ⊗[A] M`.
Finite Laurent coordinates are used to prove exactness, not to replace
the scalar extension with a differently defined algebra or module.
-/

namespace Decoupling.LaurentInduction

open scoped TensorProduct LaurentPolynomial
open CategoryTheory CategoryTheory.Abelian

noncomputable section

universe u

variable {A M : Type u} [CommRing A] [AddCommGroup M] [Module A M]

/-- The finite Laurent coefficient difference for an endomorphism `L`. -/
def coefficientDifference (L : M →ₗ[A] M) : (ℤ →₀ M) →ₗ[A] (ℤ →₀ M) :=
  Finsupp.lmapDomain M A (fun n : ℤ => n + 1) - Finsupp.mapRange.linearMap L

@[simp] theorem coefficientDifference_single (L : M →ₗ[A] M) (n : ℤ) (m : M) :
    coefficientDifference L (Finsupp.single n m) =
      Finsupp.single (n + 1) m - Finsupp.single n (L m) := by
  change Finsupp.mapDomain (fun n : ℤ => n + 1) (Finsupp.single n m) -
    Finsupp.mapRange L L.map_zero (Finsupp.single n m) = _
  simp

theorem coefficientDifference_apply (L : M →ₗ[A] M) (f : ℤ →₀ M) (n : ℤ) :
    coefficientDifference L f (n + 1) = f n - L (f (n + 1)) := by
  change Finsupp.mapDomain (fun n : ℤ => n + 1) f (n + 1) - L (f (n + 1)) = _
  rw [Finsupp.mapDomain_apply_of_injective (add_left_injective (1 : ℤ))]

/-- The leading nonzero Laurent coefficient cannot disappear under the
difference, regardless of any injectivity property of `L`. -/
theorem coefficientDifference_injective (L : M →ₗ[A] M) :
    Function.Injective (coefficientDifference L) := by
  classical
  apply (LinearMap.ker_eq_bot).mp
  apply eq_bot_iff.mpr
  intro f hf
  change f = 0
  by_contra hne
  have hs : f.support.Nonempty := Finsupp.support_nonempty_iff.mpr hne
  let n := f.support.max' hs
  have hn : n ∈ f.support := Finset.max'_mem _ _
  have hn1 : n + 1 ∉ f.support := by
    intro h
    have := Finset.le_max' f.support (n + 1) h
    change n + 1 ≤ n at this
    omega
  have hz : coefficientDifference L f = 0 := hf
  have hcoef := congrArg (fun g : ℤ →₀ M => g (n + 1)) hz
  rw [coefficientDifference_apply, Finsupp.notMem_support_iff.mp hn1,
    map_zero, sub_zero] at hcoef
  exact (Finsupp.mem_support_iff.mp hn) hcoef

/-- Actual induction of scalars along `A → A[T;T⁻¹]`. -/
abbrev Induced := A[T;T⁻¹] ⊗[A] M

/-- Coordinates in the actual Laurent monomial basis of the left factor. -/
def coordinates : Induced (A := A) (M := M) ≃ₗ[A] (ℤ →₀ M) :=
  TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis ℤ A)

@[simp] theorem coordinates_monomial (n : ℤ) (m : M) :
    coordinates ((LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m) =
      Finsupp.single n m := by
  change TensorProduct.equivFinsuppOfBasisLeft (AddMonoidAlgebra.basis ℤ A)
    ((AddMonoidAlgebra.basis ℤ A) n ⊗ₜ[A] m) = _
  rw [TensorProduct.equivFinsuppOfBasisLeft_apply_tmul, Module.Basis.repr_self]
  simp

variable [Module A[T;T⁻¹] M] [IsScalarTower A A[T;T⁻¹] M]

/-- `t ⊗ m - 1 ⊗ (t • m)`, extended Laurent-linearly. -/
def differential : Induced (A := A) (M := M) →ₗ[A[T;T⁻¹]] Induced (A := A) (M := M) :=
  LinearMap.lsmul A[T;T⁻¹] (Induced (A := A) (M := M)) (LaurentPolynomial.T 1) -
    (Algebra.lsmul A A M (LaurentPolynomial.T 1 : A[T;T⁻¹])).baseChange A[T;T⁻¹]

@[simp] theorem differential_tmul (b : A[T;T⁻¹]) (m : M) :
    differential (b ⊗ₜ[A] m) =
      (LaurentPolynomial.T 1 * b) ⊗ₜ[A] m -
        b ⊗ₜ[A] ((LaurentPolynomial.T 1 : A[T;T⁻¹]) • m) := by
  simp [differential, TensorProduct.smul_tmul']

/-- Multiplication of the two tensor factors using the given Laurent action. -/
def evaluation : Induced (A := A) (M := M) →ₗ[A[T;T⁻¹]] M :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun b => Algebra.lsmul A A M b
      map_add' := fun b c => by ext m; exact add_smul b c m
      map_smul' := fun b c => by ext m; exact mul_smul b c m }

@[simp] theorem evaluation_tmul (b : A[T;T⁻¹]) (m : M) :
    evaluation (b ⊗ₜ[A] m) = b • m := rfl

@[simp] theorem differential_monomial (n : ℤ) (m : M) :
    differential ((LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m) =
      (LaurentPolynomial.T (n + 1) : A[T;T⁻¹]) ⊗ₜ[A] m -
        (LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A]
          ((LaurentPolynomial.T 1 : A[T;T⁻¹]) • m) := by
  rw [differential_tmul, ← LaurentPolynomial.T_add, add_comm 1 n]

/-- The native tensor differential has precisely the finite Laurent
coefficient difference proved injective above. -/
theorem coordinates_differential (x : Induced (A := A) (M := M)) :
    coordinates (differential x) =
      coefficientDifference (Algebra.lsmul A A M (LaurentPolynomial.T 1 : A[T;T⁻¹]))
        (coordinates x) := by
  let e := coordinates (A := A) (M := M)
  obtain ⟨f, rfl⟩ := e.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp [e]
  | add f g hf hg => simpa only [map_add] using congrArg₂ (· + ·) hf hg
  | single n m =>
    have hsingle : e.symm (Finsupp.single n m) =
        (LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m :=
      e.injective (by simp [e])
    rw [hsingle, differential_monomial]
    simp

theorem differential_injective :
    Function.Injective (differential (A := A) (M := M)) := by
  intro x y h
  apply (coordinates (A := A) (M := M)).injective
  apply coefficientDifference_injective
    (Algebra.lsmul A A M (LaurentPolynomial.T 1 : A[T;T⁻¹]))
  simpa only [← coordinates_differential] using congrArg coordinates h

theorem evaluation_differential :
    (evaluation (A := A) (M := M)).comp differential = 0 := by
  apply TensorProduct.AlgebraTensorModule.ext
  intro b m
  simp [mul_smul]

theorem evaluation_surjective :
    Function.Surjective (evaluation (A := A) (M := M)) := by
  intro m
  exact ⟨1 ⊗ₜ[A] m, by simp⟩

private abbrev relationQuotient :=
  (LinearMap.range (differential (A := A) (M := M))).mkQ

private theorem relation_monomial (n : ℤ) (m : M) :
    relationQuotient ((LaurentPolynomial.T (n + 1) : A[T;T⁻¹]) ⊗ₜ[A] m) =
      relationQuotient ((LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A]
        ((LaurentPolynomial.T 1 : A[T;T⁻¹]) • m)) := by
  apply (Submodule.Quotient.eq _).mpr
  exact ⟨(LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m,
    differential_monomial n m⟩

/-- Finite telescoping in both integer directions, expressed in the
actual quotient by the tensor differential. -/
private theorem monomial_congr (n : ℤ) (m : M) :
    relationQuotient ((LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m) =
      relationQuotient ((1 : A[T;T⁻¹]) ⊗ₜ[A]
        ((LaurentPolynomial.T n : A[T;T⁻¹]) • m)) := by
  induction n using Int.induction_on generalizing m with
  | zero => simp
  | succ n ih =>
    rw [relation_monomial, ih]
    simp only [← mul_smul, ← LaurentPolynomial.T_add]
  | pred n ih =>
    have h := relation_monomial (A := A) (- (n : ℤ) - 1)
      ((LaurentPolynomial.T (-1) : A[T;T⁻¹]) • m)
    have hcancel : (LaurentPolynomial.T 1 : A[T;T⁻¹]) •
        ((LaurentPolynomial.T (-1) : A[T;T⁻¹]) • m) = m := by
      rw [← mul_smul, ← LaurentPolynomial.T_add]
      simp
    rw [hcancel] at h
    have hind : -(n : ℤ) - 1 + 1 = -(n : ℤ) := by omega
    rw [hind, ih] at h
    simpa only [← mul_smul, ← LaurentPolynomial.T_add, sub_eq_add_neg] using h.symm

/-- Every finite Laurent sum is congruent to its evaluation placed in
degree zero. The induction uses only finite support. -/
private theorem evaluation_congr (x : Induced (A := A) (M := M)) :
    relationQuotient x =
      relationQuotient ((1 : A[T;T⁻¹]) ⊗ₜ[A] evaluation x) := by
  let e := coordinates (A := A) (M := M)
  obtain ⟨f, rfl⟩ := e.symm.surjective x
  induction f using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add, TensorProduct.tmul_add] using congrArg₂ (· + ·) hf hg
  | single n m =>
    have hsingle : e.symm (Finsupp.single n m) =
        (LaurentPolynomial.T n : A[T;T⁻¹]) ⊗ₜ[A] m :=
      e.injective (by simp [e])
    rw [hsingle, evaluation_tmul]
    exact monomial_congr n m

/-- The kernel/image assertion is proved for the actual Laurent-linear
maps, without an exactness hypothesis. -/
theorem exact_differential_evaluation :
    LinearMap.ker (evaluation (A := A) (M := M)) = LinearMap.range differential := by
  apply le_antisymm
  · intro x hx
    have h := evaluation_congr x
    rw [show evaluation x = 0 from hx, TensorProduct.tmul_zero, map_zero] at h
    exact (Submodule.Quotient.mk_eq_zero _).mp h
  · rintro x ⟨y, rfl⟩
    exact LinearMap.congr_fun evaluation_differential y

/-- The canonical Laurent extension sequence consists of genuine induced
modules and the given module `M`. -/
def canonicalSequence : ShortComplex (ModuleCat A[T;T⁻¹]) :=
  ShortComplex.moduleCatMk
    (differential (A := A) (M := M)) evaluation evaluation_differential

theorem canonicalSequence_shortExact :
    (canonicalSequence (A := A) (M := M)).ShortExact where
  exact := by
    apply (canonicalSequence (A := A) (M := M)).moduleCat_exact_iff.mpr
    intro x hx
    have hx' : x ∈ LinearMap.ker (evaluation (A := A) (M := M)) := hx
    rw [exact_differential_evaluation] at hx'
    exact hx'
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (differential_injective (A := A) (M := M))
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (evaluation_surjective (A := A) (M := M))

/-- The exact sequence gives the native projective-dimension inequality
`pd M ≤ pd (A[T;T⁻¹] ⊗[A] M) + 1`. -/
theorem projectiveDimensionLE_succ (n : ℕ)
    [HasProjectiveDimensionLE (ModuleCat.of A[T;T⁻¹] (Induced (A := A) (M := M))) n] :
    HasProjectiveDimensionLE (ModuleCat.of A[T;T⁻¹] M) (n + 1) := by
  apply (canonicalSequence_shortExact (A := A) (M := M)).hasProjectiveDimensionLT_X₃
    (n + 1)
  · exact inferInstanceAs
      (HasProjectiveDimensionLE (ModuleCat.of A[T;T⁻¹] (Induced (A := A) (M := M))) n)
  · exact hasProjectiveDimensionLT_of_ge
      (ModuleCat.of A[T;T⁻¹] (Induced (A := A) (M := M))) (n + 1) (n + 1 + 1)
      (Nat.le_succ _)

/-- If the underlying `A`-module is projective, actual scalar induction
is projective over the Laurent ring. -/
instance induced_projective [Module.Projective A M] :
    Module.Projective A[T;T⁻¹] (Induced (A := A) (M := M)) := inferInstance

/-- In particular an `A`-projective Laurent module has Laurent projective
dimension at most one. -/
theorem projectiveDimensionLE_one [Module.Projective A M] :
    HasProjectiveDimensionLE (ModuleCat.of A[T;T⁻¹] M) 1 :=
  projectiveDimensionLE_succ (A := A) (M := M) 0

end

end Decoupling.LaurentInduction
