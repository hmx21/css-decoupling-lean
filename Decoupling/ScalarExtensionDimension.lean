import Decoupling.LaurentInduction
import Mathlib.RingTheory.Flat.Basic
import Mathlib.CategoryTheory.Preadditive.Projective.Preserves
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Projective dimension under flat scalar extension

All modules, tensor products, projectivity and projective dimensions in this
file are the native mathlib constructions. The proof tensors a projective
cover and proceeds by the native short-exact-sequence dimension shift.
-/

namespace Decoupling.ScalarExtensionDimension

open scoped TensorProduct
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits

noncomputable section

universe u

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- A short complex tensored with the actual scalar extension `B ⊗[A] -`. -/
def tensorSequence (S : ShortComplex (ModuleCat.{u} A)) : ShortComplex (ModuleCat.{u} B) :=
  ShortComplex.moduleCatMk (S.f.hom.baseChange B) (S.g.hom.baseChange B) (by
    apply TensorProduct.AlgebraTensorModule.ext
    intro b m
    change b ⊗ₜ[A] S.g (S.f m) = 0
    rw [S.moduleCat_zero_apply, TensorProduct.tmul_zero])

theorem tensorSequence_shortExact [Module.Flat A B]
    (S : ShortComplex (ModuleCat.{u} A)) (hS : S.ShortExact) :
    (tensorSequence (B := B) S).ShortExact where
  exact := by
    apply (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact
      (tensorSequence (B := B) S)).mpr
    exact Module.Flat.lTensor_exact B
      ((ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).mp hS.exact)
  mono_f := (ModuleCat.mono_iff_injective _).mpr
    (Module.Flat.lTensor_preserves_injective_linearMap S.f.hom hS.moduleCat_injective_f)
  epi_g := (ModuleCat.epi_iff_surjective _).mpr
    (LinearMap.baseChange_surjective B hS.moduleCat_surjective_g)

/-- Flat scalar extension cannot increase projective dimension. -/
theorem tensor_projectiveDimensionLE [Module.Flat A B] (n : ℕ) (M : ModuleCat.{u} A)
    [HasProjectiveDimensionLE M n] :
    HasProjectiveDimensionLE (ModuleCat.of B (B ⊗[A] M)) n := by
  induction n generalizing M with
  | zero =>
    have : Projective M := (projective_iff_hasProjectiveDimensionLE_zero M).mpr ‹_›
    have : Module.Projective A M := inferInstance
    exact inferInstance
  | succ n ih =>
    obtain ⟨⟨P, f⟩⟩ := ModuleCat.enoughProjectives.1 M
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
    let T := tensorSequence (B := B) S
    have hT : T.ShortExact := tensorSequence_shortExact S hS
    have hP : Projective T.X₂ := by
      have : Module.Projective A P := inferInstance
      exact inferInstanceAs (Projective (ModuleCat.of B (B ⊗[A] P)))
    have : HasProjectiveDimensionLE (kernel f) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    exact (hT.hasProjectiveDimensionLT_X₃_iff n hP).mpr (ih (kernel f))

section Functor

variable {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [EnoughProjectives C] (F : C ⥤ D) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesProjectiveObjects]

/-- An exact additive functor preserving projectives preserves every
finite native projective-dimension bound. This also supplies transport
along a ring equivalence. -/
theorem functor_projectiveDimensionLE (n : ℕ) (X : C) [HasProjectiveDimensionLE X n] :
    HasProjectiveDimensionLE (F.obj X) n := by
  induction n generalizing X with
  | zero =>
    have : Projective X := (projective_iff_hasProjectiveDimensionLE_zero X).mpr ‹_›
    exact inferInstance
  | succ n ih =>
    let f := Projective.π X
    let S := ShortComplex.mk (kernel.ι f) f (kernel.condition f)
    have hS : S.ShortExact := { exact := ShortComplex.exact_kernel f }
    have hT : (S.map F).ShortExact := hS.map_of_exact F
    have : HasProjectiveDimensionLE (kernel f) n :=
      (hS.hasProjectiveDimensionLT_X₃_iff n inferInstance).mp inferInstance
    exact (hT.hasProjectiveDimensionLT_X₃_iff n (F.projective_obj _)).mpr (ih (kernel f))

end Functor

end

end Decoupling.ScalarExtensionDimension
