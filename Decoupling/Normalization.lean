import Decoupling.EvaluationLinear
import Mathlib.Algebra.Field.ZMod
import Mathlib.Algebra.Module.Projective
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Normalizing a free cover of trivial layers

This file proves the free-cover step of Lemma III.2. A surjection from `R^c`
to the actual trivial-translation module `𝔽₂^t` is evaluation followed by a
finite-field surjection. A constant change of coordinates is constructed from
a section and a basis of that finite-field kernel, then lifted to `R` together
with its inverse. The normalized kernel is `R^(c-t) × J^t`.
-/

namespace Decoupling.Normalization

open Module Matrix EvaluationLinear

noncomputable section

section Split

variable {K V W : Type*} [CommRing K]
  [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A specified section identifies a module with its kernel plus its quotient. -/
def kernelProdEquiv (q : V →ₗ[K] W) (s : W →ₗ[K] V)
    (hs : q.comp s = LinearMap.id) : V ≃ₗ[K] (LinearMap.ker q × W) where
  toFun v := (⟨v - s (q v), by
    change q (v - s (q v)) = 0
    have hs' (w : W) : q (s w) = w := DFunLike.congr_fun hs w
    simp [hs']⟩, q v)
  invFun z := z.1 + s z.2
  left_inv v := by simp
  right_inv z := by
    have hs' (w : W) : q (s w) = w := DFunLike.congr_fun hs w
    have hz : q z.1 = 0 := z.1.property
    apply Prod.ext
    · apply Subtype.ext
      simp [hs', hz]
    · simp [hs', hz]
  map_add' v w := by
    apply Prod.ext
    · apply Subtype.ext
      simp [map_add, sub_add_sub_comm]
    · exact map_add q v w
  map_smul' a v := by
    apply Prod.ext
    · apply Subtype.ext
      simp [map_smul, smul_sub]
    · exact map_smul q a v

@[simp] theorem kernelProdEquiv_snd (q : V →ₗ[K] W) (s : W →ₗ[K] V)
    (hs : q.comp s = LinearMap.id) (v : V) : (kernelProdEquiv q s hs v).2 = q v := rfl

end Split

section ConstantLift

variable {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]

/-- Lift a finite-field coordinate isomorphism by embedding every entry as a
constant Laurent polynomial. Its inverse is lifted in exactly the same way. -/
def constantExtension (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2)) :
    (ι → R) ≃ₗ[R] (κ → R) := by
  let E := LinearMap.toMatrix' e.toLinearMap
  let I := LinearMap.toMatrix' e.symm.toLinearMap
  have hIE : I * E = 1 := by
    have h : e.symm.toLinearMap.comp e.toLinearMap = LinearMap.id := by ext v; simp
    simpa only [I, E, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  have hEI : E * I = 1 := by
    have h : e.toLinearMap.comp e.symm.toLinearMap = LinearMap.id := by ext v; simp
    simpa only [I, E, LinearMap.toMatrix'_comp, LinearMap.toMatrix'_id] using
      congrArg LinearMap.toMatrix' h
  exact Matrix.toLin'OfInv (M := I.map constant) (M' := E.map constant)
    (by rw [← Matrix.map_mul, hIE]; exact Matrix.map_one _ (map_zero constant) (map_one constant))
    (by rw [← Matrix.map_mul, hEI]; exact Matrix.map_one _ (map_zero constant) (map_one constant))

@[simp] theorem constantExtension_apply
    (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2)) (v : ι → R) :
    constantExtension e v = (LinearMap.toMatrix' e.toLinearMap).map constant *ᵥ v := rfl

/-- Evaluation commutes with a constant change of coordinates. -/
theorem evaluation_constantExtension
    (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (κ → ZMod 2)) (v : ι → R) :
    augmentation ∘ constantExtension e v = e (augmentation ∘ v) := by
  rw [constantExtension_apply]
  have h : ((LinearMap.toMatrix' e.toLinearMap).map constant).map augmentation =
      LinearMap.toMatrix' e.toLinearMap := by ext i j; simp
  funext i
  rw [Function.comp_apply, augmentation.map_mulVec, h, LinearMap.toMatrix'_mulVec]
  rfl

end ConstantLift

section FiniteField

variable {c t : ℕ}

/-- Construct the constant-coordinate normal form of a surjective finite-field map. -/
theorem exists_field_normalization
    (q : (Fin c → ZMod 2) →ₗ[ZMod 2] (Fin t → ZMod 2))
    (hq : Function.Surjective q) :
    ∃ e : (Fin c → ZMod 2) ≃ₗ[ZMod 2] ((Fin (c - t) ⊕ Fin t) → ZMod 2),
      ∀ v j, e v (Sum.inr j) = q v j := by
  obtain ⟨s, hs⟩ := Module.projective_lifting_property q LinearMap.id hq
  let e₀ := kernelProdEquiv q s hs
  have hdim : Module.finrank (ZMod 2) (LinearMap.ker q) = c - t := by
    have he := e₀.finrank_eq
    simp only [Module.finrank_fin_fun, Module.finrank_prod] at he
    omega
  let b := Module.finBasisOfFinrankEq (ZMod 2) (LinearMap.ker q) hdim
  let e₁ := b.equivFun.prodCongr (LinearEquiv.refl (ZMod 2) (Fin t → ZMod 2))
  let e₂ := (LinearEquiv.sumArrowLequivProdArrow
    (Fin (c - t)) (Fin t) (ZMod 2) (ZMod 2)).symm
  refine ⟨(e₀.trans e₁).trans e₂, ?_⟩
  intro v j
  rfl

/-- A surjective augmentation map yields a genuinely surjective constant matrix. -/
theorem coefficientMatrix_surjective
    (ε : (Fin c → R) →ₗ[R] Trivial t) (hε : Function.Surjective ε) :
    Function.Surjective (coefficientMatrix ε).mulVecLin := by
  intro w
  obtain ⟨v, hv⟩ := hε w
  refine ⟨augmentation ∘ v, ?_⟩
  change evalMatrix (coefficientMatrix ε) v = w
  rw [evalMatrix_coefficientMatrix]
  exact hv

/-- The number of trivial quotient coordinates cannot exceed the rank of its free cover. -/
theorem quotient_rank_le (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) : t ≤ c := by
  have h := LinearMap.finrank_le_finrank_of_surjective (coefficientMatrix_surjective ε hε)
  simpa only [Module.finrank_fin_fun] using h

/-- Lemma III.2's constant basis change exists; it is not an input assumption.
The last `t` normalized coordinates are evaluated to obtain the given quotient. -/
theorem exists_constant_normalization
    (ε : (Fin c → R) →ₗ[R] Trivial t) (hε : Function.Surjective ε) :
    ∃ e : (Fin c → ZMod 2) ≃ₗ[ZMod 2] ((Fin (c - t) ⊕ Fin t) → ZMod 2),
      ∀ v j, ε v j = augmentation (constantExtension e v (Sum.inr j)) := by
  obtain ⟨e, he⟩ := exists_field_normalization (coefficientMatrix ε).mulVecLin
    (coefficientMatrix_surjective ε hε)
  refine ⟨e, ?_⟩
  intro v j
  have hεv : (coefficientMatrix ε).mulVecLin (augmentation ∘ v) = ε v := by
    change evalMatrix (coefficientMatrix ε) v = ε v
    rw [evalMatrix_coefficientMatrix]
  have hev := congrFun (evaluation_constantExtension e v) (Sum.inr j)
  exact (congrFun hεv j).symm.trans ((he _ j).symm.trans hev.symm)

/-- The finite-field coordinate change chosen from the proved existence theorem. -/
def normalizingFieldEquiv (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) :
    (Fin c → ZMod 2) ≃ₗ[ZMod 2] ((Fin (c - t) ⊕ Fin t) → ZMod 2) :=
  Classical.choose (exists_constant_normalization ε hε)

/-- The constant change of coordinates over the actual Laurent ring. -/
def normalizedCoordinates (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) :
    (Fin c → R) ≃ₗ[R] ((Fin (c - t) → R) × (Fin t → R)) :=
  (constantExtension (normalizingFieldEquiv ε hε)).trans
    (LinearEquiv.sumArrowLequivProdArrow (Fin (c - t)) (Fin t) R R)

/-- In the constructed coordinates, the quotient is `(a,b) ↦ b(1)`. -/
theorem normalized_formula (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) (v : Fin c → R) (j : Fin t) :
    ε v j = augmentation ((normalizedCoordinates ε hε v).2 j) :=
  Classical.choose_spec (exists_constant_normalization ε hε) v j

/-- In normalized coordinates the last `t` components lie in `J` precisely
when the vector belongs to the kernel of the given free cover. -/
theorem mem_kernel_iff_normalized (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) (v : Fin c → R) :
    v ∈ LinearMap.ker ε ↔ ∀ j, (normalizedCoordinates ε hε v).2 j ∈ J := by
  constructor
  · intro hv j
    rw [← ker_augmentation_eq_J]
    change augmentation ((normalizedCoordinates ε hε v).2 j) = 0
    rw [← normalized_formula ε hε]
    exact congrFun hv j
  · intro hv
    change ε v = 0
    funext j
    rw [normalized_formula ε hε]
    have hj := hv j
    rw [← ker_augmentation_eq_J] at hj
    exact hj

/-- Lemma III.2: an explicit `R`-linear equivalence from the actual free-cover
kernel to `R^(c-t) × (Fin t → J)`, using the constructed constant basis change.
The proof covers empty coordinate sets, including `c=t=0` and `t=0`.
-/
def kernelEquiv (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) :
    LinearMap.ker ε ≃ₗ[R] ((Fin (c - t) → R) × (Fin t → J)) := by
  let e := normalizedCoordinates ε hε
  have hinv (z : (Fin (c - t) → R) × (Fin t → J)) :
      e.symm (z.1, fun j => (z.2 j : R)) ∈ LinearMap.ker ε := by
    apply (mem_kernel_iff_normalized ε hε _).mpr
    intro j
    change (e (e.symm (z.1, fun j => (z.2 j : R)))).2 j ∈ J
    rw [e.apply_symm_apply]
    exact (z.2 j).property
  refine {
    toFun := fun v => ((e v).1, fun j =>
      ⟨(e v).2 j, (mem_kernel_iff_normalized ε hε v).mp v.property j⟩)
    invFun := fun z => ⟨e.symm (z.1, fun j => (z.2 j : R)), hinv z⟩
    left_inv := ?_
    right_inv := ?_
    map_add' := ?_
    map_smul' := ?_
  }
  · intro v w
    have h := e.map_add (v : Fin c → R) (w : Fin c → R)
    apply Prod.ext
    · exact congrArg (fun z : (Fin (c - t) → R) × (Fin t → R) => z.1) h
    · funext j
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd h) j
  · intro a v
    have h := e.map_smul a (v : Fin c → R)
    apply Prod.ext
    · exact congrArg (fun z : (Fin (c - t) → R) × (Fin t → R) => z.1) h
    · funext j
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd h) j
  · intro v
    apply Subtype.ext
    exact e.symm_apply_apply v
  · intro z
    have hz := e.apply_symm_apply (z.1, fun j => (z.2 j : R))
    apply Prod.ext
    · exact congrArg (fun z : (Fin (c - t) → R) × (Fin t → R) => z.1) hz
    · funext j
      apply Subtype.ext
      exact congrFun (congrArg Prod.snd hz) j

@[simp] theorem kernelEquiv_fst (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) (v : LinearMap.ker ε) :
    (kernelEquiv ε hε v).1 = (normalizedCoordinates ε hε v).1 := rfl

@[simp] theorem kernelEquiv_snd (ε : (Fin c → R) →ₗ[R] Trivial t)
    (hε : Function.Surjective ε) (v : LinearMap.ker ε) (j : Fin t) :
    ((kernelEquiv ε hε v).2 j : R) = (normalizedCoordinates ε hε v).2 j := rfl

end FiniteField

end

end Decoupling.Normalization
