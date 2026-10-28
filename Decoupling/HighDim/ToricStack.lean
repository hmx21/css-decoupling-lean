import Decoupling.HighDim.ToricWindowCoordinates
import Decoupling.HighDim.FiniteResolutionProfile
import Decoupling.HighDim.CochainCokernelDerived
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import Mathlib.Algebra.Homology.HomologicalComplexLimits

/-!
# Finite stacks of actual toric complexes

The index type enumerates individual copies, so multiplicities are
represented by repeated form indices. Empty stacks are included. The
native derived biproduct is preserved by localization; no split-profile
or model certificate is hidden in a definition.
-/

namespace Decoupling.HighDim.Toric

open CategoryTheory CategoryTheory.Limits HomologicalComplex

noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
variable (K : Type) [Field K] (D : ℕ) {ι : Type} [Fintype ι] (forms : ι → ℕ)

local instance : HasFiniteBiproducts (CochainComplex (ModuleCat (Laurent K D)) ℤ) :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- A finite biproduct of the actual `(forms i + 1)`-form complexes. -/
def stackModel : CochainComplex (ModuleCat (Laurent K D)) ℤ :=
  ⨁ fun i => model K D (forms i + 1)

def stackTermIso (n : ℤ) : (stackModel K D forms).X n ≅
    ModuleCat.of (Laurent K D) (∀ i, (model K D (forms i + 1)).X n) :=
  (eval (ModuleCat (Laurent K D)) (ComplexShape.up ℤ) n).mapBiproduct
    (fun i => model K D (forms i + 1)) ≪≫
      ModuleCat.biproductIsoPi (fun i => (model K D (forms i + 1)).X n)

theorem stackTermIso_hom_proj (n : ℤ) (i : ι) :
    (stackTermIso K D forms n).hom ≫ ModuleCat.ofHom (LinearMap.proj i) =
      (biproduct.π (fun i => model K D (forms i + 1)) i).f n := by
  have h : (ModuleCat.biproductIsoPi (fun i => (model K D (forms i + 1)).X n)).hom ≫
      ModuleCat.ofHom (LinearMap.proj i) =
      biproduct.π (fun i => (model K D (forms i + 1)).X n) i := by
    rw [← cancel_epi (ModuleCat.biproductIsoPi (fun i => (model K D (forms i + 1)).X n)).inv]
    simp
  simp only [stackTermIso, Iso.trans_hom, Category.assoc, h,
    Functor.mapBiproduct_hom]
  exact biproduct.lift_π _ i

theorem stackTermIso_apply (n : ℤ) (x : (stackModel K D forms).X n) (i : ι) :
    (stackTermIso K D forms n).hom x i =
      (biproduct.π (fun i => model K D (forms i + 1)) i).f n x :=
  congrArg (fun f => f x) (stackTermIso_hom_proj K D forms n i)

theorem stackTermIso_d (a b : ℤ) (x : (stackModel K D forms).X a) (i : ι) :
    (stackTermIso K D forms b).hom ((stackModel K D forms).d a b x) i =
      (model K D (forms i + 1)).d a b ((stackTermIso K D forms a).hom x i) := by
  rw [stackTermIso_apply, stackTermIso_apply]
  exact congrArg (fun f => f x) ((biproduct.π (fun i => model K D (forms i + 1)) i).comm a b).symm

instance stackModel_finite (n : ℤ) :
    Module.Finite (Laurent K D) ((stackModel K D forms).X n) :=
  Module.Finite.equiv (stackTermIso K D forms n).symm.toLinearEquiv

instance stackModel_free (n : ℤ) :
    Module.Free (Laurent K D) ((stackModel K D forms).X n) :=
  Module.Free.of_equiv (stackTermIso K D forms n).symm.toLinearEquiv

instance stackModel_projective (n : ℤ) : Projective ((stackModel K D forms).X n) :=
  inferInstance

/-- A conservative explicit upper bound, valid also for an empty stack. -/
def stackBound : ℕ := ∑ i, (forms i + 1)

instance stackModel_boundedAbove : (stackModel K D forms).IsStrictlyLE (stackBound forms) := by
  rw [CochainComplex.isStrictlyLE_iff]
  intro n hn
  have hi (i : ι) : IsZero ((model K D (forms i + 1)).X n) := by
    have h : forms i + 1 ≤ stackBound forms := by
      change forms i + 1 ≤ ∑ j, (forms j + 1)
      exact Finset.single_le_sum (f := fun j : ι => forms j + 1)
        (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    exact (model K D (forms i + 1)).isZero_of_isStrictlyLE (forms i + 1) n (by omega)
  let : ∀ i : ι, Subsingleton ((model K D (forms i + 1)).X n) :=
    fun i => ModuleCat.subsingleton_of_isZero (hi i)
  exact (ModuleCat.isZero_of_subsingleton _).of_iso (stackTermIso K D forms n)

/-- The actual derived direct sum of the individual coefficient layers. -/
def splitTarget : DerivedCategory (ModuleCat (Laurent K D)) :=
  ⨁ fun i => (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) (forms i + 1)).obj
    (Koszul.coefficientModule K D)

def stackDerivedIso : DerivedCategory.Q.obj (stackModel K D forms) ≅ splitTarget K D forms :=
  DerivedCategory.Q.mapBiproduct (fun i => model K D (forms i + 1)) ≪≫
    biproduct.mapIso (fun i => derivedIso K D (forms i + 1))

theorem stackModel_exact_zero : (stackModel K D forms).ExactAt 0 := by
  rw [(stackModel K D forms).exactAt_iff' (-1) 0 1 (by simp) (by simp)]
  apply (ShortComplex.moduleCat_exact_iff _).mpr
  intro x hx
  have h (i : ι) : ∃ y : (model K D (forms i + 1)).X (-1),
      (model K D (forms i + 1)).d (-1) 0 y = (stackTermIso K D forms 0).hom x i := by
    have he := (model K D (forms i + 1)).exactAt_of_isGE (forms i + 1) 0 (by omega)
    rw [(model K D (forms i + 1)).exactAt_iff' (-1) 0 1 (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff] at he
    apply he
    have hh := congrArg (fun y => (stackTermIso K D forms 1).hom y i) hx
    change (stackTermIso K D forms 1).hom ((stackModel K D forms).d 0 1 x) i =
      (stackTermIso K D forms 1).hom 0 i at hh
    simp only [map_zero] at hh
    rwa [stackTermIso_d] at hh
  choose y hy using h
  refine ⟨(stackTermIso K D forms (-1)).toLinearEquiv.symm y, ?_⟩
  apply (stackTermIso K D forms 0).toLinearEquiv.injective
  funext i
  change (stackTermIso K D forms 0).hom
    ((stackModel K D forms).d (-1) 0 ((stackTermIso K D forms (-1)).toLinearEquiv.symm y)) i = _
  rw [stackTermIso_d]
  change (model K D (forms i + 1)).d (-1) 0
    ((stackTermIso K D forms (-1)).toLinearEquiv
      ((stackTermIso K D forms (-1)).toLinearEquiv.symm y) i) = _
  rw [LinearEquiv.apply_symm_apply]
  exact hy i

/-- A genuine split profile provides the stable check-cokernel comparison
with the actual toric stack, with every model hypothesis discharged. -/
theorem stableCokernel_of_split {q s r : ℕ} (c : CSS.Checks K D q s r)
    (hc : c.Topological) (e : Profile.S_X c ≅ splitTarget K D forms) :
    ∃ a b : ℕ, Nonempty
      ((CochainCokernel.CheckCokernel (stackModel K D forms) × (Fin b → Laurent K D))
        ≃ₗ[Laurent K D]
      (CochainCokernel.CheckCokernel (FiniteResolution.cssComplex c hc) ×
        (Fin a → Laurent K D))) :=
  CochainCokernel.exists_stableEquiv_of_derivedIso (D + 2) (stackBound forms)
    (FiniteResolution.cssComplex_profileIso c hc ≪≫ e ≪≫ (stackDerivedIso K D forms).symm)

end
end Decoupling.HighDim.Toric
