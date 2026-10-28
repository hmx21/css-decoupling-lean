import Decoupling.CoarseBasis
import Decoupling.FrobeniusDuality
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Restriction to an arbitrary finite-index translation sublattice

The retained ring is a literal subring of the manuscript's Laurent ring,
supported on `Λ ≤ ℤ³`. Cosets, including negative exponents, give an actual
free basis. No rectangular shape of the sublattice is assumed.
-/

namespace Decoupling.GeneralLatticeRestriction

open Module Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

variable (Λ : AddSubgroup Translation)

abbrev LatticeAlgebra := AddMonoidAlgebra (ZMod 2) Λ

def embed : LatticeAlgebra Λ →+* R :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) Λ.subtype

def retained : Subring R := (embed Λ).range
abbrev S := retained Λ

instance : Algebra (S Λ) R := (retained Λ).subtype.toAlgebra

theorem embed_injective : Function.Injective (embed Λ) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- The retained subring is the actual image of the subgroup algebra. -/
def latticeEquiv : LatticeAlgebra Λ ≃+* S Λ :=
  RingEquiv.ofBijective (embed Λ).rangeRestrict
    ⟨fun _ _ h => embed_injective Λ (congrArg Subtype.val h),
      (embed Λ).rangeRestrict_surjective⟩

@[simp] theorem embed_single (a : Λ) (c : ZMod 2) :
    embed Λ (AddMonoidAlgebra.single a c) = AddMonoidAlgebra.single (a : Translation) c := by
  simp [embed]

@[simp] theorem embed_coeff (r : LatticeAlgebra Λ) (a : Λ) :
    (embed Λ r).coeff (a : Translation) = r.coeff a :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective r.coeff a

/-- Membership in the actual retained subring is exactly support on `Λ`. -/
theorem mem_retained_iff (r : R) : r ∈ retained Λ ↔ ∀ a ∉ Λ, r.coeff a = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ a ha
    exact Finsupp.mapDomain_of_notMem_range p.coeff a (by
      rintro ⟨b, rfl⟩
      exact ha b.property)
  · intro h
    have h' : ∀ a ∉ Set.range (Subtype.val : Λ → Translation), r.coeff a = 0 := by
      intro a ha
      exact h a (by intro hm; exact ha ⟨⟨a, hm⟩, rfl⟩)
    obtain ⟨p, hp⟩ := (Finsupp.mem_range_mapDomain_iff
      (Subtype.val : Λ → Translation) Subtype.val_injective r.coeff).mpr h'
    refine ⟨AddMonoidAlgebra.ofCoeff p, ?_⟩
    exact AddMonoidAlgebra.coeff_injective hp

theorem latticeEquiv_symm_coeff (s : S Λ) (a : Λ) :
    ((latticeEquiv Λ).symm s).coeff a = (s : R).coeff (a : Translation) := by
  have hs : embed Λ ((latticeEquiv Λ).symm s) = (s : R) :=
    congrArg Subtype.val ((latticeEquiv Λ).apply_symm_apply s)
  rw [← hs, embed_coeff]

abbrev Coset := Translation ⧸ Λ

/-- Representatives are normalized so that the identity coset has exponent zero. -/
def representative (q : Coset Λ) : Translation := by
  classical
  exact if q = 0 then 0 else q.out

@[simp] theorem representative_zero : representative Λ 0 = 0 := by simp [representative]

@[simp] theorem representative_class (q : Coset Λ) :
    (QuotientAddGroup.mk' Λ) (representative Λ q) = q := by
  by_cases hq : q = 0
  · subst q; simp [representative]
  · simp only [representative, hq, ↓reduceIte]
    exact Quotient.out_eq' q

theorem exponent_difference_mem (a : Translation) :
    a - representative Λ ((QuotientAddGroup.mk' Λ) a) ∈ Λ := by
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' Λ) (a - representative Λ ((QuotientAddGroup.mk' Λ) a)) = 0
  rw [map_sub, representative_class, sub_self]

/-- Every exponent is uniquely a chosen coset representative plus a retained exponent. -/
def exponentEquiv : Translation ≃ Coset Λ × Λ where
  toFun a := ((QuotientAddGroup.mk' Λ) a,
    ⟨a - representative Λ ((QuotientAddGroup.mk' Λ) a), exponent_difference_mem Λ a⟩)
  invFun p := (p.2 : Translation) + representative Λ p.1
  left_inv a := sub_add_cancel _ _
  right_inv p := by
    have hz : (QuotientAddGroup.mk' Λ) (p.2 : Translation) = 0 :=
      (QuotientAddGroup.eq_zero_iff (p.2 : Translation)).mpr p.2.property
    have hp : (QuotientAddGroup.mk' Λ) ((p.2 : Translation) + representative Λ p.1) = p.1 := by
      rw [map_add, representative_class, hz, zero_add]
    apply Prod.ext
    · exact hp
    · apply Subtype.ext
      change (p.2 : Translation) + representative Λ p.1 -
        representative Λ ((QuotientAddGroup.mk' Λ) ((p.2 : Translation) + representative Λ p.1)) = p.2
      rw [hp, add_sub_cancel_right]

@[simp] theorem exponentEquiv_symm (q : Coset Λ) (a : Λ) :
    (exponentEquiv Λ).symm (q, a) = (a : Translation) + representative Λ q := rfl

def decomposeAddEquiv : R ≃+ (Coset Λ →₀ S Λ) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr (exponentEquiv Λ)).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv
          (AddMonoidAlgebra.coeffAddEquiv.symm.trans (latticeEquiv Λ).toAddEquiv)

@[simp] theorem decompose_single (a : Translation) (c : ZMod 2) :
    decomposeAddEquiv Λ (AddMonoidAlgebra.single a c) =
      Finsupp.single (exponentEquiv Λ a).1
        (latticeEquiv Λ (AddMonoidAlgebra.single (exponentEquiv Λ a).2 c)) := by
  simp [decomposeAddEquiv, Finsupp.domCongr]

def assemble : (Coset Λ →₀ S Λ) →ₗ[S Λ] R :=
  Finsupp.linearCombination (S Λ) (fun q => monomial (representative Λ q))

@[simp] theorem assemble_single (q : Coset Λ) (s : S Λ) :
    assemble Λ (Finsupp.single q s) = s • monomial (representative Λ q) := by
  simp [assemble]

theorem lattice_single_smul (a : Λ) (c : ZMod 2) (q : Coset Λ) :
    latticeEquiv Λ (AddMonoidAlgebra.single a c) • monomial (representative Λ q) =
      AddMonoidAlgebra.single ((a : Translation) + representative Λ q) c := by
  rw [Algebra.smul_def]
  change embed Λ (AddMonoidAlgebra.single a c) * monomial (representative Λ q) = _
  simp [monomial]

theorem assemble_decompose (r : R) : assemble Λ (decomposeAddEquiv Λ r) = r := by
  have h : (assemble Λ).toAddMonoidHom.comp (decomposeAddEquiv Λ).toAddMonoidHom =
      AddMonoidHom.id R := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a c
    change assemble Λ (decomposeAddEquiv Λ (AddMonoidAlgebra.single a c)) = _
    rw [decompose_single, assemble_single, lattice_single_smul, ← exponentEquiv_symm]
    rw [(exponentEquiv Λ).symm_apply_apply]
    rfl
  exact DFunLike.congr_fun h r

theorem assemble_eq_inverse :
    (assemble Λ : (Coset Λ →₀ S Λ) → R) = (decomposeAddEquiv Λ).symm := by
  funext v
  simpa only [(decomposeAddEquiv Λ).apply_symm_apply] using
    assemble_decompose Λ ((decomposeAddEquiv Λ).symm v)

def assemblyEquiv : (Coset Λ →₀ S Λ) ≃ₗ[S Λ] R :=
  LinearEquiv.ofBijective (assemble Λ) (by
    rw [assemble_eq_inverse]
    exact (decomposeAddEquiv Λ).symm.bijective)

/-- The actual Laurent coset-monomial basis, valid even before finite index. -/
def cosetBasis : Basis (Coset Λ) (S Λ) R := Basis.ofRepr (assemblyEquiv Λ).symm

theorem cosetBasis_repr (r : R) : (cosetBasis Λ).repr r = decomposeAddEquiv Λ r := by
  apply (assemblyEquiv Λ).injective
  change assemblyEquiv Λ ((assemblyEquiv Λ).symm r) = assemble Λ (decomposeAddEquiv Λ r)
  rw [(assemblyEquiv Λ).apply_symm_apply, assemble_decompose]

@[simp] theorem cosetBasis_apply (q : Coset Λ) :
    cosetBasis Λ q = monomial (representative Λ q) := by
  change assemble Λ (Finsupp.single q 1) = monomial (representative Λ q)
  rw [assemble_single, one_smul]

instance retainedModuleFree : Module.Free (S Λ) R := Module.Free.of_basis (cosetBasis Λ)

/-- Every genuinely free original-ring module remains free under scalar restriction. -/
theorem free_restrict_of_free (M : Type*) [AddCommMonoid M]
    [Module (S Λ) M] [Module R M] [IsScalarTower (S Λ) R M] [Module.Free R M] :
    Module.Free (S Λ) M := Module.Free.trans (R := S Λ) (S := R) (M := M)

/-- Restriction preserves arbitrary native projectives by restricting their
actual splitting off a free cover. -/
theorem projective_restrict (M : Type*) [AddCommGroup M]
    [Module (S Λ) M] [Module R M] [IsScalarTower (S Λ) R M] [Module.Projective R M] :
    Module.Projective (S Λ) M := by
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := R) (P := M)).mp inferInstance
  let : Module.Free (S Λ) (M →₀ R) := free_restrict_of_free Λ (M →₀ R)
  apply Module.Projective.of_split (i.restrictScalars (S Λ))
    ((Finsupp.linearCombination R id).restrictScalars (S Λ))
  apply LinearMap.ext
  intro m
  exact DFunLike.congr_fun hi m

/-- Keep precisely the coefficients supported on the retained lattice. -/
def τ : R →ₗ[S Λ] S Λ := (cosetBasis Λ).coord 0

theorem τ_coeff (r : R) (a : Λ) :
    ((latticeEquiv Λ).symm (τ Λ r)).coeff a = r.coeff (a : Translation) := by
  simp [τ, Basis.coord_apply, cosetBasis_repr, decomposeAddEquiv,
    Finsupp.domCongr, exponentEquiv_symm]

theorem τ_coe_coeff (r : R) (a : Translation) :
    (τ Λ r : R).coeff a = if a ∈ Λ then r.coeff a else 0 := by
  classical
  by_cases ha : a ∈ Λ
  · simp only [ha, ↓reduceIte]
    rw [← latticeEquiv_symm_coeff Λ (τ Λ r) ⟨a, ha⟩, τ_coeff]
  · simp only [ha, ↓reduceIte]
    exact (mem_retained_iff Λ _).mp (τ Λ r).property a ha

@[simp] theorem τ_one : τ Λ 1 = 1 := by
  have hzero : cosetBasis Λ (0 : Coset Λ) = 1 := by simp
  rw [← hzero]
  simp only [τ, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

@[simp] theorem τ_algebraMap (s : S Λ) : τ Λ (algebraMap (S Λ) R s) = s := by
  change τ Λ (s : R) = s
  have h : τ Λ ((s : R) * 1) = s * τ Λ 1 := (τ Λ).map_smul s (1 : R)
  simpa only [mul_one, τ_one] using h

theorem bar_mem_retained {r : R} (hr : r ∈ retained Λ) : bar r ∈ retained Λ := by
  apply (mem_retained_iff Λ _).mpr
  intro a ha
  rw [bar_coeff]
  exact (mem_retained_iff Λ _).mp hr (-a) (fun h => ha (by simpa using Λ.neg_mem h))

/-- Retained conjugation is literally the restriction of Laurent conjugation. -/
def barS : S Λ ≃+* S Λ where
  toFun s := ⟨bar s, bar_mem_retained Λ s.property⟩
  invFun s := ⟨bar s, bar_mem_retained Λ s.property⟩
  left_inv s := Subtype.ext (bar_bar s)
  right_inv s := Subtype.ext (bar_bar s)
  map_mul' s t := Subtype.ext (bar_mul s t)
  map_add' s t := Subtype.ext (bar_add s t)

@[simp] theorem coe_barS (s : S Λ) : (barS Λ s : R) = bar (s : R) := rfl

@[simp] theorem barS_barS (s : S Λ) : barS Λ (barS Λ s) = s :=
  Subtype.ext (bar_bar s)

theorem τ_bar (r : R) : τ Λ (bar r) = barS Λ (τ Λ r) := by
  apply Subtype.ext
  ext a
  simp only [τ_coe_coeff, coe_barS, bar_coeff, AddSubgroup.neg_mem_iff]

section FiniteIndex

variable [Λ.FiniteIndex]

instance cosetFintype : Fintype (Coset Λ) := Fintype.ofFinite _

instance retainedModuleFinite : Module.Finite (S Λ) R := Module.Finite.of_basis (cosetBasis Λ)

theorem finrank_retained : Module.finrank (S Λ) R = Λ.index := by
  rw [Module.finrank_eq_card_basis (cosetBasis Λ)]
  exact Nat.card_eq_fintype_card.symm

omit [Λ.FiniteIndex] in
/-- Monomial representatives and their inverses are dual for coefficient extraction. -/
theorem τ_inverse_basis (p q : Coset Λ) :
    τ Λ (bar (cosetBasis Λ p) * cosetBasis Λ q) = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp
  · simp only [hpq, ↓reduceIte]
    rw [cosetBasis_apply, cosetBasis_apply, bar_monomial, monomial_mul]
    apply (latticeEquiv Λ).symm.injective
    ext a
    rw [τ_coeff]
    have hne : -representative Λ p + representative Λ q ≠ (a : Translation) := by
      intro ha
      have he : (exponentEquiv Λ).symm (p, a) = (exponentEquiv Λ).symm (q, 0) := by
        simp only [exponentEquiv_symm, ZeroMemClass.coe_zero, zero_add]
        rw [← ha]
        abel
      exact hpq (congrArg Prod.fst ((exponentEquiv Λ).symm.injective he))
    simp [monomial, hne]

omit [Λ.FiniteIndex] in
theorem τ_basis_inverse (p q : Coset Λ) :
    τ Λ (cosetBasis Λ p * bar (cosetBasis Λ q)) = if p = q then 1 else 0 := by
  simpa only [mul_comm, eq_comm] using τ_inverse_basis Λ q p

omit [Λ.FiniteIndex] in
theorem τ_inverse_mul_eq_coord (p : Coset Λ) (r : R) :
    τ Λ (bar (cosetBasis Λ p) * r) = (cosetBasis Λ).coord p r := by
  have h : (τ Λ).comp (LinearMap.mul (S Λ) R (bar (cosetBasis Λ p))) =
      (cosetBasis Λ).coord p := by
    apply (cosetBasis Λ).ext
    intro q
    change τ Λ (bar (cosetBasis Λ p) * cosetBasis Λ q) = (cosetBasis Λ).coord p _
    rw [τ_inverse_basis]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun h r

def pairingMap : R →ₗ[S Λ] (R →ₗ[S Λ] S Λ) where
  toFun r := {
    toFun a := τ Λ (a * r)
    map_add' a b := by simp [add_mul]
    map_smul' s a := by simp }
  map_add' r s := by
    apply LinearMap.ext
    intro a
    change τ Λ (a * (r + s)) = τ Λ (a * r) + τ Λ (a * s)
    simp [mul_add]
  map_smul' s r := by
    apply LinearMap.ext
    intro a
    change τ Λ (a * (s • r)) = s • τ Λ (a * r)
    simp

omit [Λ.FiniteIndex] in
@[simp] theorem pairingMap_apply (r a : R) : pairingMap Λ r a = τ Λ (a * r) := rfl

omit [Λ.FiniteIndex] in
theorem pairingMap_injective : Function.Injective (pairingMap Λ) := by
  intro r s hrs
  apply (cosetBasis Λ).repr.injective
  apply Finsupp.ext
  intro p
  change (cosetBasis Λ).coord p r = (cosetBasis Λ).coord p s
  rw [← τ_inverse_mul_eq_coord, ← τ_inverse_mul_eq_coord]
  exact DFunLike.congr_fun hrs (bar (cosetBasis Λ p))

theorem pairingMap_surjective : Function.Surjective (pairingMap Λ) := by
  classical
  intro g
  refine ⟨∑ p, g (cosetBasis Λ p) • bar (cosetBasis Λ p), ?_⟩
  apply (cosetBasis Λ).ext
  intro q
  change τ Λ (cosetBasis Λ q * ∑ p, g (cosetBasis Λ p) • bar (cosetBasis Λ p)) = _
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, τ_basis_inverse, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp

/-- Perfectness of the actual trace pairing for every finite-index lattice. -/
def pairingEquiv : R ≃ₗ[S Λ] (R →ₗ[S Λ] S Λ) :=
  LinearEquiv.ofBijective (pairingMap Λ) ⟨pairingMap_injective Λ, pairingMap_surjective Λ⟩

def frobeniusPairing : FrobeniusDuality.Pairing (S Λ) R where
  trace := τ Λ
  dualEquiv := pairingEquiv Λ
  dual_apply _ _ := rfl

variable {V : Type*} [AddCommGroup V] [Module R V] [Module (S Λ) V]
  [IsScalarTower (S Λ) R V]

/-- Dual restriction for arbitrary original-ring modules, not only free modules. -/
def dualRestrictEquiv : (V →ₗ[R] R) ≃ₗ[S Λ] (V →ₗ[S Λ] S Λ) :=
  (frobeniusPairing Λ).dualRestrictEquiv

@[simp] theorem dualRestrictEquiv_apply (f : V →ₗ[R] R) (v : V) :
    dualRestrictEquiv Λ f v = τ Λ (f v) := rfl

variable {W : Type*} [AddCommGroup W] [Module R W] [Module (S Λ) W]
  [IsScalarTower (S Λ) R W]

theorem dualRestrict_naturality (f : V →ₗ[R] W) (g : W →ₗ[R] R) :
    dualRestrictEquiv Λ (g.comp f) =
      (dualRestrictEquiv Λ g).comp (f.restrictScalars (S Λ)) := rfl

end FiniteIndex

end

end Decoupling.GeneralLatticeRestriction
