import Decoupling.HighDim.Laurent
import Decoupling.FrobeniusDuality
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
import Mathlib.RingTheory.Finiteness.Basic

/-!
# Restriction to an arbitrary finite-index translation sublattice in any dimension

Source: `drafts/appendix.tex`, coarse-graining and duality paragraphs,
lines 263–306. This proves scalar and linear duality statements, not yet
a derived-profile isomorphism.

The retained ring is a literal subring of the manuscript's Laurent ring,
supported on `Λ ≤ ℤ^D`, over any commutative coefficient ring. Cosets, including negative exponents, give an actual
free basis. No rectangular shape of the sublattice is assumed.
-/

namespace Decoupling.HighDim.LatticeRestriction

open Module Matrix

noncomputable section

attribute [local instance] Classical.propDecidable

variable (K : Type*) [CommRing K] {D : ℕ}

variable (Λ : AddSubgroup (Translation D))

abbrev LatticeAlgebra := AddMonoidAlgebra K Λ

def embed : LatticeAlgebra K Λ →+* (Laurent K D) :=
  AddMonoidAlgebra.mapDomainRingHom K Λ.subtype

def retained : Subring (Laurent K D) := (embed K Λ).range
abbrev S := retained K Λ

instance : Algebra (S K Λ) (Laurent K D) := (retained K Λ).subtype.toAlgebra

theorem embed_injective : Function.Injective (embed K Λ) :=
  AddMonoidAlgebra.mapDomain_injective Subtype.val_injective

/-- The retained subring is the actual image of the subgroup algebra. -/
def latticeEquiv : LatticeAlgebra K Λ ≃+* S K Λ :=
  RingEquiv.ofBijective (embed K Λ).rangeRestrict
    ⟨fun _ _ h => embed_injective K Λ (congrArg Subtype.val h),
      (embed K Λ).rangeRestrict_surjective⟩

@[simp] theorem embed_single (a : Λ) (c : K) :
    embed K Λ (AddMonoidAlgebra.single a c) = AddMonoidAlgebra.single (a : (Translation D)) c := by
  simp [embed]

@[simp] theorem embed_coeff (r : LatticeAlgebra K Λ) (a : Λ) :
    (embed K Λ r).coeff (a : (Translation D)) = r.coeff a :=
  Finsupp.mapDomain_apply_of_injective Subtype.val_injective r.coeff a

/-- Membership in the actual retained subring is exactly support on `Λ`. -/
theorem mem_retained_iff (r : (Laurent K D)) : r ∈ retained K Λ ↔ ∀ a ∉ Λ, r.coeff a = 0 := by
  constructor
  · rintro ⟨p, rfl⟩ a ha
    exact Finsupp.mapDomain_of_notMem_range p.coeff a (by
      rintro ⟨b, rfl⟩
      exact ha b.property)
  · intro h
    have h' : ∀ a ∉ Set.range (Subtype.val : Λ → (Translation D)), r.coeff a = 0 := by
      intro a ha
      exact h a (by intro hm; exact ha ⟨⟨a, hm⟩, rfl⟩)
    obtain ⟨p, hp⟩ := (Finsupp.mem_range_mapDomain_iff
      (Subtype.val : Λ → (Translation D)) Subtype.val_injective r.coeff).mpr h'
    refine ⟨AddMonoidAlgebra.ofCoeff p, ?_⟩
    exact AddMonoidAlgebra.coeff_injective hp

theorem latticeEquiv_symm_coeff (s : S K Λ) (a : Λ) :
    ((latticeEquiv K Λ).symm s).coeff a = (s : (Laurent K D)).coeff (a : (Translation D)) := by
  have hs : embed K Λ ((latticeEquiv K Λ).symm s) = (s : (Laurent K D)) :=
    congrArg Subtype.val ((latticeEquiv K Λ).apply_symm_apply s)
  rw [← hs, embed_coeff]

abbrev Coset := (Translation D) ⧸ Λ

/-- Representatives are normalized so that the identity coset has exponent zero. -/
def representative (q : Coset Λ) : (Translation D) := by
  classical
  exact if q = 0 then 0 else q.out

@[simp] theorem representative_zero : representative Λ 0 = 0 := by simp [representative]

@[simp] theorem representative_class (q : Coset Λ) :
    (QuotientAddGroup.mk' Λ) (representative Λ q) = q := by
  by_cases hq : q = 0
  · subst q; simp [representative]
  · simp only [representative, hq, ↓reduceIte]
    exact Quotient.out_eq' q

theorem exponent_difference_mem (a : (Translation D)) :
    a - representative Λ ((QuotientAddGroup.mk' Λ) a) ∈ Λ := by
  apply (QuotientAddGroup.eq_zero_iff _).mp
  change (QuotientAddGroup.mk' Λ) (a - representative Λ ((QuotientAddGroup.mk' Λ) a)) = 0
  rw [map_sub, representative_class, sub_self]

/-- Every exponent is uniquely a chosen coset representative plus a retained exponent. -/
def exponentEquiv : (Translation D) ≃ Coset Λ × Λ where
  toFun a := ((QuotientAddGroup.mk' Λ) a,
    ⟨a - representative Λ ((QuotientAddGroup.mk' Λ) a), exponent_difference_mem Λ a⟩)
  invFun p := (p.2 : (Translation D)) + representative Λ p.1
  left_inv a := sub_add_cancel _ _
  right_inv p := by
    have hz : (QuotientAddGroup.mk' Λ) (p.2 : (Translation D)) = 0 :=
      (QuotientAddGroup.eq_zero_iff (p.2 : (Translation D))).mpr p.2.property
    have hp : (QuotientAddGroup.mk' Λ) ((p.2 : (Translation D)) + representative Λ p.1) = p.1 := by
      rw [map_add, representative_class, hz, zero_add]
    apply Prod.ext
    · exact hp
    · apply Subtype.ext
      change (p.2 : (Translation D)) + representative Λ p.1 -
        representative Λ ((QuotientAddGroup.mk' Λ) ((p.2 : (Translation D)) + representative Λ p.1)) = p.2
      rw [hp, add_sub_cancel_right]

@[simp] theorem exponentEquiv_symm (q : Coset Λ) (a : Λ) :
    (exponentEquiv Λ).symm (q, a) = (a : (Translation D)) + representative Λ q := rfl

def decomposeAddEquiv : (Laurent K D) ≃+ (Coset Λ →₀ S K Λ) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr (exponentEquiv Λ)).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv
          (AddMonoidAlgebra.coeffAddEquiv.symm.trans (latticeEquiv K Λ).toAddEquiv)

@[simp] theorem decompose_single (a : (Translation D)) (c : K) :
    decomposeAddEquiv K Λ (AddMonoidAlgebra.single a c) =
      Finsupp.single (exponentEquiv Λ a).1
        (latticeEquiv K Λ (AddMonoidAlgebra.single (exponentEquiv Λ a).2 c)) := by
  simp [decomposeAddEquiv, Finsupp.domCongr]

def assemble : (Coset Λ →₀ S K Λ) →ₗ[S K Λ] (Laurent K D) :=
  Finsupp.linearCombination (S K Λ) (fun q => monomial K (representative Λ q))

@[simp] theorem assemble_single (q : Coset Λ) (s : S K Λ) :
    assemble K Λ (Finsupp.single q s) = s • monomial K (representative Λ q) := by
  simp [assemble]

theorem lattice_single_smul (a : Λ) (c : K) (q : Coset Λ) :
    latticeEquiv K Λ (AddMonoidAlgebra.single a c) • monomial K (representative Λ q) =
      AddMonoidAlgebra.single ((a : (Translation D)) + representative Λ q) c := by
  rw [Algebra.smul_def]
  change embed K Λ (AddMonoidAlgebra.single a c) * monomial K (representative Λ q) = _
  simp [monomial]

theorem assemble_decompose (r : (Laurent K D)) : assemble K Λ (decomposeAddEquiv K Λ r) = r := by
  have h : (assemble K Λ).toAddMonoidHom.comp (decomposeAddEquiv K Λ).toAddMonoidHom =
      AddMonoidHom.id (Laurent K D) := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a c
    change assemble K Λ (decomposeAddEquiv K Λ (AddMonoidAlgebra.single a c)) = _
    rw [decompose_single, assemble_single, lattice_single_smul, ← exponentEquiv_symm]
    rw [(exponentEquiv Λ).symm_apply_apply]
    rfl
  exact DFunLike.congr_fun h r

theorem assemble_eq_inverse :
    (assemble K Λ : (Coset Λ →₀ S K Λ) → (Laurent K D)) = (decomposeAddEquiv K Λ).symm := by
  funext v
  simpa only [(decomposeAddEquiv K Λ).apply_symm_apply] using
    assemble_decompose K Λ ((decomposeAddEquiv K Λ).symm v)

def assemblyEquiv : (Coset Λ →₀ S K Λ) ≃ₗ[S K Λ] (Laurent K D) :=
  LinearEquiv.ofBijective (assemble K Λ) (by
    rw [assemble_eq_inverse]
    exact (decomposeAddEquiv K Λ).symm.bijective)

/-- The actual Laurent coset-monomial basis, valid even before finite index. -/
def cosetBasis : Basis (Coset Λ) (S K Λ) (Laurent K D) := Basis.ofRepr (assemblyEquiv K Λ).symm

theorem cosetBasis_repr (r : (Laurent K D)) : (cosetBasis K Λ).repr r = decomposeAddEquiv K Λ r := by
  apply (assemblyEquiv K Λ).injective
  change assemblyEquiv K Λ ((assemblyEquiv K Λ).symm r) = assemble K Λ (decomposeAddEquiv K Λ r)
  rw [(assemblyEquiv K Λ).apply_symm_apply, assemble_decompose]

@[simp] theorem cosetBasis_apply (q : Coset Λ) :
    cosetBasis K Λ q = monomial K (representative Λ q) := by
  change assemble K Λ (Finsupp.single q 1) = monomial K (representative Λ q)
  rw [assemble_single, one_smul]

instance retainedModuleFree : Module.Free (S K Λ) (Laurent K D) := Module.Free.of_basis (cosetBasis K Λ)

/-- Every genuinely free original-ring module remains free under scalar restriction. -/
theorem free_restrict_of_free (M : Type*) [AddCommMonoid M]
    [Module (S K Λ) M] [Module (Laurent K D) M] [IsScalarTower (S K Λ) (Laurent K D) M] [Module.Free (Laurent K D) M] :
    Module.Free (S K Λ) M := Module.Free.trans (R := S K Λ) (S := (Laurent K D)) (M := M)

/-- Restriction preserves arbitrary native projectives by restricting their
actual splitting off a free cover. -/
theorem projective_restrict (M : Type*) [AddCommGroup M]
    [Module (S K Λ) M] [Module (Laurent K D) M] [IsScalarTower (S K Λ) (Laurent K D) M] [Module.Projective (Laurent K D) M] :
    Module.Projective (S K Λ) M := by
  obtain ⟨i, hi⟩ := (Module.projective_def' (R := (Laurent K D)) (P := M)).mp inferInstance
  let : Module.Free (S K Λ) (M →₀ (Laurent K D)) := free_restrict_of_free K Λ (M →₀ (Laurent K D))
  apply Module.Projective.of_split (i.restrictScalars (S K Λ))
    ((Finsupp.linearCombination (Laurent K D) id).restrictScalars (S K Λ))
  apply LinearMap.ext
  intro m
  exact DFunLike.congr_fun hi m

/-- Keep precisely the coefficients supported on the retained lattice. -/
def τ : (Laurent K D) →ₗ[S K Λ] S K Λ := (cosetBasis K Λ).coord 0

theorem τ_coeff (r : (Laurent K D)) (a : Λ) :
    ((latticeEquiv K Λ).symm (τ K Λ r)).coeff a = r.coeff (a : (Translation D)) := by
  simp [τ, Basis.coord_apply, cosetBasis_repr, decomposeAddEquiv,
    Finsupp.domCongr, exponentEquiv_symm]

theorem τ_coe_coeff (r : (Laurent K D)) (a : (Translation D)) :
    (τ K Λ r : (Laurent K D)).coeff a = if a ∈ Λ then r.coeff a else 0 := by
  classical
  by_cases ha : a ∈ Λ
  · simp only [ha, ↓reduceIte]
    rw [← latticeEquiv_symm_coeff K Λ (τ K Λ r) ⟨a, ha⟩, τ_coeff]
  · simp only [ha, ↓reduceIte]
    exact (mem_retained_iff K Λ _).mp (τ K Λ r).property a ha

@[simp] theorem τ_one : τ K Λ 1 = 1 := by
  have hzero : cosetBasis K Λ (0 : Coset Λ) = 1 := by simp
  rw [← hzero]
  simp only [τ, Basis.coord_apply, Basis.repr_self, Finsupp.single_eq_same]

@[simp] theorem τ_algebraMap (s : S K Λ) : τ K Λ (algebraMap (S K Λ) (Laurent K D) s) = s := by
  change τ K Λ (s : (Laurent K D)) = s
  have h : τ K Λ ((s : (Laurent K D)) * 1) = s * τ K Λ 1 := (τ K Λ).map_smul s (1 : (Laurent K D))
  simpa only [mul_one, τ_one] using h

theorem bar_mem_retained {r : (Laurent K D)} (hr : r ∈ retained K Λ) : bar r ∈ retained K Λ := by
  apply (mem_retained_iff K Λ _).mpr
  intro a ha
  rw [bar_coeff]
  exact (mem_retained_iff K Λ _).mp hr (-a) (fun h => ha (by simpa using Λ.neg_mem h))

/-- Retained conjugation is literally the restriction of Laurent conjugation. -/
def barS : S K Λ ≃+* S K Λ where
  toFun s := ⟨bar (s : Laurent K D), bar_mem_retained K Λ s.property⟩
  invFun s := ⟨bar (s : Laurent K D), bar_mem_retained K Λ s.property⟩
  left_inv s := Subtype.ext (bar_bar (s : Laurent K D))
  right_inv s := Subtype.ext (bar_bar (s : Laurent K D))
  map_mul' s t := Subtype.ext (bar_mul (s : Laurent K D) (t : Laurent K D))
  map_add' s t := Subtype.ext (bar_add (s : Laurent K D) (t : Laurent K D))

@[simp] theorem coe_barS (s : S K Λ) : (barS K Λ s : (Laurent K D)) = bar (s : (Laurent K D)) := rfl

@[simp] theorem barS_barS (s : S K Λ) : barS K Λ (barS K Λ s) = s :=
  Subtype.ext (bar_bar (s : Laurent K D))

theorem τ_bar (r : (Laurent K D)) : τ K Λ (bar r) = barS K Λ (τ K Λ r) := by
  apply Subtype.ext
  ext a
  simp only [τ_coe_coeff, coe_barS, bar_coeff, AddSubgroup.neg_mem_iff]

section FiniteIndex

variable [Λ.FiniteIndex]

instance cosetFintype : Fintype (Coset Λ) := Fintype.ofFinite _

instance retainedModuleFinite : Module.Finite (S K Λ) (Laurent K D) := Module.Finite.of_basis (cosetBasis K Λ)

/-- Finite generation is preserved under a finite-index lattice restriction.
Together with `free_restrict_of_free`, this proves preservation of finite
free modules without assuming either conclusion. -/
theorem finite_restrict_of_finite (M : Type*) [AddCommMonoid M]
    [Module (S K Λ) M] [Module (Laurent K D) M]
    [IsScalarTower (S K Λ) (Laurent K D) M] [Module.Finite (Laurent K D) M] :
    Module.Finite (S K Λ) M := Module.Finite.trans (Laurent K D) M

theorem finrank_retained [Nontrivial K] : Module.finrank (S K Λ) (Laurent K D) = Λ.index := by
  rw [Module.finrank_eq_card_basis (cosetBasis K Λ)]
  exact Nat.card_eq_fintype_card.symm

omit [Λ.FiniteIndex] in
/-- Monomial representatives and their inverses are dual for coefficient extraction. -/
theorem τ_inverse_basis (p q : Coset Λ) :
    τ K Λ (bar (cosetBasis K Λ p) * cosetBasis K Λ q) = if p = q then 1 else 0 := by
  classical
  by_cases hpq : p = q
  · subst q
    simp
  · simp only [hpq, ↓reduceIte]
    rw [cosetBasis_apply, cosetBasis_apply, bar_monomial, monomial_mul]
    apply (latticeEquiv K Λ).symm.injective
    ext a
    rw [τ_coeff]
    have hne : -representative Λ p + representative Λ q ≠ (a : (Translation D)) := by
      intro ha
      have he : (exponentEquiv Λ).symm (p, a) = (exponentEquiv Λ).symm (q, 0) := by
        simp only [exponentEquiv_symm, ZeroMemClass.coe_zero, zero_add]
        rw [← ha]
        abel
      exact hpq (congrArg Prod.fst ((exponentEquiv Λ).symm.injective he))
    simp [monomial, hne]

omit [Λ.FiniteIndex] in
theorem τ_basis_inverse (p q : Coset Λ) :
    τ K Λ (cosetBasis K Λ p * bar (cosetBasis K Λ q)) = if p = q then 1 else 0 := by
  simpa only [mul_comm, eq_comm] using τ_inverse_basis K Λ q p

omit [Λ.FiniteIndex] in
theorem τ_inverse_mul_eq_coord (p : Coset Λ) (r : (Laurent K D)) :
    τ K Λ (bar (cosetBasis K Λ p) * r) = (cosetBasis K Λ).coord p r := by
  have h : (τ K Λ).comp (LinearMap.mul (S K Λ) (Laurent K D) (bar (cosetBasis K Λ p))) =
      (cosetBasis K Λ).coord p := by
    apply (cosetBasis K Λ).ext
    intro q
    change τ K Λ (bar (cosetBasis K Λ p) * cosetBasis K Λ q) = (cosetBasis K Λ).coord p _
    rw [τ_inverse_basis]
    simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]
  exact DFunLike.congr_fun h r

def pairingMap : (Laurent K D) →ₗ[S K Λ] ((Laurent K D) →ₗ[S K Λ] S K Λ) where
  toFun r := {
    toFun a := τ K Λ (a * r)
    map_add' a b := by simp [add_mul]
    map_smul' s a := by simp }
  map_add' r s := by
    apply LinearMap.ext
    intro a
    change τ K Λ (a * (r + s)) = τ K Λ (a * r) + τ K Λ (a * s)
    simp [mul_add]
  map_smul' s r := by
    apply LinearMap.ext
    intro a
    change τ K Λ (a * (s • r)) = s • τ K Λ (a * r)
    simp

omit [Λ.FiniteIndex] in
@[simp] theorem pairingMap_apply (r a : (Laurent K D)) : pairingMap K Λ r a = τ K Λ (a * r) := rfl

omit [Λ.FiniteIndex] in
theorem pairingMap_injective : Function.Injective (pairingMap K Λ) := by
  intro r s hrs
  apply (cosetBasis K Λ).repr.injective
  apply Finsupp.ext
  intro p
  change (cosetBasis K Λ).coord p r = (cosetBasis K Λ).coord p s
  rw [← τ_inverse_mul_eq_coord, ← τ_inverse_mul_eq_coord]
  exact DFunLike.congr_fun hrs (bar (cosetBasis K Λ p))

theorem pairingMap_surjective : Function.Surjective (pairingMap K Λ) := by
  classical
  intro g
  refine ⟨∑ p, g (cosetBasis K Λ p) • bar (cosetBasis K Λ p), ?_⟩
  apply (cosetBasis K Λ).ext
  intro q
  change τ K Λ (cosetBasis K Λ q * ∑ p, g (cosetBasis K Λ p) • bar (cosetBasis K Λ p)) = _
  rw [Finset.mul_sum, map_sum]
  simp only [mul_smul_comm, map_smul, τ_basis_inverse, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  simp

/-- Perfectness of the actual trace pairing for every finite-index lattice. -/
def pairingEquiv : (Laurent K D) ≃ₗ[S K Λ] ((Laurent K D) →ₗ[S K Λ] S K Λ) :=
  LinearEquiv.ofBijective (pairingMap K Λ) ⟨pairingMap_injective K Λ, pairingMap_surjective K Λ⟩

def frobeniusPairing : FrobeniusDuality.Pairing (S K Λ) (Laurent K D) where
  trace := τ K Λ
  dualEquiv := pairingEquiv K Λ
  dual_apply _ _ := rfl

variable {V : Type*} [AddCommGroup V] [Module (Laurent K D) V] [Module (S K Λ) V]
  [IsScalarTower (S K Λ) (Laurent K D) V]

/-- Dual restriction for arbitrary original-ring modules, not only free modules. -/
def dualRestrictEquiv : (V →ₗ[(Laurent K D)] (Laurent K D)) ≃ₗ[S K Λ] (V →ₗ[S K Λ] S K Λ) :=
  (frobeniusPairing K Λ).dualRestrictEquiv

@[simp] theorem dualRestrictEquiv_apply (f : V →ₗ[(Laurent K D)] (Laurent K D)) (v : V) :
    dualRestrictEquiv K Λ f v = τ K Λ (f v) := rfl

variable {W : Type*} [AddCommGroup W] [Module (Laurent K D) W] [Module (S K Λ) W]
  [IsScalarTower (S K Λ) (Laurent K D) W]

theorem dualRestrict_naturality (f : V →ₗ[(Laurent K D)] W) (g : W →ₗ[(Laurent K D)] (Laurent K D)) :
    dualRestrictEquiv K Λ (g.comp f) =
      (dualRestrictEquiv K Λ g).comp (f.restrictScalars (S K Λ)) := rfl

end FiniteIndex

end

end Decoupling.HighDim.LatticeRestriction
