import Decoupling.CoarseBasis

/-!
# Rectangular retained lattices nℤ³

This supplies the first finite-period restriction as well as doubling. The
coefficient ring is the literal subring of Laurent sums whose exponents are
multiples of n. Integer division includes negative translation exponents.
-/

namespace Decoupling.GeneralRetained

open Module

noncomputable section

def scaleExponent (n : ℕ) : Translation →+ Translation where
  toFun a i := (n : ℤ) * a i
  map_zero' := by funext i; simp
  map_add' a b := by funext i; simp [mul_add]

def embed (n : ℕ) : R →+* R :=
  AddMonoidAlgebra.mapDomainRingHom (ZMod 2) (scaleExponent n)

def retained (n : ℕ) : Subring R := (embed n).range
abbrev S (n : ℕ) := retained n

instance (n : ℕ) : Algebra (S n) R := (retained n).subtype.toAlgebra

variable (n : ℕ) [NeZero n]

theorem scaleExponent_injective : Function.Injective (scaleExponent n) := by
  intro a b h
  funext i
  have hi := congrFun h i
  change (n : ℤ) * a i = (n : ℤ) * b i at hi
  exact mul_left_cancel₀ (by exact_mod_cast NeZero.ne n) hi

theorem embed_injective : Function.Injective (embed n) :=
  AddMonoidAlgebra.mapDomain_injective (scaleExponent_injective n)

/-- Rename Laurent generators to their nth powers in the actual subring. -/
def renameEquiv : R ≃+* S n :=
  RingEquiv.ofBijective (embed n).rangeRestrict
    ⟨fun _ _ h => embed_injective n (congrArg Subtype.val h),
      (embed n).rangeRestrict_surjective⟩

omit [NeZero n] in
@[simp] theorem embed_monomial (a : Translation) :
    embed n (monomial a) = monomial (scaleExponent n a) := by
  simp [embed, monomial]

abbrev Residue := Fin 3 → Fin n

def residueExponent (p : Residue n) : Translation := fun i => (p i : ℤ)

def exponentEquiv : Translation ≃ Residue n × Translation where
  toFun a := (fun i => (Int.divModEquiv n (a i)).2,
    fun i => (Int.divModEquiv n (a i)).1)
  invFun p i := (Int.divModEquiv n).symm (p.2 i, p.1 i)
  left_inv a := by
    funext i
    exact (Int.divModEquiv n).symm_apply_apply (a i)
  right_inv p := by
    apply Prod.ext
    · funext i
      exact congrArg Prod.snd ((Int.divModEquiv n).apply_symm_apply (p.2 i, p.1 i))
    · funext i
      exact congrArg Prod.fst ((Int.divModEquiv n).apply_symm_apply (p.2 i, p.1 i))

theorem exponentEquiv_symm (p : Residue n) (a : Translation) :
    (exponentEquiv n).symm (p, a) = scaleExponent n a + residueExponent n p := by
  funext i
  simp [exponentEquiv, Int.divModEquiv, scaleExponent, residueExponent, mul_comm]

def decomposeAddEquiv : R ≃+ (Residue n →₀ S n) :=
  AddMonoidAlgebra.coeffAddEquiv.trans <|
    (Finsupp.domCongr (exponentEquiv n)).trans <|
      Finsupp.curryAddEquiv.trans <|
        Finsupp.mapRange.addEquiv
          (AddMonoidAlgebra.coeffAddEquiv.symm.trans (renameEquiv n).toAddEquiv)

@[simp] theorem decompose_single (a : Translation) (t : ZMod 2) :
    decomposeAddEquiv n (AddMonoidAlgebra.single a t) =
      Finsupp.single (exponentEquiv n a).1
        (renameEquiv n (AddMonoidAlgebra.single (exponentEquiv n a).2 t)) := by
  simp [decomposeAddEquiv, Finsupp.domCongr]

def assemble : (Residue n →₀ S n) →ₗ[S n] R :=
  Finsupp.linearCombination (S n) (fun p => monomial (residueExponent n p))

omit [NeZero n] in
@[simp] theorem assemble_single (p : Residue n) (s : S n) :
    assemble n (Finsupp.single p s) = s • monomial (residueExponent n p) := by
  simp [assemble]

theorem renamed_single_smul (a : Translation) (t : ZMod 2) (p : Residue n) :
    renameEquiv n (AddMonoidAlgebra.single a t) • monomial (residueExponent n p) =
      AddMonoidAlgebra.single (scaleExponent n a + residueExponent n p) t := by
  rw [Algebra.smul_def]
  change embed n (AddMonoidAlgebra.single a t) * monomial (residueExponent n p) = _
  simp [embed, monomial]

theorem assemble_decompose (r : R) : assemble n (decomposeAddEquiv n r) = r := by
  have h : (assemble n).toAddMonoidHom.comp (decomposeAddEquiv n).toAddMonoidHom =
      AddMonoidHom.id R := by
    apply AddMonoidAlgebra.addMonoidHom_ext
    intro a t
    change assemble n (decomposeAddEquiv n (AddMonoidAlgebra.single a t)) =
      AddMonoidAlgebra.single a t
    rw [decompose_single, assemble_single, renamed_single_smul, ← exponentEquiv_symm]
    rw [(exponentEquiv n).symm_apply_apply]
  exact DFunLike.congr_fun h r

theorem assemble_eq_inverse :
    (assemble n : (Residue n →₀ S n) → R) = (decomposeAddEquiv n).symm := by
  funext v
  simpa only [(decomposeAddEquiv n).apply_symm_apply] using
    assemble_decompose n ((decomposeAddEquiv n).symm v)

def assemblyEquiv : (Residue n →₀ S n) ≃ₗ[S n] R :=
  LinearEquiv.ofBijective (assemble n) (by
    rw [assemble_eq_inverse]
    exact (decomposeAddEquiv n).symm.bijective)

def residueBasis : Basis (Residue n) (S n) R := Basis.ofRepr (assemblyEquiv n).symm

theorem residueBasis_repr (r : R) : (residueBasis n).repr r = decomposeAddEquiv n r := by
  apply (assemblyEquiv n).injective
  change assemblyEquiv n ((assemblyEquiv n).symm r) = assemble n (decomposeAddEquiv n r)
  rw [(assemblyEquiv n).apply_symm_apply, assemble_decompose]

@[simp] theorem residueBasis_apply (p : Residue n) :
    residueBasis n p = monomial (residueExponent n p) := by
  change assemble n (Finsupp.single p 1) = monomial (residueExponent n p)
  rw [assemble_single, one_smul]

instance retainedModuleFree : Module.Free (S n) R := Module.Free.of_basis (residueBasis n)
instance retainedModuleFinite : Module.Finite (S n) R := Module.Finite.of_basis (residueBasis n)

theorem finrank_retained : Module.finrank (S n) R = n ^ 3 := by
  rw [Module.finrank_eq_card_basis (residueBasis n)]
  simp [Residue]

end
end Decoupling.GeneralRetained
