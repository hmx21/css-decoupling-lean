import Decoupling.HighDim.ProfileStabilityProjective

/-!
# Lemma 5 for product-state ancillas and identity X checks

The quotients in this file are formed from the actual stabilized matrices
in `StableCSS`. Their kernel/image identities are proved explicitly. The
profile isomorphisms below preserve the whole positive derived object.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Abelian Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [CommRing K] {D : ℕ}
local notation "R" => Laurent K D

def conjugateProductIso (M T : ModuleCat R) :
    Layers.conjugate (ModuleCat.of R (M × T)) ≅
      ModuleCat.of R (Layers.conjugate M × Layers.conjugate T) :=
  (show Layers.conjugate (ModuleCat.of R (M × T)) ≃ₗ[R]
      ModuleCat.of R (Layers.conjugate M × Layers.conjugate T) from {
    toFun x := x
    invFun x := x
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl }).toModuleIso

/-- The actual positive profile is unaffected by a conjugate-projective summand. -/
def moduleProductProfileIso (M T : ModuleCat R) [Projective (Layers.conjugate T)] :
    moduleProfile (ModuleCat.of R (M × T)) ≅ moduleProfile M :=
  ResolutionComparison.profileIsoOfModuleIso (ModuleCat.of R R)
    (projectiveResolution (Layers.conjugate (ModuleCat.of R (M × T))))
    (conjugateProductIso M T)
    (projectiveResolution (ModuleCat.of R (Layers.conjugate M × Layers.conjugate T))) ≪≫
  projectiveSummandProfileIso (projectiveResolution (Layers.conjugate M))
    (Layers.conjugate T) (ModuleCat.of R R)
    (projectiveResolution (ModuleCat.of R (Layers.conjugate M × Layers.conjugate T)))

variable {Q C A B I : Type} [Fintype C] [Fintype A] [Fintype B] [Fintype I]
  [DecidableEq A] [DecidableEq B]

/-- Forget the fully stabilized plus coordinates, keep the free zero coordinates. -/
def ancillaQuotientMap (H : Matrix C Q R) :
    (((Q ⊕ A) ⊕ B) → R) →ₗ[R] (matrixReduced H × (B → R)) :=
  (((LinearMap.range (dagger H).mulVecLin).mkQ).comp
    (LinearMap.funLeft R R (fun q => Sum.inl (Sum.inl q)))).prod
      (LinearMap.funLeft R R Sum.inr)

omit [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B] in
theorem ancillaQuotientMap_surjective (H : Matrix C Q R) :
    Function.Surjective (ancillaQuotientMap (A := A) (B := B) H) := by
  rintro ⟨v, b⟩
  obtain ⟨x, hx⟩ := (LinearMap.range (dagger H).mulVecLin).mkQ_surjective v
  exact ⟨Sum.elim (Sum.elim x 0) b, Prod.ext hx rfl⟩

omit [Fintype B] [DecidableEq B] in
theorem ancillaQuotientMap_kernel (H : Matrix C Q R) :
    LinearMap.ker (ancillaQuotientMap (A := A) (B := B) H) =
      LinearMap.range (dagger (StableCSS.H_X (A := A) (B := B) H)).mulVecLin := by
  ext v
  change ancillaQuotientMap H v = 0 ↔ ∃ z, dagger (StableCSS.H_X H) *ᵥ z = v
  constructor
  · intro h
    have hq : (LinearMap.range (dagger H).mulVecLin).mkQ
        (fun q => v (.inl (.inl q))) = 0 := congrArg Prod.fst h
    have hb : (v ∘ Sum.inr) = 0 := congrArg Prod.snd h
    obtain ⟨z, hz⟩ := (Submodule.Quotient.mk_eq_zero _).mp hq
    refine ⟨Sum.elim z (fun a => v (.inl (.inr a))), ?_⟩
    rw [StableCSS.dagger_X_mulVec]
    funext i
    rcases i with (q | a) | b
    · exact congrFun hz q
    · rfl
    · exact (congrFun hb b).symm
  · rintro ⟨z, rfl⟩
    apply Prod.ext
    · apply (Submodule.Quotient.mk_eq_zero _).mpr
      refine ⟨z ∘ Sum.inl, ?_⟩
      funext q
      simp [StableCSS.dagger_X_mulVec]
    · funext b
      change (dagger (StableCSS.H_X (A := A) (B := B) H) *ᵥ z) (.inr b) = 0
      rw [StableCSS.dagger_X_mulVec]
      rfl

/-- Plus ancillas add no reduced degrees of freedom; zero ancillas add exactly a free summand. -/
def ancillaReducedIso (H : Matrix C Q R) :
    matrixReduced (StableCSS.H_X (A := A) (B := B) H) ≅
      ModuleCat.of R (matrixReduced H × (B → R)) :=
  ((Submodule.quotEquivOfEq _ _ (ancillaQuotientMap_kernel (A := A) (B := B) H).symm).trans
    ((ancillaQuotientMap H).quotKerEquivOfSurjective (ancillaQuotientMap_surjective H))).toModuleIso

/-- Both families of actual product-state ancillas leave the entire profile unchanged. -/
def ancillaProfileIso (H : Matrix C Q R) :
    matrixProfile (StableCSS.H_X (A := A) (B := B) H) ≅ matrixProfile H := by
  let : Projective (ModuleCat.of R (B → R)) :=
    ModuleCat.projective_of_free (Pi.basisFun R B)
  let : Projective (Layers.conjugate (ModuleCat.of R (B → R))) :=
    Projective.of_iso (Layers.conjugateFreeEquiv B).toModuleIso.symm inferInstance
  exact moduleProfileIso (ancillaReducedIso (A := A) (B := B) H) ≪≫
    moduleProductProfileIso (matrixReduced H) (ModuleCat.of R (B → R))

/-- Identity-valued X checks are literal zero rows and preserve the actual stabilizer image. -/
def identityChecksReducedIso (H : Matrix C Q R) :
    matrixReduced (StableCSS.identityChecks (A := I) H) ≅ matrixReduced H := by
  apply LinearEquiv.toModuleIso
  apply Submodule.quotEquivOfEq
  ext v
  exact StableCSS.identityChecks_dagger_image H v

/-- Adjoining identity X checks preserves the full positive RHom profile. -/
def identityChecksProfileIso (H : Matrix C Q R) :
    matrixProfile (StableCSS.identityChecks (A := I) H) ≅ matrixProfile H :=
  moduleProfileIso (identityChecksReducedIso H)

end
end Decoupling.HighDim.ProfileStability
