import Decoupling.HighDim.ProfileStabilityResolution

/-!
# A projective direct summand does not change the full positive profile

The actual chain inclusion splits degreewise. After dualizing it is an
isomorphism in every positive degree and a split epimorphism in degree zero.
Consequently its positive good truncation is a quasi-isomorphism. This
proves invariance of the entire derived object, including its gluing data.
-/

namespace Decoupling.HighDim.ProfileStability

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian HomologicalComplex
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable {R : Type} [CommRing R] {X : ModuleCat R}
  (P : ProjectiveResolution X) (T Y : ModuleCat R)

def enlargedInclusion : P.complex ⟶ enlargedComplex P T where
  f
    | 0 => ModuleCat.ofHom (LinearMap.inl R (P.complex.X 0) T)
    | _ + 1 => 𝟙 _
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [enlargedComplex_d]
    cases j <;> rfl

def enlargedProjection : enlargedComplex P T ⟶ P.complex where
  f
    | 0 => ModuleCat.ofHom (LinearMap.fst R (P.complex.X 0) T)
    | _ + 1 => 𝟙 _
  comm' i j hij := by
    obtain rfl : j + 1 = i := hij
    rw [enlargedComplex_d]
    cases j <;> rfl

@[simp] theorem enlargedInclusion_projection :
    enlargedInclusion P T ≫ enlargedProjection P T = 𝟙 P.complex := by
  ext n
  cases n <;> rfl

/-- Evaluation on the original resolution inside the enlarged one. -/
def enlargedDualMap :
    (enlargedComplex P T).linearYonedaObj R Y ⟶ P.complex.linearYonedaObj R Y :=
  ResolutionComparison.dualMap Y (enlargedInclusion P T)

instance enlargedDualMap_epi (n : ℕ) : Epi ((enlargedDualMap P T Y).f n) := by
  have h : ResolutionComparison.dualMap Y (enlargedProjection P T) ≫
      enlargedDualMap P T Y = 𝟙 _ := by
    rw [enlargedDualMap, ← ResolutionComparison.dualMap_comp,
      enlargedInclusion_projection, ResolutionComparison.dualMap_id]
  let : IsSplitEpi ((enlargedDualMap P T Y).f n) :=
    ⟨⟨{ section_ := (ResolutionComparison.dualMap Y (enlargedProjection P T)).f n,
         id := congrArg (fun f => f.f n) h }⟩⟩
  infer_instance

instance enlargedDualMap_isIso (n : ℕ) : IsIso ((enlargedDualMap P T Y).f (n + 1)) := by
  have h : (enlargedDualMap P T Y).f (n + 1) = 𝟙 _ := by
    ext f
    rfl
  rw [h]
  infer_instance

def enlargedExtendedDualMap :
    ((enlargedComplex P T).linearYonedaObj R Y).extend ComplexShape.embeddingUpNat ⟶
    Profile.rHomComplex P Y :=
  extendMap (enlargedDualMap P T Y) ComplexShape.embeddingUpNat

instance enlargedExtendedDualMap_epi (n : ℕ) :
    Epi ((enlargedExtendedDualMap P T Y).f (n : ℤ)) := by
  dsimp only [enlargedExtendedDualMap]
  rw [extendMap_f _ _ (i := n) (i' := (n : ℤ)) rfl]
  infer_instance

instance enlargedExtendedDualMap_isIso (n : ℕ) :
    IsIso ((enlargedExtendedDualMap P T Y).f (n + 1 : ℕ)) := by
  dsimp only [enlargedExtendedDualMap]
  rw [extendMap_f _ _ (i := n + 1) (i' := ((n + 1 : ℕ) : ℤ)) rfl]
  infer_instance

theorem enlargedExtendedDualMap_quasiIsoAt (n : ℕ) :
    QuasiIsoAt (enlargedExtendedDualMap P T Y) (n + 1 : ℕ) := by
  rw [quasiIsoAt_iff' (enlargedExtendedDualMap P T Y) (n : ℤ)
    (n + 1 : ℕ) (n + 2 : ℕ) (by simp) (by simp; omega)]
  let f := (shortComplexFunctor' (ModuleCat R) (.up ℤ)
    (n : ℕ) (n + 1 : ℕ) (n + 2 : ℕ)).map (enlargedExtendedDualMap P T Y)
  let : Epi f.τ₁ := enlargedExtendedDualMap_epi P T Y n
  let : IsIso f.τ₂ := enlargedExtendedDualMap_isIso P T Y n
  let : IsIso f.τ₃ := enlargedExtendedDualMap_isIso P T Y (n + 1)
  exact ShortComplex.quasiIso_of_epi_of_isIso_of_mono f

variable [Projective T]

def enlargedPositiveDualMap :
    Profile.positiveComplex (enlargedResolution P T) Y ⟶ Profile.positiveComplex P Y :=
  CochainComplex.truncGEMap (enlargedExtendedDualMap P T Y) 1

instance enlargedPositiveDualMap_quasiIso : QuasiIso (enlargedPositiveDualMap P T Y) := by
  apply (CochainComplex.quasiIso_truncGEMap_iff (enlargedExtendedDualMap P T Y) 1).mpr
  intro n hn
  obtain ⟨m, rfl⟩ : ∃ m : ℕ, n = (m + 1 : ℕ) := ⟨(n - 1).toNat, by omega⟩
  exact enlargedExtendedDualMap_quasiIsoAt P T Y m

/-- The positive derived Hom profile is unchanged by an actual projective summand. -/
def projectiveSummandProfileIso (Q : ProjectiveResolution (productModule (X := X) T)) :
    Profile.ofResolution Q Y ≅ Profile.ofResolution P Y :=
  ResolutionComparison.profileIso Y Q (enlargedResolution P T) ≪≫
    asIso (DerivedCategory.Q.map (enlargedPositiveDualMap P T Y))

end
end Decoupling.HighDim.ProfileStability
