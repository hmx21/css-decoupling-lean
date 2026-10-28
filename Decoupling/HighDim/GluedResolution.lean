import Decoupling.HighDim.GluedMetachecks
import Decoupling.HighDim.FiniteResolutionDual
import Decoupling.HighDim.ResolutionComparison

/-!
# Explicit projective resolution of the actual glued-code reduced module

The prescribed presentation has ranks 6, 4, 1 and then zero. Every
exactness field is discharged using the actual matrices. Conjugation
and the native resolution comparison connect its dual to `Profile.S_X`.
-/

namespace Decoupling.HighDim.Glued

open CategoryTheory CategoryTheory.Limits Matrix
noncomputable section
attribute [local instance] HasDerivedCategory.standard
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K]

def resolutionRank : ℕ → ℕ
  | 0 => 6
  | 1 => 4
  | 2 => 1
  | _ + 3 => 0

def resolutionTerm (n : ℕ) : ModuleCat (Laurent K 3) :=
  ModuleCat.of (Laurent K 3) (Fin (resolutionRank n) → Laurent K 3)

def resolutionD : (n : ℕ) → resolutionTerm K (n + 1) ⟶ resolutionTerm K n
  | 0 => ModuleCat.ofHom (dagger (xChecks K)).mulVecLin
  | 1 => ModuleCat.ofHom (dagger (metacheck K)).mulVecLin
  | _ + 2 => 0

theorem resolutionD_sq (n : ℕ) : resolutionD K (n + 1) ≫ resolutionD K n = 0 := by
  rcases n with _ | (_ | n)
  · apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    change dagger (xChecks K) *ᵥ (dagger (metacheck K) *ᵥ v) = 0
    rw [Matrix.mulVec_mulVec, ← dagger_mul, metacheck_comp]
    simp
  · simp [resolutionD]
  · simp [resolutionD]

def resolutionAugmentation : resolutionTerm K 0 ⟶ Layers.reduced (checks K) :=
  ModuleCat.ofHom (LinearMap.range (dagger (xChecks K)).mulVecLin).mkQ

def resolutionData : FiniteResolution.Data (Layers.reduced (checks K)) 2 where
  X := resolutionTerm K
  d := resolutionD K
  sq := resolutionD_sq K
  ε := resolutionAugmentation K
  d_ε := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro v
    exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨v, rfl⟩
  surjective := (LinearMap.range (dagger (xChecks K)).mulVecLin).mkQ_surjective
  exact_zero := by
    change LinearMap.range (dagger (xChecks K)).mulVecLin =
      LinearMap.ker (LinearMap.range (dagger (xChecks K)).mulVecLin).mkQ
    rw [Submodule.ker_mkQ]
  exact_succ n := by
    rcases n with _ | (_ | n)
    · ext v
      exact (exact_metacheck K v).symm
    · change LinearMap.range (0 : (Fin 0 → Laurent K 3) →ₗ[Laurent K 3]
          (Fin 1 → Laurent K 3)) = LinearMap.ker (dagger (metacheck K)).mulVecLin
      rw [LinearMap.range_zero, LinearMap.ker_eq_bot.mpr (metacheck_dagger_injective K)]
    · change LinearMap.range (0 : (Fin 0 → Laurent K 3) →ₗ[Laurent K 3]
          (Fin 0 → Laurent K 3)) = LinearMap.ker
          (0 : (Fin 0 → Laurent K 3) →ₗ[Laurent K 3] (Fin (resolutionRank (n + 2)) → Laurent K 3))
      exact Subsingleton.elim _ _
  projective n := by
    change Projective (ModuleCat.of (Laurent K 3) (Fin (resolutionRank n) → Laurent K 3))
    infer_instance
  finite n := by
    let : Module.Finite (Laurent K 3) (Laurent K 3) := Module.Finite.self _
    change Module.Finite (Laurent K 3) (Fin (resolutionRank n) → Laurent K 3)
    exact Module.Finite.pi
  zero_above n hn := by
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
    change IsZero (ModuleCat.of (Laurent K 3) (Fin 0 → Laurent K 3))
    exact ModuleCat.isZero_of_subsingleton _

def reducedResolution : ProjectiveResolution (Layers.reduced (checks K)) :=
  (resolutionData K).toProjectiveResolution

def conjugateResolution : ProjectiveResolution (Layers.conjugate (Layers.reduced (checks K))) :=
  (ModuleCat.restrictScalars (bar : Laurent K 3 ≃+* Laurent K 3).toRingHom).mapProjectiveResolution
    (reducedResolution K)

def nativeProfileIso :
    Profile.ofResolution (conjugateResolution K) (ModuleCat.of (Laurent K 3) (Laurent K 3)) ≅
      Profile.S_X (checks K) :=
  ResolutionComparison.profileIso _ (conjugateResolution K) (Profile.resolution (checks K))

end
end Decoupling.HighDim.Glued
