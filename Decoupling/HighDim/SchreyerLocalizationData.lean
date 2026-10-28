import Decoupling.HighDim.PolynomialLaurentImage
import Decoupling.HighDim.SchreyerResolutionData
import Decoupling.HighDim.FiniteResolution

/-!
# HD014 localizing the genuine polynomial matrix resolution

The output native resolution has explicit finite-power coordinates at
every degree. Projectivity and freeness come from these powers; the
construction does not invoke a projective-freeness or terminal-basis theorem.
The polynomial resolution is an intermediate output, to be supplied by
the proved Schreyer construction in the final theorem.
-/
namespace Decoupling.HighDim.SchreyerLocalization
open CategoryTheory CategoryTheory.Limits Matrix PolynomialLaurent
noncomputable section
universe u
variable {R : Type u} [CommRing R]

structure FreeData (M : ModuleCat.{u} R) (length : ℕ) where
  data : FiniteResolution.Data M length
  rank : ℕ → ℕ
  coordinates : ∀ k, data.X k ≃ₗ[R] (Fin (rank k) → R)

theorem FreeData.free {M : ModuleCat.{u} R} {length : ℕ}
    (A : FreeData M length) (k : ℕ) : Module.Free R (A.data.X k) :=
  Module.Free.of_equiv (A.coordinates k).symm

variable {K : Type u} [Field K] {D r length : ℕ}
  {N : Submodule (SchreyerModule.Poly K D) (SchreyerModule.Vec K D r)}
  (A : SchreyerResolution.Data N length)
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

def localizedImage : Submodule (Laurent K D) (Fin r → Laurent K D) :=
  LinearMap.range (A.augmentation.map (inclusion D K)).mulVecLin

def nativeData : FiniteResolution.Data
    (ModuleCat.of (Laurent K D) (localizedImage A)) length where
  X k := ModuleCat.of (Laurent K D) (Fin (A.rank k) → Laurent K D)
  d k := ModuleCat.ofHom ((A.d k).map (inclusion D K)).mulVecLin
  sq k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change (A.d k).map (inclusion D K)*ᵥ((A.d (k+1)).map (inclusion D K)*ᵥx) = 0
    rw [Matrix.mulVec_mulVec,←map_matrix_mul,A.d_comp]
    simp
  ε := ModuleCat.ofHom (A.augmentation.map (inclusion D K)).mulVecLin.rangeRestrict
  d_ε := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    change (A.augmentation.map (inclusion D K))*ᵥ((A.d 0).map (inclusion D K)*ᵥx) = 0
    rw [Matrix.mulVec_mulVec,←map_matrix_mul,A.augmentation_comp]
    simp
  surjective := by
    intro x
    obtain ⟨v,hv⟩ := x.property
    exact ⟨v,Subtype.ext hv⟩
  exact_zero := by
    change LinearMap.range ((A.d 0).map (inclusion D K)).mulVecLin =
      LinearMap.ker (A.augmentation.map (inclusion D K)).mulVecLin.rangeRestrict
    rw [LinearMap.ker_rangeRestrict]
    exact localized_range_eq_kernel A.augmentation (A.d 0) A.exact_zero.symm
  exact_succ k := localized_range_eq_kernel (A.d k) (A.d (k+1)) (A.exact_succ k).symm
  projective k := inferInstanceAs (Projective (ModuleCat.of (Laurent K D) (Fin (A.rank k) → Laurent K D)))
  finite k := Module.Finite.of_basis (Pi.basisFun (Laurent K D) (Fin (A.rank k)))
  zero_above k hk := by
    change IsZero (ModuleCat.of (Laurent K D) (Fin (A.rank k) → Laurent K D))
    rw [A.zero_above k hk]
    exact ModuleCat.isZero_of_subsingleton _

def native : FreeData (ModuleCat.of (Laurent K D) (localizedImage A)) length where
  data := nativeData A
  rank := A.rank
  coordinates _ := LinearEquiv.refl (Laurent K D) _

@[simp] theorem native_rank (k : ℕ) : (native A).rank k = A.rank k := rfl

theorem native_differential (k : ℕ) :
    ((native A).data.d k).hom = ((A.d k).map (inclusion D K)).mulVecLin := rfl

theorem native_augmentation (x : Fin (A.rank 0) → Laurent K D) :
    (((native A).data.ε).hom x).val = A.augmentation.map (inclusion D K)*ᵥx := rfl

end
end Decoupling.HighDim.SchreyerLocalization
