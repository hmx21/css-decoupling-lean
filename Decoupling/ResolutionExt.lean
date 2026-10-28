import Decoupling.ToricExt
import Decoupling.Syndrome

/-!
# Genuine Ext from a supplied two-step free resolution

The input is an actual exact finite-free resolution, not an assumed
cohomology-to-Ext equivalence. The proof constructs the syzygy short exact
sequence and identifies its Hom terms in the standard dual coordinates.

The final `CSSResolution` specialization proves Eq. (8) for the literal
physical cochain `(H_X, Γ†)` and the genuine `ExtLayers.E_X` modules, including
vanishing above degree two. Existence of the supplied free resolution is
an explicit upstream obligation. General naturality under scalar restriction
is not asserted here; the cycle representative and descended functional
formulas record the concrete maps for that later comparison.
-/

namespace Decoupling.ResolutionExt

open Matrix CategoryTheory CategoryTheory.Abelian
open Duality ExtLayers

noncomputable section

/-- The non-augmented part of an exact length-two free resolution, whose
augmentation is the canonical map to `coker d₁`. -/
structure Resolution (n₀ n₁ n₂ : ℕ) where
  d₁ : Matrix (Fin n₀) (Fin n₁) R
  d₂ : Matrix (Fin n₁) (Fin n₂) R
  zero : d₁ * d₂ = 0
  exact₁ : ∀ a : Fin n₁ → R, d₁ *ᵥ a = 0 ↔ ∃ b : Fin n₂ → R, d₂ *ᵥ b = a
  injective₂ : Function.Injective (fun b : Fin n₂ → R => d₂ *ᵥ b)

namespace Resolution

variable {n₀ n₁ n₂ : ℕ} (r : Resolution n₀ n₁ n₂)

abbrev M := Cokernel r.d₁
abbrev K := Cokernel r.d₂

abbrev qK : (Fin n₁ → R) →ₗ[R] r.K := (LinearMap.range r.d₂.mulVecLin).mkQ
abbrev qM : (Fin n₀ → R) →ₗ[R] r.M := (LinearMap.range r.d₁.mulVecLin).mkQ

/-- The first differential descends through the image of the second. -/
def syzygyInclusion : r.K →ₗ[R] (Fin n₀ → R) :=
  (LinearMap.range r.d₂.mulVecLin).liftQ r.d₁.mulVecLin (by
    rintro _ ⟨a, rfl⟩
    change r.d₁ *ᵥ (r.d₂ *ᵥ a) = 0
    rw [mulVec_mulVec, r.zero, zero_mulVec])

@[simp] theorem syzygyInclusion_mk (a : Fin n₁ → R) :
    r.syzygyInclusion (r.qK a) = r.d₁ *ᵥ a := rfl

theorem syzygyInclusion_injective : Function.Injective r.syzygyInclusion := by
  apply LinearMap.ker_eq_bot.mp
  apply LinearMap.ker_eq_bot'.mpr
  intro a ha
  obtain ⟨v, rfl⟩ := (LinearMap.range r.d₂.mulVecLin).mkQ_surjective a
  exact (Submodule.Quotient.mk_eq_zero _).mpr ((r.exact₁ v).mp ha)

theorem qM_syzygyInclusion : r.qM.comp r.syzygyInclusion = 0 := by
  apply Submodule.linearMap_qext
  apply LinearMap.ext
  intro a
  exact (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩

/-- The actual projective-cover sequence `0 → K → P₀ → M → 0`. -/
def syzygySequence : ShortComplex (ModuleCat R) :=
  ShortComplex.moduleCatMk r.syzygyInclusion r.qM r.qM_syzygyInclusion

theorem syzygySequence_shortExact : r.syzygySequence.ShortExact where
  exact := by
    apply (r.syzygySequence.moduleCat_exact_iff).mpr
    intro a ha
    obtain ⟨b, hb⟩ := (Submodule.Quotient.mk_eq_zero _).mp ha
    exact ⟨r.qK b, hb⟩
  mono_f := (ModuleCat.mono_iff_injective _).mpr r.syzygyInclusion_injective
  epi_g := (ModuleCat.epi_iff_surjective _).mpr (LinearMap.range r.d₁.mulVecLin).mkQ_surjective

instance syzygySequence_projective_middle : Projective r.syzygySequence.X₂ :=
  ModuleCat.projective_of_free (Pi.basisFun R (Fin n₀))

/-- The dual three-term cochain, with the genuine transpose matrices. -/
def dualCochain : Syndrome.Cochain R (Fin n₀ → R) (Fin n₁ → R) (Fin n₂ → R) where
  d₁ := r.d₁.transpose.mulVecLin
  γ := r.d₂.transpose.mulVecLin
  square := by
    apply LinearMap.ext
    intro a
    change r.d₂.transpose *ᵥ (r.d₁.transpose *ᵥ a) = 0
    rw [mulVec_mulVec, ← Matrix.transpose_mul, r.zero, Matrix.transpose_zero, zero_mulVec]

/-- Pull a functional on the syzygy quotient back to its free cover and
write it in the dual standard coordinates. -/
def pullbackCoordinates :
    (ModuleCat.of R r.K ⟶ ModuleCat.of R R) →ₗ[R] (Fin n₁ → R) where
  toFun f := dualCoordinates (Fin n₁) (f.hom.comp r.qK)
  map_add' f g := by
    funext i
    simp [dualCoordinates_apply]
  map_smul' a f := by
    funext i
    simp [dualCoordinates_apply]

theorem pullbackCoordinates_mem_ker (f : ModuleCat.of R r.K ⟶ ModuleCat.of R R) :
    r.pullbackCoordinates f ∈ LinearMap.ker r.d₂.transpose.mulVecLin := by
  let f' : r.K →ₗ[R] R := f.hom
  have hf : (f'.comp r.qK).comp r.d₂.mulVecLin = 0 := by
    apply LinearMap.ext
    intro a
    change f' (Submodule.Quotient.mk (r.d₂ *ᵥ a)) = 0
    have ha : (Submodule.Quotient.mk (r.d₂ *ᵥ a) : r.K) = 0 :=
      (Submodule.Quotient.mk_eq_zero _).mpr ⟨a, rfl⟩
    rw [ha, map_zero]
  change r.d₂.transpose *ᵥ dualCoordinates (Fin n₁) (f'.comp r.qK) = 0
  rw [← dualCoordinates_precomp, hf, map_zero]

/-- The Hom group of the actual syzygy maps to actual dual cycles. -/
def homToCycles : (ModuleCat.of R r.K ⟶ ModuleCat.of R R) →ₗ[R]
    LinearMap.ker r.dualCochain.γ :=
  r.pullbackCoordinates.codRestrict _ r.pullbackCoordinates_mem_ker

theorem homToCycles_injective : Function.Injective r.homToCycles := by
  intro f g h
  have hcoords : dualCoordinates (Fin n₁) (f.hom.comp r.qK) =
      dualCoordinates (Fin n₁) (g.hom.comp r.qK) := congrArg Subtype.val h
  have hfg := (dualCoordinates (Fin n₁)).injective hcoords
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  obtain ⟨v, rfl⟩ := (LinearMap.range r.d₂.mulVecLin).mkQ_surjective a
  exact DFunLike.congr_fun hfg v

theorem homToCycles_surjective : Function.Surjective r.homToCycles := by
  intro a
  let f : (Fin n₁ → R) →ₗ[R] R := (dualCoordinates (Fin n₁)).symm a.val
  have hf : f.comp r.d₂.mulVecLin = 0 := by
    apply (dualCoordinates (Fin n₂)).injective
    rw [dualCoordinates_precomp, map_zero]
    simpa only [f, LinearEquiv.apply_symm_apply] using
      (show r.d₂.transpose *ᵥ a.val = 0 from a.property)
  let f' : r.K →ₗ[R] R := (LinearMap.range r.d₂.mulVecLin).liftQ f
    (by rintro _ ⟨b, rfl⟩; exact DFunLike.congr_fun hf b)
  refine ⟨ModuleCat.ofHom f', Subtype.ext ?_⟩
  change dualCoordinates (Fin n₁) f = a.val
  exact LinearEquiv.apply_symm_apply _ _

/-- Hom of the actual syzygy quotient is linearly equivalent to the dual
cycle module, by descent of functionals. -/
def homCyclesEquiv : (ModuleCat.of R r.K ⟶ ModuleCat.of R R) ≃ₗ[R]
    LinearMap.ker r.dualCochain.γ :=
  LinearEquiv.ofBijective r.homToCycles ⟨r.homToCycles_injective, r.homToCycles_surjective⟩

/-- Under the proved Hom-to-cycles identification, restrictions of functionals
from `P₀` are exactly dual boundaries. -/
theorem homRestriction_range_cycles :
    (LinearMap.range (ExtCokernel.homRestriction R r.syzygySequence (ModuleCat.of R R))).map
      r.homCyclesEquiv.toLinearMap = LinearMap.range r.dualCochain.toCycles := by
  apply Submodule.ext
  intro a
  constructor
  · rintro ⟨f, ⟨g, rfl⟩, hga⟩
    refine ⟨dualCoordinates (Fin n₀) g.hom, ?_⟩
    apply Subtype.ext
    have hga' := congrArg Subtype.val hga
    change dualCoordinates (Fin n₁) (g.hom.comp r.d₁.mulVecLin) = a.val at hga'
    exact (dualCoordinates_precomp r.d₁ g.hom).symm.trans hga'
  · rintro ⟨b, rfl⟩
    let g : ModuleCat.of R (Fin n₀ → R) ⟶ ModuleCat.of R R :=
      ModuleCat.ofHom ((dualCoordinates (Fin n₀)).symm b)
    refine ⟨ExtCokernel.homRestriction R r.syzygySequence (ModuleCat.of R R) g,
      ⟨g, rfl⟩, ?_⟩
    apply Subtype.ext
    change dualCoordinates (Fin n₁)
      (((dualCoordinates (Fin n₀)).symm b).comp r.d₁.mulVecLin) = r.d₁.transpose *ᵥ b
    rw [dualCoordinates_precomp, LinearEquiv.apply_symm_apply]

/-- The Hom cokernel occurring in the Ext long exact sequence is the actual
first cohomology quotient of the dual cochain. -/
def homCohomologyEquiv :
    ((ModuleCat.of R r.K ⟶ ModuleCat.of R R) ⧸
      LinearMap.range (ExtCokernel.homRestriction R r.syzygySequence (ModuleCat.of R R)))
        ≃ₗ[R] r.dualCochain.C1 :=
  Submodule.Quotient.equiv _ _ r.homCyclesEquiv r.homRestriction_range_cycles

/-- The first cohomology quotient is the genuine derived Ext¹ group. -/
def C1EquivExtOne : r.dualCochain.C1 ≃ₗ[R]
    Ext (ModuleCat.of R r.M) (ModuleCat.of R R) 1 :=
  r.homCohomologyEquiv.symm.trans
    (ExtCokernel.homCokernelEquivExtOne R r.syzygySequence_shortExact (ModuleCat.of R R))

/-- On a cycle representative, the Ext¹ identification is exactly the
connecting homomorphism applied to its descended functional. -/
theorem C1EquivExtOne_mk (a : LinearMap.ker r.dualCochain.γ) :
    r.C1EquivExtOne (Submodule.Quotient.mk a) =
      ExtCokernel.connectingHom R r.syzygySequence_shortExact (ModuleCat.of R R)
        (r.homCyclesEquiv.symm a) := rfl

/-- The second cohomology quotient is the genuine derived Ext² group. -/
def C2EquivExtTwo : r.dualCochain.C2 ≃ₗ[R]
    Ext (ModuleCat.of R r.M) (ModuleCat.of R R) 2 :=
  (ToricExt.extOneCokerTransposeEquiv r.d₂ r.injective₂).symm.trans
    (ExtCokernel.dimensionShiftEquiv R r.syzygySequence_shortExact (ModuleCat.of R R))

/-- A supplied length-two free resolution has no genuine Ext above degree two. -/
theorem higherExt_eq_zero (k : ℕ)
    (e : Ext (ModuleCat.of R r.M) (ModuleCat.of R R) (k + 3)) : e = 0 := by
  obtain ⟨f, hf⟩ := Ext.contravariant_sequence_exact₃ r.syzygySequence_shortExact
    (ModuleCat.of R R) e (Ext.eq_zero_of_projective _) (n₀ := k + 2) (by omega)
  have hfzero : f = 0 := ToricExt.extHigher_eq_zero r.d₂ r.injective₂ k f
  rw [hfzero, Ext.comp_zero] at hf
  exact hf.symm

/-- The inverse Hom coordinate map is the descended functional with the
specified dual coordinates. This formula fixes the concrete representative. -/
theorem homCyclesEquiv_symm_apply (a : LinearMap.ker r.dualCochain.γ) (v : Fin n₁ → R) :
    r.homCyclesEquiv.symm a (r.qK v) = ∑ i, v i * a.val i := by
  have h : dualCoordinates (Fin n₁) ((r.homCyclesEquiv.symm a).hom.comp r.qK) = a.val :=
    congrArg Subtype.val (r.homCyclesEquiv.apply_symm_apply a)
  have hf := functional_eq_sum ((r.homCyclesEquiv.symm a).hom.comp r.qK) v
  rw [h] at hf
  exact hf

end Resolution

/-- The actual free-resolution input in Eq. (5): the map out of `Rˢ` is
`H_X†`, the kernel basis map is `Γ`, and the terminal module is the actual
reduced Pauli cokernel. Existence of this data is the separate upstream
free-resolution theorem. -/
structure CSSResolution {q s t : ℕ} (c : CSS.Checks q s t) (cX : ℕ) where
  Γ : Matrix (Fin s) (Fin cX) R
  zero : dagger c.H_X * Γ = 0
  exact₁ : ∀ a : Fin s → R, dagger c.H_X *ᵥ a = 0 ↔
    ∃ b : Fin cX → R, Γ *ᵥ b = a
  injectiveΓ : Function.Injective (fun b : Fin cX → R => Γ *ᵥ b)

namespace CSSResolution

variable {q s t cX : ℕ} {c : CSS.Checks q s t} (h : CSSResolution c cX)

/-- The supplied resolution after the actual conjugation and its standard
coordinate identification. Its first matrix is `H_Xᵀ`, not `H_X†`. -/
def conjugated : Resolution q s cX where
  d₁ := c.H_X.transpose
  d₂ := h.Γ.map bar
  zero := by
    have hz := congrArg (fun D : Matrix (Fin q) (Fin cX) R => D.map bar) h.zero
    rw [Matrix.map_mul, bar_dagger] at hz
    simpa using hz
  exact₁ a := by
    simpa only [bar_dagger] using
      ToricWindows.conjugate_exactness (dagger c.H_X) h.Γ h.exact₁ a
  injective₂ := by
    intro a b hab
    apply ToricWindows.barVec_injective
    apply h.injectiveΓ
    simpa using congrArg ToricWindows.barVec hab

/-- Exactly the physical dual cochain `(H_X, Γ†)` in Eq. (7), with no
change of the manuscript's coefficient or adjoint convention. -/
def cochain : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin cX → R) where
  d₁ := c.H_X.mulVecLin
  γ := (dagger h.Γ).mulVecLin
  square := by
    have hz : dagger h.Γ * c.H_X = 0 := by
      simpa using congrArg dagger h.zero
    apply LinearMap.ext
    intro a
    change dagger h.Γ *ᵥ (c.H_X *ᵥ a) = 0
    rw [mulVec_mulVec, hz, zero_mulVec]

theorem conjugated_dualCochain : h.conjugated.dualCochain = h.cochain := rfl

/-- Equation (8), first identification: the actual cycle quotient of the
physical dual cochain is the genuine `Ext_R¹(overline M_X,R)`. -/
def C1EquivE_X : h.cochain.C1 ≃ₗ[R] E_X c 1 :=
  h.conjugated.C1EquivExtOne.trans
    (extSourceEquiv (conjugateReducedEquiv c).toModuleIso (ModuleCat.of R R) 1).symm

/-- Equation (8), second identification: the actual cokernel of `Γ†` is
the genuine `Ext_R²(overline M_X,R)`. -/
def C2EquivE_X : h.cochain.C2 ≃ₗ[R] E_X c 2 :=
  h.conjugated.C2EquivExtTwo.trans
    (extSourceEquiv (conjugateReducedEquiv c).toModuleIso (ModuleCat.of R R) 2).symm

include h in
/-- The supplied free resolution gives vanishing of all actual Ext layers
above degree two. -/
theorem higher_E_X_eq_zero (k : ℕ) (e : E_X c (k + 3)) : e = 0 := by
  let e' := extSourceEquiv (conjugateReducedEquiv c).toModuleIso
    (ModuleCat.of R R) (k + 3)
  apply e'.injective
  rw [map_zero]
  exact h.conjugated.higherExt_eq_zero k (e' e)

end CSSResolution

end

end Decoupling.ResolutionExt
