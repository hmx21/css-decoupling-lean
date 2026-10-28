import Decoupling.MatrixCopies
import Decoupling.ScalarRestriction
import Decoupling.CoarseBasis
import Decoupling.Comparison
import Decoupling.EvaluationLinear
import Decoupling.ZeroComparison

/-!
# Doubling kills the actual syndrome obstruction

The source of the comparison is the repeated augmented Koszul complex over
the actual doubled subring `S`. The degree-zero and degree-one comparison maps
are constructed from projectivity, while the degree-two component is the
actual class of a cycle representative. Its original `R`-linearity is retained.
The explicit doubled Koszul comparison has degree-two coefficients `vw,wu,uv`,
so annihilation by `u,v,w` makes that component zero.

Consequently the genuine Ext² splice of the restricted syndrome sequences
vanishes. No comparison maps, source exactness, or vanishing Ext class are
assumed. The finite-dimensional/trivial-layer reductions which supply the
second-layer identification and first-layer annihilation are separate inputs.
-/

namespace Decoupling.CoarseVanishing

open Matrix RetainedRing MatrixCopies EvaluationLinear

noncomputable section

abbrev K₀ (A : Type*) (t : ℕ) := (Fin 1 × Fin t) → A
abbrev K₁ (A : Type*) (t : ℕ) := (Fin 3 × Fin t) → A

variable (t : ℕ)

def a₁R : K₁ R t →ₗ[R] K₀ R t := across t PhysicalKoszul.partial₁.mulVecLin
def a₂R : K₁ R t →ₗ[R] K₁ R t := across t PhysicalKoszul.partial₂.mulVecLin
def a₁S : K₁ S t →ₗ[S] K₀ S t := across t RetainedKoszul.d₁.mulVecLin
def a₂S : K₁ S t →ₗ[S] K₁ S t := across t RetainedKoszul.d₂.mulVecLin

def χ₀ : K₀ S t →ₗ[S] K₀ R t := across t (Koszul.χ₀Over S)
def χ₁ : K₁ S t →ₗ[S] K₁ R t := across t (Koszul.χ₁Over S u v w)
def χ₂ : K₁ S t →ₗ[S] K₁ R t := across t (Koszul.χ₂Over S u v w)

def augmentationR : K₀ R t →ₗ[R] Trivial t where
  toFun a j := augmentation (a (0, j))
  map_add' a b := by funext j; exact map_add augmentation _ _
  map_smul' r a := by funext j; exact map_mul augmentation _ _

theorem a₁R_comp_a₂R : (a₁R t).comp (a₂R t) = 0 := by
  apply LinearMap.ext
  intro a
  funext p
  change (PhysicalKoszul.partial₁ *ᵥ
    (PhysicalKoszul.partial₂ *ᵥ (fun i => a (i, p.2)))) p.1 = 0
  rw [mulVec_mulVec, PhysicalKoszul.partial₁_mul_partial₂, zero_mulVec]
  rfl

theorem augmentationR_comp_a₁R : (augmentationR t).comp (a₁R t) = 0 := by
  apply LinearMap.ext
  intro a
  funext j
  change augmentation ((PhysicalKoszul.partial₁ *ᵥ (fun i => a (i, j))) 0) = 0
  apply (PhysicalKoszul.exact_augmentation _).mpr
  refine ⟨fun i => a (i, j), ?_⟩
  funext i
  fin_cases i
  rfl

theorem exact_a₂S_a₁S : LinearMap.range (a₂S t) = LinearMap.ker (a₁S t) := by
  apply exact_across
  apply Submodule.ext
  intro a
  exact (RetainedKoszul.exact_d₁_d₂ a).symm

/-- Degree-one comparison over the literal retained subring. -/
theorem comparison₁ : ((a₁R t).restrictScalars S).comp (χ₁ t) =
    (χ₀ t).comp (a₁S t) := by
  apply LinearMap.ext
  intro a
  funext p
  exact congrFun (RetainedRing.comparison₁ (fun i => a (i, p.2))) p.1

/-- Degree-two comparison over the literal retained subring. -/
theorem comparison₂ : ((a₂R t).restrictScalars S).comp (χ₂ t) =
    (χ₁ t).comp (a₂S t) := by
  apply LinearMap.ext
  intro a
  funext p
  exact congrFun (RetainedRing.comparison₂ (fun i => a (i, p.2))) p.1

def uncurryR : (Fin 3 → Fin t → R) →ₗ[R] K₁ R t where
  toFun a p := a p.1 p.2
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The whole repeated degree-two comparison is killed by any originally
R-linear map into a module annihilated by the three augmentation generators. -/
theorem map_χ₂_eq_zero {E : Type*} [AddCommGroup E] [Module R E]
    (f : K₁ R t →ₗ[R] E)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0)
    (hw : ∀ e : E, w • e = 0) (a : K₁ S t) : f (χ₂ t a) = 0 := by
  have hχ : χ₂ t a = uncurryR t
      (Koszul.χ₂Blocks u v w (fun i j => algebraMap S R (a (i, j)))) := by
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i <;> simp [χ₂, across_apply, Koszul.χ₂Over, Koszul.diagonalOver,
      uncurryR, Koszul.χ₂Blocks]
  rw [hχ]
  exact Koszul.map_χ₂Blocks_eq_zero u v w (f.comp (uncurryR t)) hu hv hw _

section Syndrome

variable {q s k t : ℕ}
variable (c : Syndrome.Cochain R (Fin q → R) (Fin s → R) (Fin k → R))
variable (e₂ : c.C2 ≃ₗ[R] Trivial t)

/-- The repeated R-Koszul augmentation onto the actual second layer. -/
def εR : K₀ R t →ₗ[R] c.C2 := e₂.symm.toLinearMap.comp (augmentationR t)

/-- The repeated S-Koszul augmentation onto the actual restricted second layer. -/
def εS : K₀ S t →ₗ[S] (ScalarRestriction.restricted S c).C2 :=
  (ScalarRestriction.C2Equiv S c).symm.toLinearMap.comp
    (((εR c e₂).restrictScalars S).comp (χ₀ t))

theorem εS_evaluation (a : K₀ S t) (j : Fin t) :
    e₂ (ScalarRestriction.C2Equiv S c (εS c e₂ a)) j =
      RetainedKoszul.evaluation (a (0, j)) := by
  change e₂ (e₂.symm (augmentationR t (χ₀ t a))) j = _
  rw [e₂.apply_symm_apply]
  change augmentation (1 * algebraMap S R (a (0, j))) = _
  rw [one_mul]
  exact (RetainedKoszul.evaluation_inclusion (a (0, j))).symm

theorem εS_surjective : Function.Surjective (εS c e₂) := by
  intro z
  choose a ha using fun j => RetainedKoszul.evaluation_surjective
    (e₂ (ScalarRestriction.C2Equiv S c z) j)
  refine ⟨fun p => a p.2, ?_⟩
  apply (ScalarRestriction.C2Equiv S c).injective
  apply e₂.injective
  funext j
  exact (εS_evaluation c e₂ _ j).trans (ha j)

theorem exact_a₁S_εS : LinearMap.range (a₁S t) = LinearMap.ker (εS c e₂) := by
  apply Submodule.ext
  intro a
  change (∃ b, a₁S t b = a) ↔ εS c e₂ a = 0
  constructor
  · rintro ⟨b, rfl⟩
    apply (ScalarRestriction.C2Equiv S c).injective
    apply e₂.injective
    funext j
    rw [εS_evaluation, map_zero, map_zero]
    change RetainedKoszul.evaluation
      ((RetainedKoszul.d₁ *ᵥ (fun i => b (i, j))) 0) = 0
    apply (RetainedKoszul.exact_augmentation _).mpr
    refine ⟨fun i => b (i, j), ?_⟩
    funext i
    fin_cases i
    rfl
  · intro ha
    have heval (j : Fin t) : RetainedKoszul.evaluation (a (0, j)) = 0 := by
      rw [← εS_evaluation c e₂ a j, ha, map_zero, map_zero]
      rfl
    choose b hb using fun j => (RetainedKoszul.exact_augmentation _).mp (heval j)
    refine ⟨fun p => b p.2 p.1, ?_⟩
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i
    exact congrFun (hb j) 0

theorem εR_comp_a₁R : (εR c e₂).comp (a₁R t) = 0 := by
  rw [εR, LinearMap.comp_assoc, augmentationR_comp_a₁R, LinearMap.comp_zero]

/-- Actual original R-linear comparison representatives; this data is proved
to exist below from the free repeated Koszul source. -/
structure ComparisonLift where
  q₀ : K₀ R t →ₗ[R] (Fin k → R)
  v₁ : K₁ R t →ₗ[R] (Fin s → R)
  square₀ : c.pQ.comp q₀ = εR c e₂
  square₁ : c.γ.comp v₁ = q₀.comp (a₁R t)

theorem comparisonLift_exists : Nonempty (ComparisonLift c e₂) := by
  obtain ⟨q₀, hq₀⟩ := Module.projective_lifting_property c.pQ (εR c e₂)
    (LinearMap.range c.γ).mkQ_surjective
  have hzero : c.pQ.comp (q₀.comp (a₁R t)) = 0 := by
    rw [← LinearMap.comp_assoc, hq₀, εR_comp_a₁R]
  obtain ⟨v₁, hv₁⟩ := Comparison.exists_lift_of_comp_eq_zero
    c.γ c.pQ (q₀.comp (a₁R t)) (LinearMap.range c.γ).ker_mkQ.symm hzero
  exact ⟨⟨q₀, v₁, hq₀, hv₁⟩⟩

namespace ComparisonLift

variable (l : ComparisonLift c e₂)

def q₁ : K₁ R t →ₗ[R] c.N := c.ε.comp l.v₁

theorem cycle₂ (a : K₁ R t) : c.γ (l.v₁ (a₂R t a)) = 0 := by
  have h := DFunLike.congr_fun l.square₁ (a₂R t a)
  change c.γ (l.v₁ (a₂R t a)) = l.q₀ (a₁R t (a₂R t a)) at h
  rw [show a₁R t (a₂R t a) = 0 from DFunLike.congr_fun (a₁R_comp_a₂R t) a,
    map_zero] at h
  exact h

/-- The degree-two component is the literal cycle class of the chosen free
representative. It is R-linear, before any scalar restriction. -/
def f₂ : K₁ R t →ₗ[R] c.C1 :=
  (LinearMap.range c.toCycles).mkQ.comp
    ((l.v₁.comp (a₂R t)).codRestrict (LinearMap.ker c.γ) (l.cycle₂ c e₂))

theorem square₂ : c.ι.comp (l.f₂ c e₂) = (l.q₁ c e₂).comp (a₂R t) := rfl

def q₀S : K₀ S t →ₗ[S] (Fin k → R) := (l.q₀.restrictScalars S).comp (χ₀ t)

def q₁S : K₁ S t →ₗ[S] (ScalarRestriction.restricted S c).N :=
  (ScalarRestriction.NEquiv S c).symm.toLinearMap.comp
    (((l.q₁ c e₂).restrictScalars S).comp (χ₁ t))

theorem square₀S : (ScalarRestriction.restricted S c).pQ.comp (l.q₀S c e₂) =
    εS c e₂ := by
  apply LinearMap.ext
  intro a
  apply (ScalarRestriction.C2Equiv S c).injective
  exact DFunLike.congr_fun l.square₀ (χ₀ t a)

theorem square₁S : (ScalarRestriction.restricted S c).γN.comp (l.q₁S c e₂) =
    (l.q₀S c e₂).comp (a₁S t) := by
  apply LinearMap.ext
  intro a
  change c.γ (l.v₁ (χ₁ t a)) = l.q₀ (χ₀ t (a₁S t a))
  have hs : c.γ (l.v₁ (χ₁ t a)) = l.q₀ (a₁R t (χ₁ t a)) :=
    DFunLike.congr_fun l.square₁ (χ₁ t a)
  rw [hs, show a₁R t (χ₁ t a) = χ₀ t (a₁S t a) from
    DFunLike.congr_fun (comparison₁ t) a]

theorem zero_component (hu : ∀ e : c.C1, u • e = 0)
    (hv : ∀ e : c.C1, v • e = 0) (hw : ∀ e : c.C1, w • e = 0) :
    (l.q₁S c e₂).comp (a₂S t) = 0 := by
  apply LinearMap.ext
  intro a
  apply (ScalarRestriction.NEquiv S c).injective
  change l.q₁ c e₂ (χ₁ t (a₂S t a)) = 0
  rw [← show a₂R t (χ₂ t a) = χ₁ t (a₂S t a) from
    DFunLike.congr_fun (comparison₂ t) a]
  rw [← show c.ι (l.f₂ c e₂ (χ₂ t a)) = l.q₁ c e₂ (a₂R t (χ₂ t a)) from
    DFunLike.congr_fun (l.square₂ c e₂) (χ₂ t a)]
  rw [map_χ₂_eq_zero t (l.f₂ c e₂) hu hv hw, map_zero]

end ComparisonLift

include e₂ in
/-- Theorem II.1 for the genuine two-extension of the actual restricted
syndrome cochain. All comparison maps and exact source sequences are derived. -/
theorem κ_restricted_eq_zero (hu : ∀ e : c.C1, u • e = 0)
    (hv : ∀ e : c.C1, v • e = 0) (hw : ∀ e : c.C1, w • e = 0) :
    (ScalarRestriction.restricted S c).κ = 0 := by
  obtain ⟨l⟩ := comparisonLift_exists c e₂
  exact ZeroComparison.κ_eq_zero_of_zero_component
    (ScalarRestriction.restricted S c) (a₂S t) (a₁S t) (εS c e₂)
    (exact_a₂S_a₁S t) (exact_a₁S_εS c e₂) (εS_surjective c e₂)
    (l.q₀S c e₂) (l.q₁S c e₂) (l.square₀S c e₂) (l.square₁S c e₂)
    (l.zero_component c e₂ hu hv hw)

include e₂ in
/-- Since the cover restricts to a free S-module of rank `8k`, the vanished
obstruction supplies an actual S-linear section of the syndrome extension. -/
theorem exists_restricted_section (hu : ∀ e : c.C1, u • e = 0)
    (hv : ∀ e : c.C1, v • e = 0) (hw : ∀ e : c.C1, w • e = 0) :
    ∃ σ : (ScalarRestriction.restricted S c).L →ₗ[S]
        (ScalarRestriction.restricted S c).N,
      (ScalarRestriction.restricted S c).π.comp σ = LinearMap.id := by
  let : Module.Projective S (Fin k → R) :=
    CoarseBasis.projective_restrict_of_free (Fin k → R)
  exact (ScalarRestriction.restricted S c).κ_zero_iff_section.mp
    (κ_restricted_eq_zero c e₂ hu hv hw)

include e₂ in
/-- An actual retraction on the original quotient sets, now with S-linear
scalar action. Its identity is proved for the original inclusion `ι`. -/
theorem exists_restricted_retraction (hu : ∀ e : c.C1, u • e = 0)
    (hv : ∀ e : c.C1, v • e = 0) (hw : ∀ e : c.C1, w • e = 0) :
    ∃ p : c.N →ₗ[S] c.C1,
      p.comp (c.ι.restrictScalars S) = LinearMap.id := by
  let : Module.Projective S (Fin k → R) :=
    CoarseBasis.projective_restrict_of_free (Fin k → R)
  obtain ⟨σ⟩ := (ScalarRestriction.restricted S c).κ_zero_iff_splitting.mp
    (κ_restricted_eq_zero c e₂ hu hv hw)
  let p : c.N →ₗ[S] c.C1 := (ScalarRestriction.C1Equiv S c).toLinearMap.comp
    (σ.r.hom.comp (ScalarRestriction.NEquiv S c).symm.toLinearMap)
  refine ⟨p, ?_⟩
  have hr : σ.r.hom.comp (ScalarRestriction.restricted S c).ι = LinearMap.id :=
    ModuleCat.hom_ext_iff.mp σ.f_r
  apply LinearMap.ext
  intro a
  change ScalarRestriction.C1Equiv S c
    (σ.r.hom ((ScalarRestriction.restricted S c).ι
      ((ScalarRestriction.C1Equiv S c).symm a))) = a
  rw [show σ.r.hom ((ScalarRestriction.restricted S c).ι
      ((ScalarRestriction.C1Equiv S c).symm a)) =
      (ScalarRestriction.C1Equiv S c).symm a from
    DFunLike.congr_fun hr ((ScalarRestriction.C1Equiv S c).symm a)]
  exact (ScalarRestriction.C1Equiv S c).apply_symm_apply a

/-- The split syndrome product after doubling, on the original quotient
sets and with the actual restricted scalar action. -/
def restrictedEquivProd (hu : ∀ e : c.C1, u • e = 0)
    (hv : ∀ e : c.C1, v • e = 0) (hw : ∀ e : c.C1, w • e = 0) :
    c.N ≃ₗ[S] (c.C1 × c.L) := by
  let : Module.Projective S (Fin k → R) :=
    CoarseBasis.projective_restrict_of_free (Fin k → R)
  exact (ScalarRestriction.NEquiv S c).symm.trans
    (((ScalarRestriction.restricted S c).equivProdOfκZero
      (κ_restricted_eq_zero c e₂ hu hv hw)).trans
        (LinearEquiv.prodCongr (ScalarRestriction.C1Equiv S c)
          (ScalarRestriction.LEquiv S c)))

end Syndrome

end
end Decoupling.CoarseVanishing
