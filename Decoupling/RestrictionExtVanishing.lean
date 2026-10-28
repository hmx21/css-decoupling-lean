import Decoupling.GeneralExtRestriction
import Decoupling.TrivialLayers

/-!
# The entire degree-two Ext restriction map vanishes

This proves the general first assertion of Theorem II.1, not only its physical
syndrome specialization. Restriction is mathlib's actual exact-functor map on
derived Ext. Every degree-two class is represented on the second syzygy of the
R-Koszul prefix; the S-Koszul comparison kills its representative by the explicit
degree-two coefficients `vw,wu,uv` and original R-linearity.
-/

namespace Decoupling.RestrictionExtVanishing

open CategoryTheory CategoryTheory.Abelian Matrix
open RetainedRing EvaluationLinear CoarseVanishing GeneralExtRestriction

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

abbrev restriction : ModuleCat R ⥤ ModuleCat S := ModuleCat.restrictScalars (algebraMap S R)

/-- The genuine restriction map on every derived Ext group. -/
def restrictionMap (B E : ModuleCat R) (i : ℕ) :
    Ext B E i →+ Ext (restriction.obj B) (restriction.obj E) i :=
  restriction.mapExtAddHom B E i

variable {t : ℕ} (B : ModuleCat R) (eB : B ≃ₗ[R] Trivial t)

def εR : K₀ R t →ₗ[R] B := eB.symm.toLinearMap.comp (augmentationR t)

def εS : K₀ S t →ₗ[S] restriction.obj B :=
  (restriction.map (ModuleCat.ofHom (εR B eB))).hom.comp (χ₀ t)

theorem εS_evaluation (a : K₀ S t) (j : Fin t) :
    eB (εS B eB a) j = RetainedKoszul.evaluation (a (0, j)) := by
  change eB (eB.symm (augmentationR t (χ₀ t a))) j = _
  rw [eB.apply_symm_apply]
  change augmentation (1 * algebraMap S R (a (0, j))) = _
  rw [one_mul]
  exact (RetainedKoszul.evaluation_inclusion _).symm

theorem εR_surjective : Function.Surjective (εR B eB) := by
  intro b
  refine ⟨fun p => constant (eB b p.2), ?_⟩
  apply eB.injective
  change eB (eB.symm _) = eB b
  rw [eB.apply_symm_apply]
  funext j
  exact augmentation_constant _

theorem εS_surjective : Function.Surjective (εS B eB) := by
  intro b
  choose a ha using fun j => RetainedKoszul.evaluation_surjective (eB b j)
  refine ⟨fun p => a p.2, ?_⟩
  apply eB.injective
  funext j
  exact (εS_evaluation B eB _ j).trans (ha j)

theorem exactR : LinearMap.range (a₁R t) = LinearMap.ker (εR B eB) := by
  apply Submodule.ext
  intro a
  change (∃ b, a₁R t b = a) ↔ εR B eB a = 0
  constructor
  · rintro ⟨b, rfl⟩
    change eB.symm (augmentationR t (a₁R t b)) = 0
    rw [show augmentationR t (a₁R t b) = 0 from
      DFunLike.congr_fun (augmentationR_comp_a₁R t) b, map_zero]
  · intro ha
    have hz : augmentationR t a = 0 := by
      have hb := congrArg eB ha
      simpa only [εR, LinearMap.comp_apply, LinearEquiv.coe_coe,
        LinearEquiv.apply_symm_apply, map_zero] using hb
    have heach (j : Fin t) : augmentation (a (0, j)) = 0 := congrFun hz j
    choose b hb using fun j => (PhysicalKoszul.exact_augmentation _).mp (heach j)
    refine ⟨fun p => b p.2 p.1, ?_⟩
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i
    exact congrFun (hb j) 0

theorem exactS : LinearMap.range (a₁S t) = LinearMap.ker (εS B eB) := by
  apply Submodule.ext
  intro a
  change (∃ b, a₁S t b = a) ↔ εS B eB a = 0
  constructor
  · rintro ⟨b, rfl⟩
    apply eB.injective
    funext j
    rw [εS_evaluation, map_zero]
    change RetainedKoszul.evaluation
      ((RetainedKoszul.d₁ *ᵥ (fun i => b (i, j))) 0) = 0
    apply (RetainedKoszul.exact_augmentation _).mpr
    refine ⟨fun i => b (i, j), ?_⟩
    funext i
    fin_cases i
    rfl
  · intro ha
    have heach (j : Fin t) : RetainedKoszul.evaluation (a (0, j)) = 0 := by
      rw [← εS_evaluation B eB a j, ha, map_zero]
      rfl
    choose b hb using fun j => (RetainedKoszul.exact_augmentation _).mp (heach j)
    refine ⟨fun p => b p.2 p.1, ?_⟩
    funext p
    rcases p with ⟨i, j⟩
    fin_cases i
    exact congrFun (hb j) 0

def prefixR : Prefix R (K₀ R t) (K₁ R t) B :=
  ⟨εR B eB, a₁R t, exactR B eB, εR_surjective B eB⟩

def prefixS : Prefix S (K₀ S t) (K₁ S t) (restriction.obj B) :=
  ⟨εS B eB, a₁S t, exactS B eB, εS_surjective B eB⟩

/-- The R degree-two boundary, regarded as a map onto actual second syzygies. -/
def boundary₂R : K₁ R t →ₗ[R] (prefixR B eB).K₂ :=
  (a₂R t).codRestrict _ (by
    intro a
    apply Subtype.ext
    exact DFunLike.congr_fun (a₁R_comp_a₂R t) a)

/-- The degree-zero comparison restricts to the first syzygies. -/
def χK₁ : (prefixS B eB).K₁ →ₗ[S]
    restriction.obj (ModuleCat.of R (prefixR B eB).K₁) where
  toFun a := ⟨χ₀ t a, a.property⟩
  map_add' a b := Subtype.ext ((χ₀ t).map_add a b)
  map_smul' s a := Subtype.ext ((χ₀ t).map_smul s a)

/-- The degree-one comparison restricts to the second syzygies. -/
def χK₂ : (prefixS B eB).K₂ →ₗ[S]
    restriction.obj (ModuleCat.of R (prefixR B eB).K₂) where
  toFun a := ⟨χ₁ t a, by
    apply Subtype.ext
    have ha : a₁S t a = 0 := congrArg Subtype.val a.property
    change a₁R t (χ₁ t a) = 0
    rw [show a₁R t (χ₁ t a) = χ₀ t (a₁S t a) from
      DFunLike.congr_fun (CoarseVanishing.comparison₁ t) a.val, ha, map_zero]⟩
  map_add' a b := Subtype.ext ((χ₁ t).map_add a b)
  map_smul' s a := Subtype.ext ((χ₁ t).map_smul s a)

/-- Original R-linearity kills every syzygy representative after the doubled
comparison. Surjectivity of the S degree-two boundary is actual Koszul exactness. -/
theorem χK₂_comp_zero (E : ModuleCat R)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0) (hw : ∀ e : E, w • e = 0)
    (f : ModuleCat.of R (prefixR B eB).K₂ ⟶ E) :
    ModuleCat.ofHom (χK₂ B eB) ≫ restriction.map f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro a
  have ha : (a : K₁ S t) ∈ LinearMap.ker (a₁S t) := congrArg Subtype.val a.property
  rw [← exact_a₂S_a₁S t] at ha
  obtain ⟨b, hb⟩ := ha
  have hχ : χK₂ B eB a = boundary₂R B eB (χ₂ t b) := by
    apply Subtype.ext
    change χ₁ t a.val = a₂R t (χ₂ t b)
    rw [← hb]
    exact (DFunLike.congr_fun (CoarseVanishing.comparison₂ t) b).symm
  change f (χK₂ B eB a) = 0
  rw [hχ]
  exact map_χ₂_eq_zero t (f.hom.comp (boundary₂R B eB)) hu hv hw b

/-- Naturality carries each genuine R-Ext cocycle class to the compared
S-cocycle class, whose component is zero. -/
theorem map_cocycleClass_eq_zero (E : ModuleCat R)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0) (hw : ∀ e : E, w • e = 0)
    (f : ModuleCat.of R (prefixR B eB).K₂ ⟶ E) :
    ((prefixR B eB).cocycleClass E f).mapExactFunctor restriction = 0 := by
  have hc := YonedaCocycle.change_resolution_preserves_class
    ((prefixR B eB).shortExactU.map_of_exact restriction)
    ((prefixR B eB).shortExactV.map_of_exact restriction)
    (prefixS B eB).shortExactU (prefixS B eB).shortExactV
    (ModuleCat.ofHom (χK₂ B eB)) (ModuleCat.ofHom (χ₁ t))
    (ModuleCat.ofHom (χK₁ B eB)) (ModuleCat.ofHom (χ₀ t))
    (by rfl) (by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro a
      apply Subtype.ext
      exact DFunLike.congr_fun (CoarseVanishing.comparison₁ t) a)
    (by rfl) (by rfl) (restriction.map f)
  rw [Prefix.map_cocycleClass, ← hc, χK₂_comp_zero B eB E hu hv hw f]
  simp only [YonedaCocycle.cocycleClass, Ext.mk₀_zero, Ext.comp_zero]

include eB in
/-- Every genuine Ext² element between the stated modules restricts to zero.
Only the source needs finite dimension; annihilation suffices for the target. -/
theorem restrictionMap_two_apply_eq_zero (E : ModuleCat R)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0) (hw : ∀ e : E, w • e = 0)
    (e : Ext B E 2) : restrictionMap B E 2 e = 0 := by
  obtain ⟨f, hf⟩ := (prefixR B eB).exists_representative E e
  rw [← hf]
  exact map_cocycleClass_eq_zero B eB E hu hv hw f

include eB in
/-- Equality of the entire actual derived Ext restriction homomorphism to zero,
rather than vanishing of one distinguished syndrome class. -/
theorem restrictionMap_two_eq_zero (E : ModuleCat R)
    (hu : ∀ e : E, u • e = 0) (hv : ∀ e : E, v • e = 0) (hw : ∀ e : E, w • e = 0) :
    restrictionMap B E 2 = 0 := by
  ext e
  exact restrictionMap_two_apply_eq_zero B eB E hu hv hw e

/-- Annihilation by J gives actual trivial Laurent translations. -/
theorem translationsTrivial_of_J_annihilates (M : ModuleCat R)
    (hM : ∀ a ∈ J, ∀ m : M, a • m = 0) : TrivialLayers.TranslationsTrivial M := by
  intro a m
  have ha : monomial a - 1 ∈ J := by
    rw [← ker_augmentation_eq_J]
    change augmentation (monomial a - 1) = 0
    simp
  have hz := hM (monomial a - 1) ha m
  simpa only [sub_smul, one_smul, sub_eq_zero] using hz

/-- The first assertion of manuscript Theorem II.1 in its stated module
conventions: the entire genuine Ext² restriction map is zero. The target's
finite-dimensionality is unnecessary, so this slightly strengthens the claim.
No target standard-module isomorphism or distinguished extension is assumed. -/
theorem restrictionMap_two_eq_zero_of_J_annihilates (B E : ModuleCat R)
    [FiniteDimensional (ZMod 2) (LayerTranslations.coefficients B)]
    (hB : ∀ a ∈ J, ∀ b : B, a • b = 0)
    (hE : ∀ a ∈ J, ∀ e : E, a • e = 0) : restrictionMap B E 2 = 0 := by
  let eB := TrivialLayers.equivTrivial B (translationsTrivial_of_J_annihilates B hB)
  apply restrictionMap_two_eq_zero B eB E
  · exact hE u (Ideal.subset_span (by simp))
  · exact hE v (Ideal.subset_span (by simp))
  · exact hE w (Ideal.subset_span (by simp))

end
end Decoupling.RestrictionExtVanishing
