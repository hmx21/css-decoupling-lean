import Decoupling.HighDim.MinimalLatticeYonedaContraction
import Decoupling.HighDim.ExtValuesFinite

/-!
# Actual native Yoneda detection

The native products here use the genuine derived-category composition. The
Koszul contractions are chain maps proved in `MinimalLatticeYonedaContraction`.
-/
namespace Decoupling.HighDim.YonedaDetection
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits CategoryTheory.Preadditive
open Koszul TrivialLayers CochainComplex.HomComplex KoszulExtFunctor ExtValuesFunctor
noncomputable section
attribute [local instance] HasDerivedCategory.standard Classical.propDecidable
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

section Transport
variable {C : Type*} [Category* C] [HasShift C ℤ]
  {X Y Z X' Y' Z' : C}

def shiftedTransport {a : ℤ} (e : X ≅ X') (f : Y ≅ Y')
    (g : ShiftedHom X' Y' a) : ShiftedHom X Y a :=
  e.hom ≫ g ≫ f.inv⟦a⟧'

theorem shiftedTransport_comp {a b c : ℤ} (e : X ≅ X') (f : Y ≅ Y') (h : Z ≅ Z')
    (g : ShiftedHom X' Y' a) (k : ShiftedHom Y' Z' b) (hab : b + a = c) :
    (shiftedTransport e f g).comp (shiftedTransport f h k) hab =
      shiftedTransport e h (g.comp k hab) := by
  simp only [shiftedTransport, ShiftedHom.comp, Functor.map_comp, Category.assoc]
  rw [← Functor.map_comp_assoc, f.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [← NatTrans.naturality]
  rfl
end Transport

variable (K : Type) [Field K] (D : ℕ)

def contractionMap (a : Fin D) : complex K D ⟶ (complex K D)⟦(1 : ℤ)⟧ :=
  Cocycle.equivHomShift.symm (contractionCocycle K D a)

theorem contractionMap_f (a : Fin D) (n : ℕ) :
    (contractionMap K D a).f (-(n + 1 : ℕ)) =
      ((resolution K D).cochainComplexXIso (-(n + 1 : ℕ)) (n + 1) rfl).hom ≫
        coordinateBoundary K D a n ≫
          ((resolution K D).cochainComplexXIso (-(n : ℤ)) n rfl).inv ≫
            ((complex K D).shiftFunctorObjXIso (1 : ℤ) (-(n + 1 : ℕ))
              (-(n : ℤ)) (by omega)).inv := by
  simp only [contractionMap, Cocycle.equivHomShift_symm_apply, Cocycle.homOf,
    Cocycle.rightShift_coe]
  rw [Cochain.rightShift_v _ _ _ _ _ _ _ (-(n : ℤ)) (by omega)]
  simp only [contractionCocycle, Cocycle.mk_coe, contractionCochain_v, Category.assoc]


def shiftedSingleComponentIso (A : ModuleCat (Laurent K D)) (n : ℕ) :
    (((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A)⟦(n : ℤ)⟧).X
      (-(n : ℤ)) ≅ A :=
  ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A).shiftFunctorObjXIso
      (n : ℤ) (-n) 0 (by omega) ≪≫
    HomologicalComplex.singleObjXSelf (.up ℤ) 0 A

theorem representative_from_component (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (g : complex K D ⟶ ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A)⟦(n : ℤ)⟧) :
    representative (resolution K D)
      (((resolution K D).cochainComplexXIso (-n) n rfl).inv ≫ g.f (-n) ≫
        (shiftedSingleComponentIso K D A n).hom)
      (ExtValues.boundary_postcomp_zero A hA n _) = g := by
  apply HomologicalComplex.Hom.ext
  funext i
  by_cases hi : i = -(n : ℤ)
  · subst i
    rw [representative_component]
    simp [shiftedSingleComponentIso, Category.assoc]
  · apply (IsZero.of_iso (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 A
        (i + n) (by omega))
      (((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A).shiftFunctorObjXIso
        (n : ℤ) i (i + n) rfl)).eq_of_tgt

theorem localized_eq_zero_iff_component (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (g : complex K D ⟶ ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A)⟦(n : ℤ)⟧) :
    DerivedCategory.Q.map g = 0 ↔ g.f (-(n : ℤ)) = 0 := by
  let f := ((resolution K D).cochainComplexXIso (-n) n rfl).inv ≫ g.f (-n) ≫
    (shiftedSingleComponentIso K D A n).hom
  have he := representative_from_component K D A hA n g
  change representative (resolution K D) f (ExtValues.boundary_postcomp_zero A hA n f) = g at he
  conv_lhs => rw [← he, ← extMk_eq_zero_iff_representative]
  change ExtValues.coefficientMk A hA n f = 0 ↔ _
  have hf : ExtValues.coefficientMk A hA n f = 0 ↔ f = 0 := by
    constructor
    · intro h
      apply ExtValues.coefficientMk_injective A hA n
      exact h.trans (map_zero (ExtValues.coefficientMk A hA n)).symm
    · intro h
      rw [h, map_zero]
  exact hf.trans (by simp only [f, IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero])


def resolutionDerivedIso :
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj (coefficientModule K D) ≅
      DerivedCategory.Q.obj (complex K D) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat (Laurent K D)) 0).app (coefficientModule K D) ≪≫
    (asIso (DerivedCategory.Q.map (resolution K D).π')).symm

def singleDerivedIso (A : ModuleCat (Laurent K D)) :
    (DerivedCategory.singleFunctor (ModuleCat (Laurent K D)) 0).obj A ≅
      DerivedCategory.Q.obj ((CochainComplex.singleFunctor (ModuleCat (Laurent K D)) 0).obj A) :=
  (DerivedCategory.singleFunctorIsoCompQ (ModuleCat (Laurent K D)) 0).app A

theorem coefficientMk_hom (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    (ExtValues.coefficientMk A hA n f).hom =
      shiftedTransport (resolutionDerivedIso K D) (singleDerivedIso K D A)
        (ShiftedHom.map (representative (resolution K D) f
          (ExtValues.boundary_postcomp_zero A hA n f)) DerivedCategory.Q) := by
  change ((resolution K D).extMk f (n + 1) rfl (ExtValues.boundary_postcomp_zero A hA n f)).hom = _
  rw [(resolution K D).extMk_hom]
  simp only [ShiftedHom.mk₀_comp, ShiftedHom.comp_mk₀, shiftedTransport,
    resolutionDerivedIso, singleDerivedIso, Iso.trans_hom, Iso.symm_hom, asIso_inv,
    Iso.app_hom, Iso.app_inv, Category.assoc]
  rfl

def contractionClass (a : Fin D) : Ext (coefficientModule K D) (coefficientModule K D) 1 :=
  Ext.homEquiv.symm (shiftedTransport (resolutionDerivedIso K D) (resolutionDerivedIso K D)
    (ShiftedHom.map (contractionMap K D a) DerivedCategory.Q))

theorem contractionClass_comp_zero_iff (a : Fin D) (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    (contractionClass K D a).comp (ExtValues.coefficientMk A hA n f) (Nat.add_comm 1 n) = 0 ↔
      DerivedCategory.Q.map (ShiftedHom.comp (contractionMap K D a)
        (representative (resolution K D) f (ExtValues.boundary_postcomp_zero A hA n f))
        (show (n : ℤ) + 1 = (n + 1 : ℕ) by omega)) = 0 := by
  have he (x : Ext (coefficientModule K D) A (n + 1)) : x = 0 ↔ x.hom = 0 := by
    constructor
    · intro h; simp [h]
    · intro h; apply Ext.ext; simpa using h
  rw [he, Ext.comp_hom, coefficientMk_hom]
  simp only [contractionClass, Ext.hom, Equiv.apply_symm_apply]
  change (shiftedTransport (resolutionDerivedIso K D) (resolutionDerivedIso K D)
    (ShiftedHom.map (contractionMap K D a) DerivedCategory.Q)).comp
      (shiftedTransport (resolutionDerivedIso K D) (singleDerivedIso K D A) _) _ = 0 ↔ _
  rw [shiftedTransport_comp, ← ShiftedHom.map_comp]
  simp only [shiftedTransport, ShiftedHom.map, Category.assoc,
    IsIso.comp_left_eq_zero, IsIso.comp_right_eq_zero]


@[reassoc] theorem shift_component_naturality {C : Type*} [Category* C] [Preadditive C]
    {P Q : CochainComplex C ℤ} (g : P ⟶ Q) (a p q : ℤ) (hpq : q = p + a) :
    (P.shiftFunctorObjXIso a p q hpq).inv ≫ ((shiftFunctor _ a).map g).f p =
      g.f q ≫ (Q.shiftFunctorObjXIso a p q hpq).inv := by
  subst q
  simp [CochainComplex.shiftFunctorObjXIso]

theorem contraction_rep_component_zero_iff (a : Fin D) (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    (ShiftedHom.comp (contractionMap K D a)
        (representative (resolution K D) f (ExtValues.boundary_postcomp_zero A hA n f))
        (show (n : ℤ) + 1 = (n + 1 : ℕ) by omega)).f (-(n + 1 : ℕ)) = 0 ↔
      coordinateBoundary K D a n ≫ f = 0 := by
  simp only [ShiftedHom.comp, HomologicalComplex.comp_f,
    CochainComplex.shiftFunctorAdd'_inv_app_f']
  rw [contractionMap_f]
  simp only [Category.assoc]
  rw [shift_component_naturality_assoc _ _ _ _ (by omega), representative_component]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, IsIso.comp_left_eq_zero]
  simp only [← Category.assoc, IsIso.comp_right_eq_zero]


theorem contractionClass_comp_eq_zero_iff (a : Fin D) (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0) (n : ℕ)
    (f : (laurentComplex K D).X n ⟶ A) :
    (contractionClass K D a).comp (ExtValues.coefficientMk A hA n f) (Nat.add_comm 1 n) = 0 ↔
      coordinateBoundary K D a n ≫ f = 0 := by
  rw [contractionClass_comp_zero_iff, localized_eq_zero_iff_component K D A hA,
    contraction_rep_component_zero_iff K D a A hA]

theorem exists_coordinateBoundary_postcomp_ne_zero (A : ModuleCat (Laurent K D))
    {n : ℕ} (hnD : n < D) (f : (laurentComplex K D).X n ⟶ A) (hf : f ≠ 0) :
    ∃ a : Fin D, coordinateBoundary K D a n ≫ f ≠ 0 := by
  have hv : ExtValues.cochainValuesEquiv A n f ≠ 0 := by
    intro h
    apply hf
    apply (ExtValues.cochainValuesEquiv A n).injective
    exact h.trans (map_zero _).symm
  obtain ⟨I, hI⟩ : ∃ I : Cell D n, f (Finsupp.single I 1) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨J, a, hface⟩ := exists_coface I hnD
  refine ⟨J a, ?_⟩
  intro hz
  have hzv := congrArg (fun g : (laurentComplex K D).X (n + 1) ⟶ A =>
    g (Finsupp.single J 1)) hz
  change f (boundary (Laurent K D) (Pi.single (J a) 1) n (Finsupp.single J 1)) = 0 at hzv
  rw [coordinate_contraction_basis, hface] at hzv
  have hs : Finsupp.single I ((-1 : Laurent K D) ^ a.val) =
      ((-1 : Laurent K D) ^ a.val) • Finsupp.single I 1 := by simp
  rw [hs, f.hom.map_smul] at hzv
  have hu : IsUnit ((-1 : Laurent K D) ^ a.val) := (isUnit_neg_one).pow _
  exact hI (hu.smul_eq_zero.mp hzv)

theorem coefficient_one_detects (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0)
    {n : ℕ} (hnD : n < D) (κ : Ext (coefficientModule K D) A n) (hκ : κ ≠ 0) :
    ∃ τ : Ext (coefficientModule K D) (coefficientModule K D) 1,
      τ.comp κ (Nat.add_comm 1 n) ≠ 0 := by
  obtain ⟨f, rfl⟩ := ExtValues.coefficientMk_surjective A hA n κ
  have hf : f ≠ 0 := by intro h; apply hκ; rw [h, map_zero]
  obtain ⟨a, ha⟩ := exists_coordinateBoundary_postcomp_ne_zero K D A hnD f hf
  exact ⟨contractionClass K D a, fun h => ha ((contractionClass_comp_eq_zero_iff K D a A hA n f).mp h)⟩

theorem comp_zero_degree {C : Type*} [Category* C] [Abelian C] [HasExt C]
    {X Y Z : C} {a b c d : ℕ} (α : Ext X Y a) (β : Ext Y Z b)
    (h : a + b = c) (h' : a + b = d) :
    α.comp β h = 0 ↔ α.comp β h' = 0 := by
  have : c = d := h.symm.trans h'
  cases this
  rfl

/-- Every nonzero coefficient-source native class is detected by genuine
Yoneda precomposition in any complementary admissible degree. -/
theorem coefficient_detects (A : ModuleCat (Laurent K D))
    (hA : ∀ i : Fin D, ∀ x : A, difference K i • x = 0)
    (m n : ℕ) (hmn : m + n ≤ D) (κ : Ext (coefficientModule K D) A n) (hκ : κ ≠ 0) :
    ∃ α : Ext (coefficientModule K D) (coefficientModule K D) m,
      α.comp κ rfl ≠ 0 := by
  induction m with
  | zero =>
    refine ⟨Ext.mk₀ (𝟙 _), ?_⟩
    intro hz
    apply hκ
    have hz' := (comp_zero_degree (Ext.mk₀ (𝟙 _)) κ rfl (zero_add n)).mp hz
    rwa [Ext.mk₀_id_comp] at hz' 
  | succ m ih =>
    obtain ⟨α, hα⟩ := ih (by omega)
    obtain ⟨τ, hτ⟩ := coefficient_one_detects K D A hA (by omega) (α.comp κ rfl) hα
    refine ⟨τ.comp α (Nat.add_comm 1 m), ?_⟩
    intro hz
    apply hτ
    apply (comp_zero_degree τ (α.comp κ rfl)
      (show 1 + (m + n) = (m + 1) + n by omega) (Nat.add_comm 1 (m + n))).mp
    exact (Ext.comp_assoc τ α κ (Nat.add_comm 1 m) rfl (by omega)).symm.trans hz



/-- Native Yoneda detection for arbitrary Hom-valued classes. Only the source
needs finite coefficient dimension. The target may have any dimension. The
conclusion is a nonzero actual Ext product, including complementary degree zero. -/
theorem native_detects (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B) (hA : AugmentationAction A)
    (m n : ℕ) (hmn : m + n ≤ D) (κ : Ext B A n) (hκ : κ ≠ 0) :
    ∃ α : Ext (coefficientModule K D) B m, α.comp κ rfl ≠ 0 := by
  have hv : ExtValues.finiteCoordinatesEquiv B A hB n κ ≠ 0 := by
    intro hz
    exact hκ ((ExtValues.finiteCoordinatesEquiv B A hB n).map_eq_zero_iff.mp hz)
  obtain ⟨i, hi⟩ : ∃ i : Fin (Module.finrank K (Layers.coefficients B)),
      (Ext.mk₀ (ExtValues.sourceInclusion B hB i)).comp κ (zero_add n) ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨α, hα⟩ := coefficient_detects K D A
    (ExtRestrictionVanishing.difference_annihilates_of_augmentationAction A hA)
    m n hmn ((Ext.mk₀ (ExtValues.sourceInclusion B hB i)).comp κ (zero_add n)) hi
  refine ⟨α.comp (Ext.mk₀ (ExtValues.sourceInclusion B hB i)) (add_zero m), ?_⟩
  simpa only [Ext.comp_assoc_of_second_deg_zero] using hα

end
end Decoupling.HighDim.YonedaDetection
