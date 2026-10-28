import Decoupling.HighDim.ExtValuesFinite
import Mathlib.LinearAlgebra.TensorProduct.Pi
import Mathlib.LinearAlgebra.TensorProduct.Tower

/-!
# The finite coefficient tensor Koszul resolution

Source: Lemma `lem:values`, Appendix B.2. This file constructs the finite
coordinate direct sum resolution, and identifies its terms with the actual
tensor products `K_n ⊗[K] B`. Exactness and projectivity are proved from the
existing Laurent resolution, rather than supplied as hypotheses.
-/

namespace Decoupling.HighDim.ExtValuesTensor

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Koszul TrivialLayers
open scoped TensorProduct
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable (K : Type) [Field K] (D t : ℕ)

abbrev CoordinateTerm (n : ℕ) := Fin t → Term (Laurent K D) D n

def coordinateBoundary (n : ℕ) :
    ModuleCat.of (Laurent K D) (CoordinateTerm K D t (n + 1)) ⟶
      ModuleCat.of (Laurent K D) (CoordinateTerm K D t n) :=
  ModuleCat.ofHom (LinearMap.pi fun i =>
    (boundary (Laurent K D) (difference K) n).hom.comp (LinearMap.proj i))

@[simp] theorem coordinateBoundary_apply (n : ℕ) (v : CoordinateTerm K D t (n + 1))
    (i : Fin t) : coordinateBoundary K D t n v i = boundary (Laurent K D) (difference K) n (v i) := rfl

theorem coordinateBoundary_squared (n : ℕ) :
    coordinateBoundary K D t (n + 1) ≫ coordinateBoundary K D t n = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f : ModuleCat.of (Laurent K D) (Term (Laurent K D) D (n + 2)) ⟶
    ModuleCat.of (Laurent K D) (Term (Laurent K D) D n) => f (v i))
      (boundary_squared (Laurent K D) (difference K) n)

def coordinateComplex : ChainComplex (ModuleCat (Laurent K D)) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of (Laurent K D) (CoordinateTerm K D t n))
    (coordinateBoundary K D t) (coordinateBoundary_squared K D t)

@[simp] theorem coordinateComplex_d (n : ℕ) :
    (coordinateComplex K D t).d (n + 1) n = coordinateBoundary K D t n := by
  simp [coordinateComplex]

def coordinateAugmentation : (coordinateComplex K D t).X 0 ⟶ coefficientVector K D t :=
  ModuleCat.ofHom (X := (coordinateComplex K D t).X 0) (Y := coefficientVector K D t) {
    toFun v i := augmentationMap K D (v i)
    map_add' v w := by funext i; exact (augmentationMap K D).hom.map_add (v i) (w i)
    map_smul' r v := by funext i; exact (augmentationMap K D).hom.map_smul r (v i) }

@[simp] theorem coordinateAugmentation_apply (v : CoordinateTerm K D t 0) (i : Fin t) :
    coordinateAugmentation K D t v i = augmentationMap K D (v i) := rfl

theorem coordinateBoundary_augmentation :
    (coordinateComplex K D t).d 1 0 ≫ coordinateAugmentation K D t = 0 := by
  rw [coordinateComplex_d]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro v
  funext i
  exact congrArg (fun f : (laurentComplex K D).X 1 ⟶ coefficientModule K D => f (v i))
    (boundary_augmentation K D)

def coordinateResolutionAugmentation : coordinateComplex K D t ⟶
    (ChainComplex.single₀ (ModuleCat (Laurent K D))).obj (coefficientVector K D t) :=
  (ChainComplex.toSingle₀Equiv _ _).symm
    ⟨coordinateAugmentation K D t, coordinateBoundary_augmentation K D t⟩

@[simp] theorem coordinateResolutionAugmentation_zero :
    (coordinateResolutionAugmentation K D t).f 0 = coordinateAugmentation K D t :=
  ChainComplex.toSingle₀Equiv_symm_apply_f_zero _ _

theorem coordinateComplex_exactAt_succ (n : ℕ) :
    (coordinateComplex K D t).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (by simp) (by simp),
    ShortComplex.moduleCat_exact_iff]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', coordinateComplex_d]
  change ∀ v : CoordinateTerm K D t (n + 1),
    coordinateBoundary K D t n v = 0 →
      ∃ z, coordinateBoundary K D t (n + 1) z = v
  intro v hv
  have hi (i : Fin t) : boundary (Laurent K D) (difference K) n (v i) = 0 :=
    congrFun hv i
  choose z hz using fun i => laurent_exact K D n (v i) (hi i)
  exact ⟨z, funext hz⟩

instance coordinateResolutionAugmentation_quasiIso :
    QuasiIso (coordinateResolutionAugmentation K D t) :=
  ⟨fun n => by
    cases n with
    | zero =>
      rw [ChainComplex.quasiIsoAt₀_iff]
      rw [ShortComplex.quasiIso_iff_of_zeros' _ (by rfl)
        (by change ((ChainComplex.single₀ (ModuleCat (Laurent K D))).obj
          (coefficientVector K D t)).d 1 0 = 0; simp) (by rfl)]
      constructor
      · rw [ShortComplex.moduleCat_exact_iff]
        change ∀ v : CoordinateTerm K D t 0, coordinateAugmentation K D t v = 0 →
          ∃ z, coordinateBoundary K D t 0 z = v
        intro v hv
        have hi (i : Fin t) : augmentation (zeroTermEquiv (Laurent K D) (v i)) = 0 :=
          congrFun hv i
        choose z hz using fun i => (laurent_exact_at_zero K D (v i)).mp (hi i)
        exact ⟨z, funext hz⟩
      · apply (ModuleCat.epi_iff_surjective _).mpr
        change Function.Surjective (coordinateAugmentation K D t)
        intro v
        choose z hz using fun i : Fin t => laurent_augmentation_surjective K D (v i)
        exact ⟨z, funext hz⟩
    | succ n =>
      rw [quasiIsoAt_iff_exactAt']
      · exact coordinateComplex_exactAt_succ K D t n
      · exact ChainComplex.exactAt_succ_single_obj _ _⟩

/-- The actual finite direct sum of the Koszul resolution, with no
exactness or freeness certificate as an input. -/
def coordinateResolution : ProjectiveResolution (coefficientVector K D t) where
  complex := coordinateComplex K D t
  projective n := by
    change Projective (ModuleCat.of (Laurent K D) (CoordinateTerm K D t n))
    exact ModuleCat.projective_of_free (Module.Free.chooseBasis (Laurent K D) _)
  π := coordinateResolutionAugmentation K D t

variable {K D}

/-- The coefficient coordinate resolution, augmented to the original
source module through its proved coefficient-coordinate isomorphism. -/
def sourceCoordinateResolution (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B) :
    ProjectiveResolution B where
  complex := coordinateComplex K D (Module.finrank K (Layers.coefficients B))
  projective n := (coordinateResolution K D _).projective n
  π := coordinateResolutionAugmentation K D (Module.finrank K (Layers.coefficients B)) ≫
    (ChainComplex.single₀ (ModuleCat (Laurent K D))).map (coordinateIso B hB).inv

/-- The literal tensor term `K_n ⊗_K B`, with Laurent action on the first
factor. -/
abbrev TensorTerm (B : ModuleCat (Laurent K D)) (n : ℕ) :=
  Term (Laurent K D) D n ⊗[K] Layers.coefficients B

/-- The actual coefficient-basis identification of the literal tensor
product with a finite direct sum of free Koszul terms. -/
def tensorTermEquiv (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ) :
    TensorTerm B n ≃ₗ[Laurent K D]
      CoordinateTerm K D (Module.finrank K (Layers.coefficients B)) n :=
  (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl (Laurent K D) (Term (Laurent K D) D n))
    (Module.finBasis K (Layers.coefficients B)).equivFun).trans
      (TensorProduct.piScalarRight K (Laurent K D) (Term (Laurent K D) D n)
        (Fin (Module.finrank K (Layers.coefficients B))))

@[simp] theorem tensorTermEquiv_tmul (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (v : Term (Laurent K D) D n) (b : Layers.coefficients B)
    (i : Fin (Module.finrank K (Layers.coefficients B))) :
    tensorTermEquiv B n (v ⊗ₜ[K] b) i =
      (Module.finBasis K (Layers.coefficients B)).repr b i • v := by
  simp [tensorTermEquiv, TensorProduct.piScalarRight_apply,
    Module.Basis.equivFun_apply]

/-- The tensor complex, transported along the proved termwise tensor
identifications. Its differential is verified on pure tensors below. -/
def tensorComplex (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] : ChainComplex (ModuleCat (Laurent K D)) ℕ where
  X n := ModuleCat.of (Laurent K D) (TensorTerm B n)
  d i j := (tensorTermEquiv B i).toModuleIso.hom ≫
    (coordinateComplex K D (Module.finrank K (Layers.coefficients B))).d i j ≫
      (tensorTermEquiv B j).toModuleIso.inv
  shape i j h := by
    rw [(coordinateComplex K D (Module.finrank K (Layers.coefficients B))).shape i j h]
    simp
  d_comp_d' i j k _ _ := by
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [← Category.assoc ((coordinateComplex K D
      (Module.finrank K (Layers.coefficients B))).d i j), HomologicalComplex.d_comp_d]
    simp

/-- The native chain isomorphism from the literal tensor resolution to its
finite coordinate realization. -/
def tensorComplexIso (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] :
    tensorComplex B ≅ coordinateComplex K D (Module.finrank K (Layers.coefficients B)) :=
  HomologicalComplex.Hom.isoOfComponents (fun n => (tensorTermEquiv B n).toModuleIso) (by
    intro i j _
    simp only [tensorComplex, Category.assoc, Iso.inv_hom_id, Category.comp_id])

/-- The actual tensor Koszul projective resolution of the original finite
augmentation-trivial module. -/
def tensorResolution (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B) :
    ProjectiveResolution B where
  complex := tensorComplex B
  projective n := by
    change Projective (ModuleCat.of (Laurent K D) (TensorTerm B n))
    exact ModuleCat.projective_of_free
      ((Module.Free.chooseBasis (Laurent K D)
        (CoordinateTerm K D (Module.finrank K (Layers.coefficients B)) n)).map
          (tensorTermEquiv B n).symm)
  π := (tensorComplexIso B).hom ≫ (sourceCoordinateResolution B hB).π

/-- The transported differential is literally ∂ ⊗ id on pure tensors. -/
theorem tensorComplex_d_tmul (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (v : Term (Laurent K D) D (n + 1)) (b : Layers.coefficients B) :
    (tensorComplex B).d (n + 1) n (v ⊗ₜ[K] b) =
      (show TensorTerm B n from (boundary (Laurent K D) (difference K) n v) ⊗ₜ[K] b) := by
  apply (tensorTermEquiv B n).injective
  change (tensorTermEquiv B n) ((tensorTermEquiv B n).symm
    ((coordinateComplex K D (Module.finrank K (Layers.coefficients B))).d (n + 1) n
      (tensorTermEquiv B (n + 1) (v ⊗ₜ[K] b)))) = _
  rw [LinearEquiv.apply_symm_apply, coordinateComplex_d]
  funext i
  change (boundary (Laurent K D) (difference K) n).hom
    (tensorTermEquiv B (n + 1) (v ⊗ₜ[K] b) i) =
    tensorTermEquiv B n ((boundary (Laurent K D) (difference K) n).hom v ⊗ₜ[K] b) i
  rw [tensorTermEquiv_tmul, tensorTermEquiv_tmul]
  exact ((boundary (Laurent K D) (difference K) n).hom.restrictScalars K).map_smul _ _

@[simp] theorem coordinateIso_hom_apply (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (b : Layers.coefficients B) (i : Fin (Module.finrank K (Layers.coefficients B))) :
    (coordinateIso B hB).hom (show B from b) i =
      (Module.finBasis K (Layers.coefficients B)).repr b i := rfl

/-- The augmentation of the tensor resolution is literally ε ⊗ id,
followed by the original source's scalar action. -/
theorem tensorResolution_augmentation_tmul (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (hB : AugmentationAction B)
    (v : Term (Laurent K D) D 0) (b : Layers.coefficients B) :
    (tensorResolution B hB).π.f 0 (v ⊗ₜ[K] b) =
      (show B from augmentation (zeroTermEquiv (Laurent K D) v) • b) := by
  apply (coordinateIso B hB).toLinearEquiv.injective
  change (coordinateIso B hB).hom ((coordinateIso B hB).inv
    (coordinateAugmentation K D (Module.finrank K (Layers.coefficients B))
      (tensorTermEquiv B 0 (v ⊗ₜ[K] b)))) = _
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id]
  funext i
  change (augmentationMap K D).hom (tensorTermEquiv B 0 (v ⊗ₜ[K] b) i) =
    ((Module.finBasis K (Layers.coefficients B)).repr
      (augmentation (zeroTermEquiv (Laurent K D) v) • b)) i
  rw [tensorTermEquiv_tmul]
  change augmentation (zeroTermEquiv (Laurent K D)
    ((Module.finBasis K (Layers.coefficients B)).repr b i • v)) = _
  have hz := ((zeroTermEquiv (Laurent K D)).restrictScalars K).map_smul
    ((Module.finBasis K (Layers.coefficients B)).repr b i) v
  change zeroTermEquiv (Laurent K D) (_ • v) =
    _ • zeroTermEquiv (Laurent K D) v at hz
  rw [hz]
  rw [Algebra.smul_def, map_mul]
  change augmentation (constant ((Module.finBasis K (Layers.coefficients B)).repr b i)) *
    augmentation (zeroTermEquiv (Laurent K D) v) = _
  rw [augmentation_constant, map_smul, Finsupp.smul_apply, smul_eq_mul]
  exact mul_comm _ _

/-- Tensor insertion in one coefficient, as an actual Laurent-linear map. -/
def tensorInsertion (B : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)] (n : ℕ)
    (b : Layers.coefficients B) :
    (laurentComplex K D).X n ⟶ (tensorComplex B).X n :=
  ModuleCat.ofHom ({
    toFun v := v ⊗ₜ[K] b
    map_add' v w := TensorProduct.add_tmul v w b
    map_smul' r v := TensorProduct.smul_tmul' r v b } :
      Term (Laurent K D) D n →ₗ[Laurent K D] TensorTerm B n)


/-- The Hom differential of the actual tensor resolution is zero. -/
theorem tensor_boundary_postcomp_zero (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0)
    (n : ℕ) (f : (tensorComplex B).X n ⟶ A) :
    (tensorComplex B).d (n + 1) n ≫ f = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add x y hx hy => simp_all only [map_add]
  | tmul v b =>
    change f ((tensorComplex B).d (n + 1) n (v ⊗ₜ[K] b)) = 0
    rw [tensorComplex_d_tmul]
    have he := congrArg (fun g : (laurentComplex K D).X (n + 1) ⟶ A => g v)
      (ExtValues.boundary_postcomp_zero A hA n (tensorInsertion B n b ≫ f))
    change f (((laurentComplex K D).d (n + 1) n v) ⊗ₜ[K] b) = 0 at he
    have hd : (laurentComplex K D).d (n + 1) n =
        boundary (Laurent K D) (difference K) n := complex_d _ _ _
    rw [hd] at he
    exact he

/-- The manuscript's native tensor-cochain representative map. -/
def tensorMk (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    ((tensorComplex B).X n ⟶ A) →+ Ext B A n where
  toFun f := (tensorResolution B hB).extMk f (n + 1) rfl
    (tensor_boundary_postcomp_zero B A hA n f)
  map_zero' := (tensorResolution B hB).extMk_zero (n + 1) rfl
  map_add' f g := ((tensorResolution B hB).add_extMk f g (n + 1) rfl _ _).symm

theorem tensorMk_surjective (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Function.Surjective (tensorMk B A hB hA n) := by
  intro e
  obtain ⟨f, hf, he⟩ := (tensorResolution B hB).extMk_surjective e (n + 1) rfl
  exact ⟨f, he⟩

theorem tensorMk_injective (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Function.Injective (tensorMk B A hB hA n) := by
  open CategoryTheory.Preadditive CochainComplex.HomComplex in
  apply (injective_iff_map_eq_zero _).mpr
  intro f hf
  cases n with
  | succ n =>
    obtain ⟨g, hg⟩ := ((tensorResolution B hB).extMk_eq_zero_iff f (n + 2) rfl
      (tensor_boundary_postcomp_zero B A hA (n + 1) f) n rfl).mp hf
    exact hg.symm.trans (tensor_boundary_postcomp_zero B A hA n g)
  | zero =>
    change (tensorResolution B hB).extMk f 1 rfl
      (tensor_boundary_postcomp_zero B A hA 0 f) = 0 at hf
    rw [← (tensorResolution B hB).extEquivCohomologyClass.apply_eq_iff_eq,
      ProjectiveResolution.extEquivCohomologyClass_extMk,
      ProjectiveResolution.extEquivCohomologyClass_zero,
      CochainComplex.HomComplex.CohomologyClass.mk_eq_zero_iff] at hf
    obtain ⟨g, hg⟩ :=
      (CochainComplex.HomComplex.Cocycle.toSingleMk_mem_coboundaries_iff _ _ _ _ _ 1
        (by simp)).mp hf
    have hg0 : g = 0 :=
      ((tensorResolution B hB).cochainComplex.isZero_of_isStrictlyLE 0 1).eq_of_src _ _
    rw [hg0, comp_zero] at hg
    exact (cancel_epi ((tensorResolution B hB).cochainComplexXIso 0 0 rfl).hom).mp
      (show ((tensorResolution B hB).cochainComplexXIso 0 0 rfl).hom ≫ f =
        ((tensorResolution B hB).cochainComplexXIso 0 0 rfl).hom ≫ 0 by
          simpa using hg.symm)

/-- Lemma 3: every native Ext class has one and only one actual tensor
Koszul cochain representative. The source resolution is proved exact and
projective above, and no representative existence is assumed. -/
theorem existsUnique_tensorRepresentative (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ)
    (e : Ext B A n) :
    ∃! f : (tensorComplex B).X n ⟶ A, tensorMk B A hB hA n f = e := by
  obtain ⟨f, hf⟩ := tensorMk_surjective B A hB hA n e
  exact ⟨f, hf, fun g hg => tensorMk_injective B A hB hA n (hg.trans hf.symm)⟩

/-- Native Ext identified with the actual tensor cochains, including
zero-degree cochains. -/
def tensorExtEquiv (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ) :
    Ext B A n ≃+ ((tensorComplex B).X n ⟶ A) :=
  (AddEquiv.ofBijective (tensorMk B A hB hA n)
    ⟨tensorMk_injective B A hB hA n, tensorMk_surjective B A hB hA n⟩).symm

@[simp] theorem tensorExtEquiv_mk (B A : ModuleCat (Laurent K D))
    [FiniteDimensional K (Layers.coefficients B)]
    (hB : AugmentationAction B)
    (hA : ∀ i : Fin D, ∀ a : A, difference K i • a = 0) (n : ℕ)
    (f : (tensorComplex B).X n ⟶ A) :
    tensorExtEquiv B A hB hA n (tensorMk B A hB hA n f) = f :=
  (tensorExtEquiv B A hB hA n).apply_symm_apply f

end
end Decoupling.HighDim.ExtValuesTensor
